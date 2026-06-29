(* GUI side of the SL plugin: an "SL <-> ACSL" tab in the lower notebook
   showing, per function, the original separation-logic block next to the
   ACSL contract generated for it.

   Features:
   - 50/50 side-by-side columns (draggable), word-wrapped, with a Copy button;
   - a proof-status badge (green/red/orange/grey bullet) per function header;
   - click a function's block to jump to it in the source view;
   - a "Refresh status" button (re-query after WP runs).

   Data comes from Frama_sl.Sl_attach.get_comparisons (recorded during -sl
   processing); this module is pure presentation. *)

let sl_keywords = [ "req"; "ens"; "case"; "Term"; "emp" ]

let acsl_keywords =
  [ "requires"; "ensures"; "assigns"; "behavior"; "assumes";
    "complete"; "disjoint"; "behaviors"; "loop"; "invariant"; "variant";
    "\\valid"; "\\old"; "\\result"; "\\forall"; "\\exists"; "\\nothing";
    "\\true"; "\\false"; "\\at"; "\\separated" ]

let is_word_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9') || c = '_'

(* GText buffer offsets count *characters*, but Str.search_forward returns *byte*
   offsets. The status bullet ("●", 3 bytes / 1 char) makes the two diverge, so
   we convert byte -> char offset before building iters. *)
let char_offset_of_byte (text : string) (b : int) : int =
  let n = ref 0 in
  for j = 0 to b - 1 do
    let c = Char.code (String.unsafe_get text j) in
    if c < 0x80 || c >= 0xC0 then incr n
  done;
  !n

(* Apply [tag] to every word-boundary occurrence of [kw] in [buffer]. *)
let tag_keyword (buffer : GText.buffer) tag kw =
  let text = buffer#get_text () in
  let klen = String.length kw in
  let tlen = String.length text in
  let rec search from =
    if from + klen <= tlen then
      match
        try Some (Str.search_forward (Str.regexp_string kw) text from)
        with Not_found -> None
      with
      | None -> ()
      | Some i ->
        let ok_before =
          i = 0 || not (is_word_char text.[i - 1] && is_word_char kw.[0])
        in
        let ok_after =
          i + klen >= tlen
          || not (is_word_char text.[i + klen] && is_word_char kw.[klen - 1])
        in
        if ok_before && ok_after then
          buffer#apply_tag tag
            ~start:(buffer#get_iter (`OFFSET (char_offset_of_byte text i)))
            ~stop:(buffer#get_iter (`OFFSET (char_offset_of_byte text (i + klen))));
        search (i + klen)
  in
  search 0

let clipboard = lazy (GData.clipboard Gdk.Atom.clipboard)

(* The GUI top-level, captured so the click handler can navigate the source. *)
let main_ui_ref : Design.main_window_extension_points option ref = ref None

(* Consolidated proof status of a function -> (bullet glyph, color key). *)
let bullet_full = "\xe2\x97\x8f" (* ● *)
let bullet_empty = "\xe2\x97\x8b" (* ○ *)

let feedback_style (st : Property_status.Feedback.t) : string * string =
  match st with
  | Property_status.Feedback.Valid
  | Property_status.Feedback.Considered_valid -> (bullet_full, "green")
  | Property_status.Feedback.Invalid
  | Property_status.Feedback.Invalid_under_hyp
  | Property_status.Feedback.Invalid_but_dead
  | Property_status.Feedback.Inconsistent -> (bullet_full, "red")
  | Property_status.Feedback.Never_tried -> (bullet_empty, "grey")
  | _ -> (bullet_full, "orange")  (* Unknown, *_under_hyp, *_but_dead *)

(* Preconditions / assumes are caller obligations and hypotheses, not goals WP
   proves for *this* function; for an uncalled function they stay "Unknown" and
   would wrongly drag the badge to orange. Exclude them from the aggregate. *)
let is_hypothesis_ip = function
  | Property.IPPredicate ip ->
    (match ip.Property.ip_kind with
     | Property.PKRequires _ | Property.PKAssumes _ -> true
     | _ -> false)
  | _ -> false

let status_of_kf kf : Property_status.Feedback.t =
  try
    let spec = Annotations.funspec kf in
    let ips =
      Property.ip_of_spec kf Cil_types.Kglobal ~active:[] spec
      |> List.filter (fun ip -> not (is_hypothesis_ip ip))
    in
    match ips with
    | [] -> Property_status.Feedback.Never_tried
    | _ -> Property_status.Feedback.get_conjunction ips
  with Annotations.No_funspec _ -> Property_status.Feedback.Never_tried

type side = {
  view : GText.view;
  buffer : GText.buffer;
  kw_tag : GText.tag;
  header_tag : GText.tag;
  sel_tag : GText.tag; (* background highlight of the selected function's block *)
  status_tags : (string * GText.tag) list;
  keywords : string list;
  (* (buffer offset where a function's block starts, that function), ascending *)
  ranges : (int * Kernel_function.t) list ref;
}

let left_side : side option ref = ref None
let right_side : side option ref = ref None

(* highlight + scroll the block of [kf] in one side *)
let highlight_side (s : side) kf =
  s.buffer#remove_tag s.sel_tag
    ~start:s.buffer#start_iter ~stop:s.buffer#end_iter;
  let rec find = function
    | (st, k) :: rest ->
      if Cil_datatype.Kf.equal k kf then
        let en = match rest with (n, _) :: _ -> n | [] -> s.buffer#end_iter#offset in
        Some (st, en)
      else find rest
    | [] -> None
  in
  match find !(s.ranges) with
  | None -> ()
  | Some (st, en) ->
    let i0 = s.buffer#get_iter (`OFFSET st) in
    s.buffer#apply_tag s.sel_tag ~start:i0
      ~stop:(s.buffer#get_iter (`OFFSET en));
    ignore (s.view#scroll_to_iter ~use_align:true ~yalign:0.1 i0)

(* highlight the function's block in BOTH columns *)
let highlight_all kf =
  Option.iter (fun s -> highlight_side s kf) !left_side;
  Option.iter (fun s -> highlight_side s kf) !right_side

let make_side ~title ~keywords ~color (packing : GObj.widget -> unit) : side =
  let vbox = GPack.vbox ~packing () in
  let header = GPack.hbox ~spacing:4 ~packing:(vbox#pack ~expand:false) () in
  ignore
    (GMisc.label
       ~markup:(Printf.sprintf "<b> %s </b>" title)
       ~xalign:0.0
       ~packing:(header#pack ~expand:true ~fill:true)
       ());
  let copy_btn =
    GButton.button ~label:"Copy" ~packing:(header#pack ~expand:false) ()
  in
  let sw =
    GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
      ~packing:(vbox#pack ~expand:true ~fill:true)
      ()
  in
  let view =
    GText.view ~editable:false ~cursor_visible:false ~wrap_mode:`WORD_CHAR
      ~packing:sw#add ()
  in
  view#misc#modify_font_by_name "Monospace 11";
  view#set_left_margin 6;
  let buffer = view#buffer in
  ignore
    (copy_btn#connect#clicked ~callback:(fun () ->
         (Lazy.force clipboard)#set_text (buffer#get_text ())));
  let kw_tag = buffer#create_tag [ `WEIGHT `BOLD; `FOREGROUND color ] in
  let header_tag =
    buffer#create_tag
      [ `WEIGHT `BOLD; `SCALE `LARGE; `FOREGROUND "#1a5fb4";
        `PARAGRAPH_BACKGROUND "#e8e8e8" ]
  in
  let sel_tag = buffer#create_tag [ `PARAGRAPH_BACKGROUND "#fff2cc" ] in
  let mk c = buffer#create_tag [ `FOREGROUND c; `WEIGHT `BOLD; `SCALE `LARGE ] in
  let status_tags =
    [ ("green", mk "#26a269"); ("red", mk "#c01c28");
      ("orange", mk "#e5a50a"); ("grey", mk "#888888") ]
  in
  let ranges = ref [] in
  (* click a function's block -> jump to it in the source view *)
  ignore
    (view#event#connect#button_press ~callback:(fun ev ->
         (if GdkEvent.Button.button ev = 1 then begin
            let x = int_of_float (GdkEvent.Button.x ev) in
            let y = int_of_float (GdkEvent.Button.y ev) in
            let (bx, by) =
              view#window_to_buffer_coords ~tag:`WIDGET ~x ~y
            in
            let off = (view#get_iter_at_location ~x:bx ~y:by)#offset in
            let target =
              List.fold_left
                (fun acc (s, kf) -> if s <= off then Some kf else acc)
                None !ranges
            in
            match target with
            | Some kf ->
              (* highlight this function in BOTH columns, and jump to source *)
              highlight_all kf;
              (match !main_ui_ref with
               | Some ui ->
                 (try ui#select_or_display_global (Kernel_function.get_global kf)
                  with _ -> ())
               | None -> ())
            | None -> ()
          end);
         false));
  { view; buffer; kw_tag; header_tag; sel_tag; status_tags; keywords; ranges }

(* entries: (function, header label, status bullet, status color, body text) *)
let render_side (s : side)
    (entries : (Kernel_function.t * string * string * string * string) list) =
  s.buffer#set_text "";
  s.ranges := [];
  (match entries with
   | [] ->
     s.buffer#set_text
       "No SL contracts found.\n\nRun frama-c-gui with -sl on a file \
        containing /*@[SL] ... */ annotations."
   | _ ->
     List.iter
       (fun (kf, label, bullet, color, body) ->
          s.ranges := (s.buffer#end_iter#offset, kf) :: !(s.ranges);
          (* colored status bullet *)
          let b0 = s.buffer#end_iter#offset in
          s.buffer#insert ~iter:s.buffer#end_iter (bullet ^ " ");
          (match List.assoc_opt color s.status_tags with
           | Some t ->
             s.buffer#apply_tag t
               ~start:(s.buffer#get_iter (`OFFSET b0))
               ~stop:s.buffer#end_iter
           | None -> ());
          (* function header *)
          let h0 = s.buffer#end_iter#offset in
          s.buffer#insert ~iter:s.buffer#end_iter
            (Printf.sprintf "function %s\n" label);
          s.buffer#apply_tag s.header_tag
            ~start:(s.buffer#get_iter (`OFFSET h0))
            ~stop:s.buffer#end_iter;
          s.buffer#insert ~iter:s.buffer#end_iter (body ^ "\n\n"))
       entries;
     s.ranges := List.rev !(s.ranges);
     List.iter (fun kw -> tag_keyword s.buffer s.kw_tag kw) s.keywords)

let render () =
  let entries = Frama_sl.Sl_attach.get_comparisons () in
  let prep project =
    List.map
      (fun (kf, sl, acsl, attached) ->
         let name = Kernel_function.get_name kf in
         let (bullet, color, label) =
           if attached then
             let (b, c) = feedback_style (status_of_kf kf) in (b, c, name)
           else ("\xe2\x9a\xa0", "red", name ^ "  (not attached)") (* ⚠ *)
         in
         (kf, label, bullet, color, project sl acsl))
      entries
  in
  Option.iter (fun s -> render_side s (prep (fun sl _ -> sl))) !left_side;
  Option.iter (fun s -> render_side s (prep (fun _ acsl -> acsl))) !right_side

(* when a function is selected in the source view, highlight it in the tab *)
let on_select _factory _ui ~button:_ loc =
  match Printer_tag.kf_of_localizable loc with
  | Some kf -> highlight_all kf
  | None -> ()

let main (main_ui : Design.main_window_extension_points) =
  main_ui_ref := Some main_ui;
  let container = GPack.vbox () in
  let toolbar = GPack.hbox ~spacing:6 ~packing:(container#pack ~expand:false) () in
  let refresh_btn =
    GButton.button ~label:"Refresh status"
      ~packing:(toolbar#pack ~expand:false) ()
  in
  ignore
    (GMisc.label
       ~markup:"<i>click a function (here or in the source) to sync</i>"
       ~packing:(toolbar#pack ~expand:false) ());
  let paned =
    GPack.paned `HORIZONTAL ~packing:(container#pack ~expand:true ~fill:true) ()
  in
  left_side :=
    Some
      (make_side ~title:"Separation Logic (SL)" ~keywords:sl_keywords
         ~color:"#a51d2d"
         (fun w -> paned#pack1 ~resize:true ~shrink:true w));
  right_side :=
    Some
      (make_side ~title:"Generated ACSL" ~keywords:acsl_keywords
         ~color:"#26a269"
         (fun w -> paned#pack2 ~resize:true ~shrink:true w));
  (* center the divider once a real width is known; user can drag afterwards *)
  let placed = ref false in
  ignore
    (paned#misc#connect#size_allocate ~callback:(fun (r : Gtk.rectangle) ->
         if (not !placed) && r.Gtk.width > 1 then begin
           placed := true;
           paned#set_position (r.Gtk.width / 2)
         end));
  ignore (refresh_btn#connect#clicked ~callback:render);
  main_ui#register_source_selector on_select;
  let tab_label = (GMisc.label ~markup:"<b>SL \xe2\x86\x92 ACSL</b>" ())#coerce in
  ignore (main_ui#lower_notebook#append_page ~tab_label container#coerce);
  render ()

let () = Design.register_extension main
let () = Design.register_reset_extension (fun _ -> render ())
