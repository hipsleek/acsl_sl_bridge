(* Core of the SL plugin: extract SL annotations from the source, translate them
   to ACSL with the bridge, then parse/type/attach the result as a real
   Cil_types.funspec on the corresponding function.

   The translation pipeline (Sl_parser -> Sl_to_core -> Core_to_acsl, wrapped by
   Translate.sl_to_acsl) is reused verbatim from the standalone bridge. Only the
   back end changes: instead of writing a *_acsl.c file, we feed the ACSL text to
   Frama-C's own parser/typer and register it via Annotations. *)

open Cil_types

(* ------------------------------------------------------------------ *)
(* Typing context.  Adapted from Frama-C's own (private)              *)
(* Logic_parse_string.{find_var,default_typer,sync_typedefs}, which   *)
(* the kernel does not export.  Uses only public kernel lookups.      *)
(* ------------------------------------------------------------------ *)

exception Error of Cil_types.location * string
exception Unbound of string

let find_var kf kinstr ?label var =
  let vi =
    try
      let scope =
        match kinstr with
        | Kglobal -> Whole_function kf
        | Kstmt stmt ->
          (match label with
           | None | Some "Here" | Some "Post" | Some "Old" -> Block_scope stmt
           | Some "Pre" -> raise Not_found
           | Some "Init" -> raise Not_found
           | Some "LoopEntry" | Some "LoopCurrent" ->
             if not (Kernel_function.stmt_in_loop kf stmt) then
               Kernel.fatal
                 "Use of LoopEntry or LoopCurrent outside of a loop";
             Block_scope (Kernel_function.find_enclosing_loop kf stmt)
           | Some l ->
             (try let s = Kernel_function.find_label kf l in Block_scope !s
              with Not_found ->
                Kernel.fatal
                  "Use of label %s that does not exist in function %a"
                  l Kernel_function.pretty kf))
      in
      Globals.Vars.find_from_astinfo var scope
    with Not_found ->
    try Globals.Vars.find_from_astinfo var (Formal kf)
    with Not_found -> Globals.Vars.find_from_astinfo var Global
  in
  Cil.cvar_to_lvar vi

let default_typer kf kinstr =
  let module LT = Logic_typing.Make (struct
      let anonCompFieldName = Cabs2cil.anonCompFieldName
      let conditionalConversion = Cabs2cil.logicConditionalConversion

      let is_loop () =
        match kinstr with
        | Kglobal -> false
        | Kstmt s -> Kernel_function.stmt_in_loop kf s

      let find_macro _ = raise Not_found
      let find_var ?label var = find_var kf kinstr ?label var

      let find_enum_tag x =
        try Globals.Types.find_enum_tag x
        with Not_found -> raise (Unbound ("Unbound variable " ^ x))

      let find_comp_field info s =
        let field = Cil.getCompField info s in
        Field (field, NoOffset)

      let find_type = Globals.Types.find_type
      let find_label s = Kernel_function.find_label kf s

      let integral_cast ty t =
        raise
          (Failure
             (Format.asprintf "term %a has type %a, but %a is expected."
                Printer.pp_term t Printer.pp_logic_type Linteger
                Printer.pp_typ ty))

      let error loc msg =
        Pretty_utils.ksfprintf (fun e -> raise (Error (loc, e))) msg

      let on_error f rollback x =
        try f x
        with Error (loc, msg) as exn -> rollback (loc, msg); raise exn
    end)
  in
  (module LT : Logic_typing.S)

let sync_typedefs () =
  Logic_env.reset_typenames ();
  Globals.Types.iter_types (fun name _ ns ->
      if ns = Logic_typing.Typedef then
        try ignore @@ String.index name ':'
        with Not_found -> Logic_env.add_typename name)

(* ------------------------------------------------------------------ *)
(* SL-specific glue                                                    *)
(* ------------------------------------------------------------------ *)

let emitter =
  Emitter.create "SL" [ Emitter.Funspec ] ~correctness:[] ~tuning:[]

(* (function, raw SL text, generated ACSL text or error note, attached?),
   in attachment order. Consumed by the GUI sub-plugin to render the
   side-by-side comparison, query per-function proof status, navigate to the
   source, and flag functions whose contract was not actually attached. *)
let comparisons : (Kernel_function.t * string * string * bool) list ref = ref []
let get_comparisons () = List.rev !comparisons

(* Drop the "/*@" ... "*/" wrapper emitted by Core_to_acsl so we can hand the
   bare spec body to Logic_lexer.spec. *)
let strip_markers (s : string) : string =
  let s = String.trim s in
  let s =
    if String.length s >= 3 && String.sub s 0 3 = "/*@"
    then String.sub s 3 (String.length s - 3)
    else s
  in
  let s = String.trim s in
  let s =
    if String.length s >= 2 && String.sub s (String.length s - 2) 2 = "*/"
    then String.sub s 0 (String.length s - 2)
    else s
  in
  String.trim s

let read_file (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* All defined functions as (basename, start_line, kf). *)
let collect_functions () =
  let acc = ref [] in
  Globals.Functions.iter (fun kf ->
      if Kernel_function.is_definition kf then begin
        let pos = fst (Kernel_function.get_location kf) in
        let file = Filename.basename (Filepath.to_string pos.Filepath.pos_path) in
        acc := (file, pos.Filepath.pos_lnum, kf) :: !acc
      end);
  !acc

(* Recursively collect (location, loop-statement) pairs in a block.  We walk the
   body rather than relying on fundec.sallstmts, which needs the CFG (not
   necessarily computed at this point). *)
let rec loops_in_block acc (b : block) =
  List.fold_left loops_in_stmt acc b.bstmts
and loops_in_stmt acc (s : stmt) =
  match s.skind with
  | Loop (_, body, loc, _, _) -> loops_in_block ((loc, s) :: acc) body
  | Block b -> loops_in_block acc b
  | If (_, b1, b2, _) -> loops_in_block (loops_in_block acc b1) b2
  | Switch (_, b, _, _) -> loops_in_block acc b
  | UnspecifiedSequence seq ->
    List.fold_left (fun a (st, _, _, _, _) -> loops_in_stmt a st) acc seq
  | _ -> acc

(* All loop statements as (basename, line, kf, stmt). *)
let collect_loops () =
  let acc = ref [] in
  Globals.Functions.iter (fun kf ->
      if Kernel_function.is_definition kf then begin
        let fd = Kernel_function.get_definition kf in
        List.iter
          (fun (loc, stmt) ->
             let p = fst loc in
             acc :=
               ( Filename.basename (Filepath.to_string p.Filepath.pos_path),
                 p.Filepath.pos_lnum, kf, stmt )
               :: !acc)
          (loops_in_block [] fd.sbody)
      end);
  !acc

(* Parse an SL block and translate it to ACSL text (shared by both attach
   paths). *)
let translate_sl (b : Sl_extract.block) : (string, string) result =
  try
    let spec = Sl_parser.main Sl_lexer.token (Lexing.from_string b.text) in
    Ok (Core_to_acsl.spec_to_acsl (Sl_to_core.sl_to_core spec))
  with
  | Sl_parser.Error -> Error "(SL parse error)"
  | Failure msg -> Error (Printf.sprintf "(translation error: %s)" msg)

(* -sl-show: print the SL block beside the generated ACSL. *)
let show_block kf sl acsl_full =
  if Sl_options.Show.get () then begin
    let bar = String.make 60 '-' in
    Sl_options.result
      "%a@\n%s@\n[SL]@\n%s@\n%s@\n[ACSL]@\n%s@\n%s"
      Kernel_function.pretty kf bar sl bar (String.trim acsl_full) bar
  end

(* Attach a function-contract block as a typed funspec on [kf]. *)
let attach_one kf (b : Sl_extract.block) =
  let sl = String.trim b.text in
  let push acsl attached = comparisons := (kf, sl, acsl, attached) :: !comparisons in
  match translate_sl b with
  | Error note ->
    push note false;
    Sl_options.warning "SL translation failed near line %d" b.start_line
  | Ok acsl_full ->
    show_block kf sl acsl_full;
    let acsl = String.trim acsl_full in
    (try
       let inner = strip_markers acsl_full in
       let pos = fst (Kernel_function.get_location kf) in
       sync_typedefs ();
       let module LT = (val default_typer kf Kglobal : Logic_typing.S) in
       match Logic_lexer.spec (pos, inner) with
       | None ->
         push acsl false;
         Sl_options.warning "could not parse generated ACSL for %a"
           Kernel_function.pretty kf
       | Some (_, ptree_spec) ->
         let vi = Kernel_function.get_vi kf in
         let formals = Some (Kernel_function.get_formals kf) in
         let typ = Kernel_function.get_type kf in
         let typed = LT.funspec [] vi formals typ ptree_spec in
         Annotations.add_behaviors emitter kf typed.spec_behavior;
         Option.iter (Annotations.add_terminates emitter kf) typed.spec_terminates;
         Option.iter (Annotations.add_decreases emitter kf) typed.spec_variant;
         List.iter (Annotations.add_complete emitter kf) typed.spec_complete_behaviors;
         List.iter (Annotations.add_disjoint emitter kf) typed.spec_disjoint_behaviors;
         push acsl true;
         Sl_options.feedback "attached SL contract to %a" Kernel_function.pretty kf
     with
     | Error (_, msg) ->
       push acsl false;
       Sl_options.warning "ACSL typing error for %a: %s" Kernel_function.pretty kf msg
     | Unbound msg ->
       push acsl false;
       Sl_options.warning "ACSL typing (unbound) for %a: %s"
         Kernel_function.pretty kf msg
     | Failure msg ->
       push acsl false;
       Sl_options.warning "failure for %a: %s" Kernel_function.pretty kf msg)

(* Attach a loop block as code annotations (loop invariant/assigns/variant) on
   the loop statement [stmt] inside [kf].  A loop annotation parses as a single
   [Aloop_annot] holding the whole clause list, which we then type and attach.
   (Note: Logic_parse_string.code_annot keeps only [Acode_annot] and silently
   drops loop annotations, so we drive Logic_lexer.annot ourselves.) *)
let attach_loop kf stmt (b : Sl_extract.block) =
  let sl = String.trim b.text in
  let push acsl attached = comparisons := (kf, sl, acsl, attached) :: !comparisons in
  match translate_sl b with
  | Error note ->
    push note false;
    Sl_options.warning "loop SL translation failed near line %d" b.start_line
  | Ok acsl_full ->
    show_block kf sl acsl_full;
    let acsl = String.trim acsl_full in
    let inner = strip_markers acsl_full in
    (try
       sync_typedefs ();
       let module LT = (val default_typer kf (Kstmt stmt) : Logic_typing.S) in
       let sloc = Cil_datatype.Stmt.loc stmt in
       match Logic_lexer.annot (fst sloc, inner) with
       | Some (_, Logic_ptree.Aloop_annot (_, cas)) ->
         Populate_spec.populate_funspec kf [ `Assigns ];
         let behaviors =
           Logic_utils.get_behavior_names (Annotations.funspec kf)
         in
         let rt = Ctype (Kernel_function.get_return_type kf) in
         List.iter
           (fun pa ->
              let ca = LT.code_annot sloc behaviors rt pa in
              (* keep_empty:false lets the loop `assigns` replace WP's implicit
                 "assigns everything"; otherwise it is silently dropped. *)
              Annotations.add_code_annot ~keep_empty:false emitter ~kf stmt ca)
           cas;
         push acsl true;
         Sl_options.feedback "attached loop annotations to %a"
           Kernel_function.pretty kf
       | _ ->
         push acsl false;
         Sl_options.warning "could not parse generated loop ACSL for %a"
           Kernel_function.pretty kf
     with exn ->
       push acsl false;
       Sl_options.warning "loop annotation failed for %a: %s"
         Kernel_function.pretty kf (Printexc.to_string exn))

let process () =
  comparisons := [];
  let funcs = collect_functions () in
  let loops = collect_loops () in
  let files = Filepath.to_string_list (Kernel.Files.get ()) in
  List.iter
    (fun path ->
       let file = Filename.basename path in
       match read_file path with
       | exception Sys_error msg -> Sl_options.warning "cannot read %s: %s" path msg
       | text ->
         Sl_extract.extract text
         |> List.iter (fun (b : Sl_extract.block) ->
                if b.is_sl then begin
                  let after = b.end_line in
                  let fn_below =
                    funcs
                    |> List.filter (fun (f, l, _) -> f = file && l > after)
                    |> List.sort (fun (_, a, _) (_, c, _) -> compare a c)
                    |> (function [] -> None | (_, l, kf) :: _ -> Some (l, kf))
                  in
                  let loop_below =
                    loops
                    |> List.filter (fun (f, l, _, _) -> f = file && l > after)
                    |> List.sort (fun (_, a, _, _) (_, c, _, _) -> compare a c)
                    |> (function [] -> None | (_, l, kf, st) :: _ -> Some (l, kf, st))
                  in
                  (* nearest entity below the block wins: a loop -> loop annot,
                     a function definition -> funspec. *)
                  match loop_below, fn_below with
                  | Some (ll, lkf, st), Some (fl, _) when ll < fl -> attach_loop lkf st b
                  | Some (_, lkf, st), None -> attach_loop lkf st b
                  | _, Some (_, kf) -> attach_one kf b
                  | None, None ->
                    Sl_options.warning
                      "SL block ending at line %d in %s: no function or loop below it"
                      after file
                end))
    files
