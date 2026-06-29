(* Shared SL-block extraction.

   A source file is a sequence of plain-C chunks interleaved with SL blocks
   delimited by [/*@[SL]] ... [*/]. [extract] splits the text into ordered
   [block]s, flagging which are SL and recording each block's 1-based line span.

   For an SL block, [text] is the *content between the markers* (what the SL
   parser consumes); [start_line]/[end_line] span the whole comment, so a block
   can be mapped to the function that immediately follows it.

   This module is reused by both the CLI ([main.ml]) and the Frama-C plugin. *)

type block = {
  is_sl : bool;
  text : string;
  start_line : int; (* 1-based line of the first character of the block *)
  end_line : int;   (* 1-based line of the last character of the block  *)
}

let start_marker = "/*@[SL]"
let end_marker = "*/"

(* 1-based line number of the character at byte offset [off]. *)
let line_of_offset (text : string) (off : int) : int =
  let n = ref 1 in
  let bound = min off (String.length text) in
  for i = 0 to bound - 1 do
    if text.[i] = '\n' then incr n
  done;
  !n

let extract (text : string) : block list =
  let start_len = String.length start_marker in
  let end_len = String.length end_marker in
  let n = String.length text in
  let starts_with_marker i =
    i + start_len <= n && String.sub text i start_len = start_marker
  in
  let ends_with_marker i =
    i + end_len <= n && String.sub text i end_len = end_marker
  in
  let blocks = ref [] in
  (* [start_off] inclusive, [end_off] exclusive *)
  let push is_sl s start_off end_off =
    if is_sl || s <> "" then begin
      let last = max start_off (end_off - 1) in
      blocks :=
        { is_sl;
          text = s;
          start_line = line_of_offset text start_off;
          end_line = line_of_offset text last }
        :: !blocks
    end
  in
  let i = ref 0 in
  (* leading code chunk, if the file does not open with an SL marker *)
  if not (starts_with_marker 0) then begin
    let code_start = 0 in
    while !i < n && not (starts_with_marker !i) do incr i done;
    push false (String.sub text code_start (!i - code_start)) code_start !i
  end;
  while !i < n do
    let marker_start = !i in
    let sl_content_start = !i + start_len in
    let j = ref sl_content_start in
    while !j < n && not (ends_with_marker !j) do incr j done;
    if !j + end_len > n then
      failwith
        (Printf.sprintf "SL block end marker not found (expected \"%s\")."
           end_marker);
    let sl_inside = String.sub text sl_content_start (!j - sl_content_start) in
    push true sl_inside marker_start (!j + end_len);
    let after_end = !j + end_len in
    i := after_end;
    let code_start = !i in
    while !i < n && not (starts_with_marker !i) do incr i done;
    push false (String.sub text code_start (!i - code_start)) code_start !i
  done;
  List.rev !blocks

(* "foo.c" -> "foo_acsl.c"; anything without a .c suffix gets "_acsl" appended. *)
let make_output_filename (filename : string) : string =
  if not (Filename.check_suffix filename ".c") then filename ^ "_acsl"
  else
    let base = String.sub filename 0 (String.length filename - 2) in
    base ^ "_acsl.c"
