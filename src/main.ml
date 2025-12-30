let user_input_handler () : string =
  if Array.length Sys.argv <> 2 then (
    Printf.eprintf "Usage: main <file.c>\n";
    exit 2
  );
  let filename = Sys.argv.(1) in
  if not (Filename.check_suffix filename ".c") then (
    Printf.eprintf "Error: input file must have .c extension\n";
    exit 2
  );
  filename

let read_all_from_file (filename : string) : string =
  let ic = open_in filename in
  let buf = Buffer.create 256 in
  (try
     while true do
       let line = input_line ic in
       Buffer.add_string buf line;
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  close_in ic;
  Buffer.contents buf

let split_once_on_sl (text : string) : string array =
  let start_marker = "/*@[SL]" in
  let end_marker = "*/" in
  let start_len = String.length start_marker in
  let end_len = String.length end_marker in

  (* Must start with the SL marker *)
  if String.length text < start_len || String.sub text 0 start_len <> start_marker then (
    Printf.eprintf "Error: file must begin with SL marker \"%s\".\n" start_marker;
    exit 1
  );

  (* Find the first end marker after the start marker *)
  let rec find_end i =
    if i + end_len > String.length text then (
      Printf.eprintf "Error: SL block end marker not found (expected \"%s\").\n" end_marker;
      exit 1
    ) else if String.sub text i end_len = end_marker then
      i
    else
      find_end (i + 1)
  in

  let sl_content_start = start_len in
  let end_pos = find_end sl_content_start in

  let sl_inside = String.sub text sl_content_start (end_pos - sl_content_start) in
  let code_after =
    let after_start = end_pos + end_len in
    String.sub text after_start (String.length text - after_start)
  in

  (* For now: exactly one SL block, file begins with SL then code *)
  [| sl_inside; code_after |]

let make_output_filename (filename : string) : string =
  if not (Filename.check_suffix filename ".c") then
    filename ^ "_acsl"
  else
    let base =
      String.sub filename 0 (String.length filename - 2)
    in
    base ^ "_acsl.c"

let write_to_file (filename : string) (content : string) : unit =
  let oc = open_out filename in
  output_string oc content;
  close_out oc

let () =
  let filename = user_input_handler () in
  let file_text = read_all_from_file filename in
  let segments = split_once_on_sl file_text in

  let sl_text = segments.(0) in
  let lexbuf = Lexing.from_string sl_text in
  try
    let spec = Sl_parser.main Sl_lexer.token lexbuf in
    let acsl = Translate.sl_to_acsl spec in
    segments.(0) <- acsl;
    let output_text = String.concat "" (Array.to_list segments) in
    let output_filename = make_output_filename filename in
    write_to_file output_filename output_text;
    Printf.printf "%s\n" output_text
  with
  | Sl_parser.Error ->
      Printf.eprintf "Parse error.\n";
      exit 1
  | Sys_error msg ->
      Printf.eprintf "File error: %s\n" msg;
      exit 1
  | Failure msg ->
      Printf.eprintf "Failure: %s\n" msg;
      exit 1



