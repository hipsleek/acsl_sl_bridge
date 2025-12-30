let has_c_extension (filename : string) : bool =
  Filename.check_suffix filename ".c"

let user_input_handler () : string = 
  if Array.length Sys.argv <> 2 then (
    Printf.eprintf "Usage: main <file.c>\n";
    exit 2
  );
  let filename = Sys.argv.(1) in
  if not (has_c_extension filename) then (
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

let () =
  let filename = user_input_handler () in
  let text = read_all_from_file filename in
  let lexbuf = Lexing.from_string text in
  try
    let spec = Sl_parser.main Sl_lexer.token lexbuf in
    let acsl = Translate.sl_to_acsl spec in
    Printf.printf "%s\n" acsl
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
