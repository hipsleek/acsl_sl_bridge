
let read_all () : string =
  let buf = Buffer.create 256 in
  (try
     while true do
       let line = input_line stdin in
       Buffer.add_string buf line;
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  Buffer.contents buf

let () =
  let text = read_all () in
  let lexbuf = Lexing.from_string text in
  try
    let spec = Sl_parser.main Sl_lexer.token lexbuf in
    let acsl = Translate.sl_to_acsl spec in
    Printf.printf "%s\n" acsl
  with
  | Sl_parser.Error ->
      Printf.eprintf "Parse error.\n";
      exit 1
  | Failure msg ->
      Printf.eprintf "Failure: %s\n" msg;
      exit 1
