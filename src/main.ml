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

let write_to_file (filename : string) (content : string) : unit =
  let oc = open_out filename in
  output_string oc content;
  close_out oc

let () =
  let filename = user_input_handler () in
  let file_text = read_all_from_file filename in

  let blocks = Sl_extract.extract file_text in

  try
    let output_text =
      blocks
      |> List.map (fun (b : Sl_extract.block) ->
             if b.is_sl then
               let lexbuf = Lexing.from_string b.text in
               let spec = Sl_parser.main Sl_lexer.token lexbuf in
               Translate.sl_to_acsl spec
             else b.text)
      |> String.concat ""
    in
    let output_filename = Sl_extract.make_output_filename filename in
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
