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

let split_all_on_sl (text : string) : string array =
  let start_marker = "/*@[SL]" in
  let end_marker = "*/" in
  let start_len = String.length start_marker in
  let end_len = String.length end_marker in
  let n = String.length text in

  let starts_with_marker i =
    i + start_len <= n && String.sub text i start_len = start_marker
  in

  let ends_with_marker i =
    i + end_len <= n && String.sub text i end_len = end_marker
  in

  (* Must start with SL marker *)
  if not (starts_with_marker 0) then (
    Printf.eprintf "Error: file must begin with SL marker \"%s\".\n" start_marker;
    exit 1
  );

  let segments = ref [] in
  let i = ref 0 in

  while !i < n do
    (* Expect an SL marker at the current position *)
    if not (starts_with_marker !i) then (
      Printf.eprintf
        "Error: expected SL marker \"%s\" at position %d.\n"
        start_marker !i;
      exit 1
    );

    (* Scan to find the end marker "*/" *)
    let sl_content_start = !i + start_len in
    let j = ref sl_content_start in
    while !j < n && not (ends_with_marker !j) do
      incr j
    done;

    if !j + end_len > n then (
      Printf.eprintf "Error: SL block end marker not found (expected \"%s\").\n" end_marker;
      exit 1
    );

    let sl_inside = String.sub text sl_content_start (!j - sl_content_start) in
    segments := sl_inside :: !segments;

    (* Move i past the end marker *)
    let after_end = !j + end_len in
    i := after_end;

    (* Collect code until next SL marker or EOF *)
    let code_start = !i in
    while !i < n && not (starts_with_marker !i) do
      incr i
    done;

    let code_chunk = String.sub text code_start (!i - code_start) in
    segments := code_chunk :: !segments
  done;

  Array.of_list (List.rev !segments)

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
  let segments = split_all_on_sl file_text in

  try
    let segments =
        Array.mapi
            (fun idx segment ->
            if idx mod 2 = 0 then
                let lexbuf = Lexing.from_string segment in
                let spec = Sl_parser.main Sl_lexer.token lexbuf in
                Translate.sl_to_acsl spec
            else
                segment)
            segments
    in
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



