
let parse_spec (input : string) : Ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let test_framework test_name input expected =
  let spec = parse_spec input in
  let actual = Ast.string_of_spec spec in
  assert_string_equality test_name expected actual



(*Unit Tests*)
let test_parser_swap_spec_int () =
  let test_name = "parser_swap_spec" in
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let expected =
    "req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);"
  in
  test_framework test_name input expected

let test_parser_swap_spec_char () =
  let test_name = "parser_swap_spec" in
  let input =
    "req a->char*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->char*(u);"
  in
  let expected =
    "req a->char*(u) && b->char*(v); ens a->char*(v) && b->char*(u);"
  in
  test_framework test_name input expected

let () =
  test_parser_swap_spec_int ();
  test_parser_swap_spec_char ();
