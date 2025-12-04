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
  let actual = Translate.sl_spec_to_acsl spec in
  assert_string_equality test_name expected actual


let test_translate_swap () =
  let test_name = "translate_swap" in
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework test_name input expected

let test_translate_no_swap () =
  let test_name = "translate_swap" in
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let expected =
"/*@
  requires \\valid(a);
  assigns  *a;
  ensures  *a == \\old(*a);
*/"
  in
  test_framework test_name input expected

let () =
  test_translate_swap ();
  test_translate_no_swap ()
