let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let test_framework test_name input expected =
  let spec = parse_spec input in
  let actual = Translate.sl_to_acsl spec in
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
  let test_name = "translate_no_swap" in
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

let test_translate_triple_swap () =
  let test_name = "translate_triple_swap" in
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b) && \\valid(c);
  assigns  *a, *b, *c;
  ensures  *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  test_framework test_name input expected

(*I let this be a postive test case because the translation only does syntatic translation*)
let test_translate_swap_type_mismatch () =
  let test_name = "translate_swap_type_mismatch" in
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework test_name input expected

let test_translate_swap_prime_notation_sugar () =
  let test_name = "translate_swap_prime_notation_sugar" in
  let input = "ens (*a)'==(*b) && (*b)'==(*a);"
  in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework test_name input expected

let test_translate_swap_old_notation_sugar () =
  let test_name = "translate_swap_old_notation_sugar" in
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework test_name input expected

let () =
  test_translate_swap ();
  test_translate_no_swap ();
  test_translate_triple_swap ();
  test_translate_swap_type_mismatch ();
  test_translate_swap_prime_notation_sugar ();
  test_translate_swap_old_notation_sugar ();
