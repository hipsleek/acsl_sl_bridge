let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let assert_string_equality name expected actual =
  if actual <> expected then
    (* Printf.printf "%s \n%S" name actual  *)
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

let test_translate_case_single () =
  let input =
    "case { a==b => req a->int*(u); ens a->int*(u); };"
  in
  let expected =
"/*@
  assigns  *a;
  behavior case1:
    assumes a == b;
    requires \\valid(a);
    ensures  *a == \\old(*a);
*/"
  in
  test_framework "translate_case_single" input expected

let test_translate_case_two () =
  let input =
    "case {\n" ^
    "  a==b => req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b => req a->int*(u) && b->int*(v);\n" ^
    "          ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in

  let expected =
"/*@
  assigns  *a, *b;
  behavior case1:
    assumes a == b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*a);
  behavior case2:
    assumes a != b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in

  test_framework "translate_case_two" input expected

let test_translate_case_operators () =
  let input =
    "case {\n" ^
    "  a<b  => req a->int*(u); ens a->int*(u);\n" ^
    "  a<=b => req a->int*(u); ens a->int*(u);\n" ^
    "  a>b  => req a->int*(u); ens a->int*(u);\n" ^
    "  a>=b => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in

  let expected =
"/*@
  assigns  *a;
  behavior case1:
    assumes a < b;
    requires \\valid(a);
    ensures  *a == \\old(*a);
  behavior case2:
    assumes a <= b;
    requires \\valid(a);
    ensures  *a == \\old(*a);
  behavior case3:
    assumes a > b;
    requires \\valid(a);
    ensures  *a == \\old(*a);
  behavior case4:
    assumes a >= b;
    requires \\valid(a);
    ensures  *a == \\old(*a);
*/"
  in

  test_framework "translate_case_operators" input expected

let test_translate_loop_terminating_case_expr () =
  let test_name = "translate_loop_terminating" in
  let input =
    "case {\n" ^
    "  i<=30 => req Term[30-i]; ens a->int*(u);\n" ^
    "  i>30  => req Term[];     ens b->int*(v);\n" ^
    "};"
  in
  let expected =
"/*@
  loop invariant i <= 30;
  loop assigns i;
  loop variant 30-i;
*/"
  in
  test_framework test_name input expected

let test_translate_loop_terminating_case_expr_change_var () =
  let test_name = "translate_loop_terminating" in
  let input =
    "case {\n" ^
    "  j<=30 => req Term[30-j]; ens a->int*(u);\n" ^
    "  j>30  => req Term[];     ens b->int*(v);\n" ^
    "};"
  in
  let expected =
"/*@
  loop invariant j <= 30;
  loop assigns j;
  loop variant 30-j;
*/"
  in
  test_framework test_name input expected

let test_translate_loop_terminating_pre_post () =
  let test_name = "translate_loop_terminating_pre_post" in
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "req i>=30 && Term[]; ens i'==i;"
  in
  let expected =
"/*@
  loop invariant j <= 30;
  loop assigns j;
  loop variant 30-j;
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

  test_translate_case_single ();
  test_translate_case_two ();
  test_translate_case_operators ();

  test_translate_loop_terminating_case_expr ();
  test_translate_loop_terminating_case_expr_change_var ();
  test_translate_loop_terminating_pre_post ();
