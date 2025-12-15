(* test_translate_ounit.ml *)

open OUnit2

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let test_framework (input : string) (expected : string) : unit =
  let spec = parse_spec input in
  let actual = Translate.sl_to_acsl spec in
  assert_equal
    ~printer:(fun s -> "\n" ^ s ^ "\n")
    expected
    actual

let test_translate_swap _ctx =
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
  test_framework input expected

let test_translate_no_swap _ctx =
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
  test_framework input expected

let test_translate_triple_swap _ctx =
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
  test_framework input expected

let test_translate_swap_type_mismatch _ctx =
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
  test_framework input expected

let test_translate_swap_prime_notation_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework input expected

let test_translate_swap_old_notation_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework input expected

let test_translate_case_single _ctx =
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
  test_framework input expected

let test_translate_case_two _ctx =
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
  test_framework input expected

let test_translate_case_operators _ctx =
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
  test_framework input expected

let test_translate_loop_terminating_case_expr _ctx =
  let input =
    "case {\n" ^
    "  i<30 => req Term[30-i]; ens i'==30;\n" ^
    "  i>=30  => req Term[]; ens  i'==i;\n" ^
    "};"
  in
  let expected =
"/*@
  loop invariant i < 30;
  loop assigns i;
  loop variant 30-i;
*/"
  in
  test_framework input expected

let test_translate_loop_terminating_case_expr_change_var _ctx =
  let input =
    "case {\n" ^
    "  j<40 => req Term[40-j];ens j'==40;\n" ^
    "  j>=40  => req Term[];ens     j'==j;\n" ^
    "};"
  in
  let expected =
"/*@
  loop invariant j < 40;
  loop assigns j;
  loop variant 40-j;
*/"
  in
  test_framework input expected

let test_translate_loop_terminating_conj_expr _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let expected =
"/*@
  loop invariant i < 30;
  loop assigns i;
  loop variant 30-i;
*/"
  in
  test_framework input expected

let test_translate_for_loop _ctx =
  let input =
    "req i<=10 && Term[10-i]; ens i'==10 && a'==a+(i'-i);"
  in
  let expected =
"/*@
  loop invariant 0 <= i <= 10;
  loop assigns i, a;
  loop variant 10-i;
*/"
  in
  test_framework input expected

let suite =
  "translate" >::: [
    "swap"                               >:: test_translate_swap;
    "no_swap"                            >:: test_translate_no_swap;
    "triple_swap"                        >:: test_translate_triple_swap;
    "swap_type_mismatch"                 >:: test_translate_swap_type_mismatch;
    "swap_prime_notation_sugar"          >:: test_translate_swap_prime_notation_sugar;
    "swap_old_notation_sugar"            >:: test_translate_swap_old_notation_sugar;
    "case_single"                        >:: test_translate_case_single;
    "case_two"                           >:: test_translate_case_two;
    "case_operators"                     >:: test_translate_case_operators;
    "loop_terminating_case_expr"          >:: test_translate_loop_terminating_case_expr;
    "loop_case_expr_change_var"          >:: test_translate_loop_terminating_case_expr_change_var;
    "loop_terminating_conj_expr"         >:: test_translate_loop_terminating_conj_expr;
    "translate_for_loop" >:: test_translate_for_loop;
  ]

let () = run_test_tt_main suite
