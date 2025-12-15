open OUnit2
open Sl_ast_printer

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let test_framework (input : string) (expected : string) : unit =
  let spec = parse_spec input in
  let actual = string_of_spec spec in
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let test_parser_swap_spec_int _ctx =
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let expected =
    "req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);"
  in
  test_framework input expected

let test_parser_swap_spec_char _ctx =
  let input =
    "req a->char*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->char*(u);"
  in
  let expected =
    "req a->char*(u) && b->char*(v); ens a->char*(v) && b->char*(u);"
  in
  test_framework input expected

let test_parser_swap_spec_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected = "ens (*a)'==(*b) && (*b)'==(*a);" in
  test_framework input expected

let test_parser_swap_spec_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  test_framework input expected

let test_parser_case_post_var _ctx =
  let input =
    "case {\n" ^
    "  i'==30 => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {i'==30 => req a->int*(u); ens a->int*(u);};"
  in
  test_framework input expected

let test_parser_case_old_var _ctx =
  let input =
    "case {\n" ^
    "  i==\\old(i) => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {i==\\old(i) => req a->int*(u); ens a->int*(u);};"
  in
  test_framework input expected

let test_parser_eq_neq _ctx =
  let input =
    "case {\n" ^
    "  a==b => req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); " ^
    "a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  test_framework input expected

let test_parser_loop_case_two_clauses _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\\n" ^
    "req i>=30 && Term[]; ens i'==i;"
  in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30; " ^
    "i>=30 => req Term[]; ens i'==i;};"
  in
  test_framework input expected

let test_parser_loop_case_single_clause _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;"
  in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30;};"
  in
  test_framework input expected

let test_parser_loop_simple_req_term_ens_conj _ctx =
  let input =
    "req i<=10 && Term[10-i]; ens i'==10 && a'==a;"
  in
  let expected =
    "case {i<=10 => req Term[10-i]; ens i'==10 && a'==a;};"
  in
  test_framework input expected

let suite =
  "sl_parser" >::: [
    "swap_spec_int"                 >:: test_parser_swap_spec_int;
    "swap_spec_char"                >:: test_parser_swap_spec_char;
    "prime_sugar"                   >:: test_parser_swap_spec_prime_sugar;
    "old_sugar"                     >:: test_parser_swap_spec_old_sugar;
    "case_post_var"                 >:: test_parser_case_post_var;
    "case_old_var"                  >:: test_parser_case_old_var;
    "eq_neq"                        >:: test_parser_eq_neq;
    "loop_case_two_clauses"         >:: test_parser_loop_case_two_clauses;
    "loop_case_single_clause"       >:: test_parser_loop_case_single_clause;
    "loop_simple_req_term_ens_conj" >:: test_parser_loop_simple_req_term_ens_conj;
  ]

let () = run_test_tt_main suite
