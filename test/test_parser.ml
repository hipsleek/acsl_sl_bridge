
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
  let actual = Sl_ast.string_of_spec spec in
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
  let test_name = "parser_swap_spec_char" in
  let input =
    "req a->char*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->char*(u);"
  in
  let expected =
    "req a->char*(u) && b->char*(v); ens a->char*(v) && b->char*(u);"
  in
  test_framework test_name input expected

let test_parser_swap_spec_prime_sugar () =
  let test_name = "parser_swap_spec_prime_sugar" in
  let input =
    "ens (*a)'==(*b) && (*b)'==(*a);"
  in
  let expected =
    "ens (*a)'==(*b) && (*b)'==(*a);"
  in
  test_framework test_name input expected

let test_parser_swap_spec_prime_old () =
  let test_name = "parser_swap_spec_old_sugar" in
  let input =
    "ens (*a)==\\old(*b) && (*b)==\\old(*a);"
  in
  let expected =
    "ens (*a)==\\old(*b) && (*b)==\\old(*a);"
  in
  test_framework test_name input expected

let test_parser_case_post_var () =
  let test_name = "parser_case_post_var" in
  let input =
    "case {\n" ^
    "  i'==30 => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {i'==30 => req a->int*(u); ens a->int*(u);};"
  in
  test_framework test_name input expected

let test_parser_case_old_var () =
  let test_name = "parser_case_old_var" in
  let input =
    "case {\n" ^
    "  i==\\old(i) => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {i==\\old(i) => req a->int*(u); ens a->int*(u);};"
  in
  test_framework test_name input expected


let test_parser_eq_neq () =
  let test_name = "parser_case_spec" in
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
  test_framework test_name input expected

let test_parser_case_loop_term () =
  let test_name = "parser_case_loop_term" in
  let input =
    "case {\n" ^
    "  i<30 => req Term[30-i]; ens i'==30;\n" ^
    "  i>=30 => req Term[];    ens i'==i;\n" ^
    "};"
  in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30; " ^
    "i>=30 => req Term[]; ens i'==i;};"
  in
  test_framework test_name input expected

let () =
  test_parser_swap_spec_int ();
  test_parser_swap_spec_char ();
  test_parser_swap_spec_prime_sugar ();
  test_parser_swap_spec_prime_old ();
  test_parser_case_post_var ();
  test_parser_case_old_var ();

  test_parser_eq_neq ();

  test_parser_case_loop_term ();
