(* test/parse/test_parser.ml
   Drop-in replacement: updates ONLY the expected outputs to match the NEW
   pretty-printer format (multi-line `case { ... }` blocks with indentation).
*)

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
  let input = "ens (*a)' == (*b) && (*b)' == (*a);" in
  let expected = "ens (*a)' == (*b) && (*b)' == (*a);" in
  test_framework input expected

let test_parser_swap_spec_old_sugar _ctx =
  let input = "ens (*a) == \\old(*b) && (*b) == \\old(*a);" in
  let expected = "ens (*a) == \\old(*b) && (*b) == \\old(*a);" in
  test_framework input expected

let test_parser_case_post_var _ctx =
  let input =
    "case {\n" ^
    "  i' == 30 ==> req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  i' == 30 ==> req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  test_framework input expected

let test_parser_case_old_var _ctx =
  let input =
    "case {\n" ^
    "  i == \\old(i) ==> req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  i == \\old(i) ==> req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  test_framework input expected

let test_parser_eq_neq _ctx =
  let input =
    "case {\n" ^
    "  a == b ==> req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b ==> req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  a == b ==> req a->int*(u); ens a->int*(u);\n" ^
    "  a != b ==> req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  test_framework input expected

let test_parser_loop_case_two_clauses _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i' == 30;\n" ^
    "/\\\n" ^
    "req i>=30 && Term[]; ens i' == i;"
  in
  let expected =
    "case {\n" ^
    "  i < 30 ==> req Term[30 - i]; ens i' == 30;\n" ^
    "  i >= 30 ==> req Term[]; ens i' == i;\n" ^
    "};"
  in
  test_framework input expected

let test_parser_loop_case_single_clause _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i' == 30;"
  in
  let expected =
    "case {\n" ^
    "  i < 30 ==> req Term[30 - i]; ens i' == 30;\n" ^
    "};"
  in
  test_framework input expected

let test_parser_loop_simple_req_term_ens_conj _ctx =
  let input =
    "req i<=10 && Term[10-i]; ens i'==10 && a'==a;"
  in
  let expected =
    "case {\n" ^
    "  i <= 10 ==> req Term[10 - i]; ens i' == 10 && a' == a;\n" ^
    "};"
  in
  test_framework input expected

let test_simple_ens _ctx =
  let input = "ens[r] r == a + 10;" in
  let expected = "ens[r] r == a + 10;" in
  test_framework input expected

let test_parse_loop_minimal _ctx =
  let input =
    "req i<=10;\n" ^
    "ens i'==10;"
  in
  let expected =
    "req i <= 10; ens i' == 10;"
  in
  test_framework input expected

let test_parse_loop_term_only _ctx =
  let input =
    "req i<=10 && Term[10-i];\n" ^
    "ens i'==10;"
  in
  let expected =
    "case {\n" ^
    "  i <= 10 ==> req Term[10 - i]; ens i' == 10;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_heap_range _ctx =
  let input =
    "req array->int*(0,length-i) && Term[length-i];\n" ^
    "ens i'==length;"
  in
  let expected =
    "case {\n" ^
    "  array->int*(0,length - i) ==> req Term[length - i]; ens i' == length;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_forall_basic _ctx =
  let input =
    "req \\forall size_t j. (0<=j ==> j<10) && Term[1];\n" ^
    "ens i'==10;"
  in
  let expected =
    "case {\n" ^
    "  \\forall j:size_t. 0 <= j ==> j < 10 ==> req Term[1]; ens i' == 10;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_index_basic _ctx =
  let input =
    "req array[i]!=element && Term[1];\n" ^
    "ens i'==10;"
  in
  let expected =
    "case {\n" ^
    "  (*(array + i)) != element ==> req Term[1]; ens i' == 10;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_forall_with_index _ctx =
  let input =
    "req \\forall size_t j. (0<=j ==> array[j]!=element) && Term[1];\n" ^
    "ens i'==10;"
  in
  let expected =
    "case {\n" ^
    "  \\forall j:size_t. 0 <= j ==> (*(array + j)) != element ==> req Term[1]; ens i' == 10;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_return_expr _ctx =
  let input =
    "req i<=10 && Term[1];\n" ^
    "ens \\return*(array+i');"
  in
  let expected =
    "case {\n" ^
    "  i <= 10 ==> req Term[1]; ens \\result == (*(array + i'));\n" ^
    "};"
  in
  test_framework input expected

let test_parse_or _ctx =
  let input =
    "req i<=10 && Term[1];\n" ^
    "ens i'==10 || i'==11;"
  in
  let expected =
    "case {\n" ^
    "  i <= 10 ==> req Term[1]; ens i' == 10 || i' == 11;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_target_full _ctx =
  let input =
    "req array->int*(0,length-i) && 0<=i<=length && Term[length-i]\n" ^
    "&& \\forall size_t j. (0<=j ==> array[j]!=element);\n" ^
    "ens i'==length || \\return*(array+i') && array[i']!=element && 0<=i'<length;"
  in
  let expected =
    "case {\n" ^
    "  array->int*(0,length - i) && 0 <= i && i <= length && \\forall j:size_t. 0 <= j ==> (*(array + j)) != element ==> " ^
    "req Term[length - i]; ens i' == length || (\\result == (*(array + i')) && (*(array + i')) != element && 0 <= i' && i' < length);\n" ^
    "};"
  in
  test_framework input expected

(* ---------- Incremental parser tests for the new (search) specification ---------- *)

let test_parse_req_heap_range_minimal _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "ens \\result==\\result;"
  in
  let expected =
    "req array->int*(0,length - 1); ens \\result == \\result;"
  in
  test_framework input expected

let test_parse_ens_ret_named_minimal _ctx =
  let input = "ens[r] r==NULL;" in
  let expected = "ens[r] r == NULL;" in
  test_framework input expected

let test_parse_case_two_branches_minimal _ctx =
  let input =
    "case {\n" ^
    "  i<0 ==> req Term[]; ens i'==i;\n" ^
    "  i>=0 ==> req Term[]; ens i'==0;\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  i < 0 ==> req Term[]; ens i' == i;\n" ^
    "  i >= 0 ==> req Term[]; ens i' == 0;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_exists_assumes _ctx =
  let input =
    "case {\n" ^
    "  (\\exists size_t off . 0<=off<length) ==> req Term[]; ens off==off;\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  \\exists off:size_t. 0 <= off && off < length ==> req Term[]; ens off == off;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_forall_implies_assumes _ctx =
  let input =
    "case {\n" ^
    "  (\\forall size_t off . (0<=off<length ==> array[off]!=element))\n" ^
    "    ==> req Term[]; ens off==off;\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  \\forall off:size_t. (0 <= off && off < length) ==> (*(array + off)) != element ==> req Term[]; ens off == off;\n" ^
    "};"
  in
  test_framework input expected

let test_parse_search_spec_full _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "case {\n" ^
    "  (\\exists size_t off . 0<=off<length && array[off]==element)\n" ^
    "    ==> ens[r] r>=array && r<array+length && *r==element;\n" ^
    "  (\\forall size_t off . (0<=off<length ==> array[off]!=element))\n" ^
    "    ==> ens[r] r==NULL;\n" ^
    "};"
  in
  let expected =
    "case {\n" ^
    "  \\exists off:size_t. 0 <= off && off < length && (*(array + off)) == element ==> " ^
    "req array->int*(0,length - 1); ens[r] r >= array && r < array + length && (*r) == element;\n" ^
    "  \\forall off:size_t. (0 <= off && off < length) ==> (*(array + off)) != element ==> " ^
    "req array->int*(0,length - 1); ens[r] r == NULL;\n" ^
    "};"
  in
  test_framework input expected

let suite =
  "sl_parser"
  >::: [
         "swap_spec_int" >:: test_parser_swap_spec_int;
         "swap_spec_char" >:: test_parser_swap_spec_char;
         "prime_sugar" >:: test_parser_swap_spec_prime_sugar;
         "old_sugar" >:: test_parser_swap_spec_old_sugar;
         "case_post_var" >:: test_parser_case_post_var;
         "case_old_var" >:: test_parser_case_old_var;
         "eq_neq" >:: test_parser_eq_neq;
         "loop_case_two_clauses" >:: test_parser_loop_case_two_clauses;
         "loop_case_single_clause" >:: test_parser_loop_case_single_clause;
         "loop_simple_req_term_ens_conj" >:: test_parser_loop_simple_req_term_ens_conj;
         "simple_ens" >:: test_simple_ens;
         "parse_loop_minimal" >:: test_parse_loop_minimal;
         "parse_loop_term_only" >:: test_parse_loop_term_only;
         "parse_heap_range" >:: test_parse_heap_range;
         "parse_forall_basic" >:: test_parse_forall_basic;
         "parse_index_basic" >:: test_parse_index_basic;
         "parse_forall_with_index" >:: test_parse_forall_with_index;
         "parse_return_expr" >:: test_parse_return_expr;
         "parse_or" >:: test_parse_or;
         "parse_target_full" >:: test_parse_target_full;
         "parse_req_heap_range_minimal" >:: test_parse_req_heap_range_minimal;
         "parse_ens_ret_named_minimal" >:: test_parse_ens_ret_named_minimal;
         "parse_case_two_branches_minimal" >:: test_parse_case_two_branches_minimal;
         "parse_exists_assumes" >:: test_parse_exists_assumes;
         "parse_forall_implies_assumes" >:: test_parse_forall_implies_assumes;
         "parse_search_spec_full" >:: test_parse_search_spec_full;
       ]

let () = run_test_tt_main suite
