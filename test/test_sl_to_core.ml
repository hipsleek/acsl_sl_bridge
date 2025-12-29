(* test/test_sl_to_core.ml *)

open OUnit2

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let test_framework (expected : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let core_of (input : string) : string =
  let sl_spec = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  Core_printer.string_of_spec core_spec

(*** Existing tests (kept) ***)

let test_sl_to_core_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == load(b) && H'(b) == load(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_no_swap _ctx =
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }"
  in
  test_framework expected actual

let test_sl_to_core_triple_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a) && valid(b) && valid(c)\n" ^
    "  ensures H'(a) == load(c) && H'(b) == load(a) && H'(c) == load(b)\n" ^
    "  assigns { *a, *b, *c }"
  in
  test_framework expected actual

let test_sl_to_core_swap_type_mismatch _ctx =
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == load(b) && H'(b) == load(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_swap_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_swap_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected actual

(*** New tests mirroring test_translate.ml ***)

let test_sl_to_core_case_single _ctx =
  let input =
    "case { a==b => req a->int*(u); ens a->int*(u); };"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes a == b\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }"
  in
  test_framework expected actual

let test_sl_to_core_case_two _ctx =
  let input =
    "case {\n" ^
    "  a==b => req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b => req a->int*(u) && b->int*(v);\n" ^
    "          ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes a == b\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a, *b }\n\n" ^
    "behavior case2:\n" ^
    "  assumes a != b\n" ^
    "  requires valid(a) && valid(b)\n" ^
    "  ensures H'(a) == load(b) && H'(b) == load(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_case_operators _ctx =
  let input =
    "case {\n" ^
    "  a<b  => req a->int*(u); ens a->int*(u);\n" ^
    "  a<=b => req a->int*(u); ens a->int*(u);\n" ^
    "  a>b  => req a->int*(u); ens a->int*(u);\n" ^
    "  a>=b => req a->int*(u); ens a->int*(u);\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes a < b\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }\n\n" ^
    "behavior case2:\n" ^
    "  assumes a <= b\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }\n\n" ^
    "behavior case3:\n" ^
    "  assumes a > b\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }\n\n" ^
    "behavior case4:\n" ^
    "  assumes a >= b\n" ^
    "  requires valid(a)\n" ^
    "  ensures H'(a) == load(a)\n" ^
    "  assigns { *a }"
  in
  test_framework expected actual

let test_sl_to_core_loop_terminating_case_expr _ctx =
  let input =
    "case {\n" ^
    "  i<30 => req Term[30-i]; ens i'==30;\n" ^
    "  i>=30  => req Term[]; ens  i'==i;\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes i < 30\n" ^
    "  requires true\n" ^
    "  ensures i' == 30\n" ^
    "  assigns { i }\n" ^
    "  variant 30 - i\n\n" ^
    "behavior case2:\n" ^
    "  assumes i >= 30\n" ^
    "  requires true\n" ^
    "  ensures i' == i\n" ^
    "  assigns { i }"
  in
  test_framework expected actual

let test_sl_to_core_loop_terminating_case_expr_change_var _ctx =
  let input =
    "case {\n" ^
    "  j<40 => req Term[40-j];ens j'==40;\n" ^
    "  j>=40  => req Term[];ens     j'==j;\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes j < 40\n" ^
    "  requires true\n" ^
    "  ensures j' == 40\n" ^
    "  assigns { j }\n" ^
    "  variant 40 - j\n\n" ^
    "behavior case2:\n" ^
    "  assumes j >= 40\n" ^
    "  requires true\n" ^
    "  ensures j' == j\n" ^
    "  assigns { j }"
  in
  test_framework expected actual

let test_sl_to_core_loop_terminating_triple_case_expr _ctx =
  let input =
    "case {\n" ^
    "  i>=30  => req Term[]; ens  i'==i;\n" ^
    "  20<=i<30 => req Term[30-i]; ens i'==30;\n" ^
    "  i<20 => req Term[20-i]; ens i'==20;\n" ^
    "};"
  in
  let actual = core_of input in
  (* core keeps cases; translate later derives invariants *)
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes i >= 30\n" ^
    "  requires true\n" ^
    "  ensures i' == i\n" ^
    "  assigns { i }\n\n" ^
    "behavior case2:\n" ^
    "  assumes 20 <= i && i < 30\n" ^
    "  requires true\n" ^
    "  ensures i' == 30\n" ^
    "  assigns { i }\n" ^
    "  variant 30 - i\n\n" ^
    "behavior case3:\n" ^
    "  assumes i < 20\n" ^
    "  requires true\n" ^
    "  ensures i' == 20\n" ^
    "  assigns { i }\n" ^
    "  variant 20 - i"
  in
  test_framework expected actual

let test_sl_to_core_loop_terminating_conj_expr _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes i < 30\n" ^
    "  requires true\n" ^
    "  ensures i' == 30\n" ^
    "  assigns { i }\n" ^
    "  variant 30 - i\n\n" ^
    "behavior case2:\n" ^
    "  assumes i >= 30\n" ^
    "  requires true\n" ^
    "  ensures i' == i\n" ^
    "  assigns { i }"
  in
  test_framework expected actual

let test_sl_to_core_for_loop _ctx =
  let input =
    "req i<=10 && Term[10-i];\n" ^
    "ens i'==10 && b'==b+(i'-i);"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes i <= 10\n" ^
    "  requires true\n" ^
    "  ensures i' == 10 && b' == b + i' - i\n" ^
    "  assigns { b, i }\n" ^
    "  variant 10 - i"
  in
  test_framework expected actual

let test_sl_to_core_ens_res _ctx =
  let input = "ens[r] r==a+10;" in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires true\n" ^
    "  ensures \\result == a + 10\n" ^
    "  assigns {}"
  in
  test_framework expected actual

let test_sl_to_core_loop_search_forall_index _ctx =
  let input =
    "req array->int*(0,length-i) && 0<=i<=length && Term[length-i]\n" ^
    "&& \\forall size_t j. (0<=j<i => array[j]!=element);\n" ^
    "ens i'==length || \\return*(array+i') && array[i']!=element && 0<=i'<length;"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes 0 <= i && i <= length && forall size_t j. (0 <= j && j < i) ==> (array[j] != element)\n" ^
    "  requires valid_read_range(array, 0, length - i)\n" ^
    "  ensures i' == length || \\result == array[i'] && array[i'] != element && 0 <= i' && i' < length\n" ^
    "  assigns { i }\n" ^
    "  variant length - i"
  in
  test_framework expected actual

let test_sl_to_core_spec_search _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "case {\n" ^
    "  (\\exists size_t off . 0<=off<length && array[off]==element)\n" ^
    "    => ens[r] r>=array && r<array+length && *r==element;\n" ^
    "  (\\forall size_t off . (0<=off<length ==> array[off]!=element))\n" ^
    "    => ens[r] r==NULL;\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes exists size_t off. 0 <= off && off < length && array[off] == element\n" ^
    "  requires valid_read_range(array, 0, length - 1)\n" ^
    "  ensures \\result >= array && \\result < array + length && load(\\result) == element\n" ^
    "  assigns {}\n\n" ^
    "behavior case2:\n" ^
    "  assumes forall size_t off. (0 <= off && off < length) ==> (array[off] != element)\n" ^
    "  requires valid_read_range(array, 0, length - 1)\n" ^
    "  ensures \\result == NULL\n" ^
    "  assigns {}"
  in
  test_framework expected actual

let test_sl_to_core_mutable_arr _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "ens \\forall size_t j. (0<=j<length => array[j]'==0);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid_read_range(array, 0, length - 1)\n" ^
    "  ensures forall size_t j. (0 <= j && j < length) ==> (array'[j'] == 0)\n" ^
    "  assigns { array+(0..length - 1) }"
  in
  test_framework expected actual

let test_sl_to_core_mutable_arr_loop _ctx =
  let input =
    "req array->int*(i,length-i) && i<=length && Term[length-i]\n" ^
    "&& \\forall size_t j. (i<=j<length => array[j]'==0);\n" ^
    "ens i'==length;"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes i <= length && forall size_t j. (0 <= j && j < i) ==> (array[j] == 0)\n" ^
    "  requires valid_read_range(array, i, length - i)\n" ^
    "  ensures i' == length\n" ^
    "  assigns { i, array+(0..length - 1) }\n" ^
    "  variant length - i"
  in
  test_framework expected actual

let test_sl_to_core_search_replace _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "ens \\forall size_t j. (0<=j<length && arr[j]==old => array[j]'==new)" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]!=old => array[j]'==array[j]);"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes true\n" ^
    "  requires valid_read_range(array, 0, length - 1)\n" ^
    "  ensures forall size_t j. ((0 <= j && j < length && arr[j] == old) ==> (array'[j'] == new)) && forall size_t j. (0 <= j && j < length && arr[j] != old) ==> (array'[j'] == array[j])\n" ^
    "  assigns { array+(0..length - 1) }"
  in
  test_framework expected actual

let test_sl_to_core_search_replace_loop _ctx =
  let input =
    "req array->int*(0,length-1) && Term[length - i]\n" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]==old => array[j]'==new)" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]!=old => array[j]'==array[j]);" ^
    "ens i'==length;"
  in
  let actual = core_of input in
  let expected =
    "kind(loop)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes forall size_t j. ((0 <= j && j < length && arr[j] == old) ==> (array'[j'] == new)) && forall size_t j. (0 <= j && j < length && arr[j] != old) ==> (array'[j'] == array[j])\n" ^
    "  requires valid_read_range(array, 0, length - 1)\n" ^
    "  ensures i' == length\n" ^
    "  assigns { i, array+(0..length - 1) }\n" ^
    "  variant length - i"
  in
  test_framework expected actual

let test_sl_to_core_incr_max _ctx =
  let input =
    "req p!=q && p->int*(a) && q->int*(b);\n" ^
    "case {\n" ^
    "  a>=b => ens p->int*(a+1) && q->int*(b);\n" ^
    "  a<b  => ens p->int*(a) && q->int*(b+1);\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes load(p) >= load(q)\n" ^
    "  requires valid(p) && valid(q) && p != q\n" ^
    "  ensures H'(p) == load(p) + 1 && H'(q) == load(q)\n" ^
    "  assigns { *p, *q }\n\n" ^
    "behavior case2:\n" ^
    "  assumes load(p) < load(q)\n" ^
    "  requires valid(p) && valid(q) && p != q\n" ^
    "  ensures H'(p) == load(p) && H'(q) == load(q) + 1\n" ^
    "  assigns { *p, *q }"
  in
  test_framework expected actual

let test_sl_to_core_incr_max_spatial_notation _ctx =
  let input =
    "req p->int*(a) ** q->int*(b);\n" ^
    "case {\n" ^
    "  a>=b => ens p->int*(a+1) && q->int*(b);\n" ^
    "  a<b  => ens p->int*(a) && q->int*(b+1);\n" ^
    "};"
  in
  let actual = core_of input in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:\n" ^
    "  assumes load(p) >= load(q)\n" ^
    "  requires p != q && valid(p) && valid(q)\n" ^
    "  ensures H'(p) == load(p) + 1 && H'(q) == load(q)\n" ^
    "  assigns { *p, *q }\n\n" ^
    "behavior case2:\n" ^
    "  assumes load(p) < load(q)\n" ^
    "  requires p != q && valid(p) && valid(q)\n" ^
    "  ensures H'(p) == load(p) && H'(q) == load(q) + 1\n" ^
    "  assigns { *p, *q }"
  in
  test_framework expected actual

let suite =
  "sl_to_core" >::: [
    "swap"                          >:: test_sl_to_core_swap;
    "no_swap"                       >:: test_sl_to_core_no_swap;
    "triple_swap"                   >:: test_sl_to_core_triple_swap;
    "swap_type_mismatch"            >:: test_sl_to_core_swap_type_mismatch;
    "swap_prime_sugar"              >:: test_sl_to_core_swap_prime_sugar;
    "swap_old_sugar"                >:: test_sl_to_core_swap_old_sugar;

    "case_single"                   >:: test_sl_to_core_case_single;
    "case_two"                      >:: test_sl_to_core_case_two;
    "case_operators"                >:: test_sl_to_core_case_operators;

    "loop_terminating_case_expr"    >:: test_sl_to_core_loop_terminating_case_expr;
    "loop_case_expr_change_var"     >:: test_sl_to_core_loop_terminating_case_expr_change_var;
    "loop_terminating_triple_case"  >:: test_sl_to_core_loop_terminating_triple_case_expr;
    "loop_terminating_conj_expr"    >:: test_sl_to_core_loop_terminating_conj_expr;

    "for_loop"                      >:: test_sl_to_core_for_loop;
    "ens_res"                       >:: test_sl_to_core_ens_res;

    "loop_search_forall_index"      >:: test_sl_to_core_loop_search_forall_index;
    "spec_search"                   >:: test_sl_to_core_spec_search;

    "mutable_arr"                   >:: test_sl_to_core_mutable_arr;
    "mutable_arr_loop"              >:: test_sl_to_core_mutable_arr_loop;

    "search_replace"                >:: test_sl_to_core_search_replace;
    "search_replace_loop"           >:: test_sl_to_core_search_replace_loop;

    "incr_max"                      >:: test_sl_to_core_incr_max;
    "incr_max_spatial_notation"     >:: test_sl_to_core_incr_max_spatial_notation;
  ]

let () = run_test_tt_main suite
