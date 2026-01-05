(* test/test_translate.ml *)

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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_no_swap _ctx =
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a);\n" ^
    "  assigns *a;\n" ^
    "  ensures *a == \\old(*a);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_triple_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b) && \\valid(c);\n" ^
    "  assigns *a, *b, *c;\n" ^
    "  ensures *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_swap_type_mismatch _ctx =
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_swap_prime_notation_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_swap_old_notation_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_case_single _ctx =
  let input =
    "case { a==b => req a->int*(u); ens a->int*(u); };"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a);\n" ^
    "  assigns *a;\n" ^
    "  ensures *a == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  behavior case1:\n" ^
    "    assumes a == b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case2:\n" ^
    "    assumes a != b;\n" ^
    "    ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\valid(a);\n" ^
    "  assigns *a;\n" ^
    "  behavior case1:\n" ^
    "    assumes a < b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case2:\n" ^
    "    assumes a <= b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case3:\n" ^
    "    assumes a > b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case4:\n" ^
    "    assumes a >= b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
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
    "/*@\n" ^
    "  loop invariant j < 40;\n" ^
    "  loop assigns j;\n" ^
    "  loop variant 40 - j;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_loop_terminating_triple_case_expr _ctx =
  let input =
    "case {\n" ^
    "  i>=30  => req Term[]; ens  i'==i;\n" ^
    "  20<=i<30 => req Term[30-i]; ens i'==30;\n" ^
    "  i<20 => req Term[20-i]; ens i'==20;\n" ^
    "};"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop invariant 20 <= i;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_loop_terminating_conj_expr _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_for_loop _ctx =
  let input =
    "req i<=10 && Term[10-i];\n" ^
    "ens i'==10 && b'==b+(i'-i);"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= 10;\n" ^
    "  loop invariant b == \\at(b, LoopEntry) + (i - \\at(i, LoopEntry));\n" ^
    "  loop assigns b, i;\n" ^
    "  loop variant 10 - i;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_ens_res _ctx =
  let input =
    "ens[r] r==a+10;"
  in
  let expected =
    "/*@\n" ^
    "  requires \\true;\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures \\result == a + 10;\n" ^
    "*/"
  in
  test_framework input expected

(* No observed difference*)
let test_translate_for_loop_search_forall_index _ctx =
  let input =
    "req array->int*(0,length-i) && 0<=i<=length && Term[length-i]\n" ^
    "&& \\forall size_t j. (0<=j<i => array[j]!=element);\n" ^
    "ens i'==length || \\return*(array+i') && array[i']!=element && 0<=i'<length;"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= length;\n" ^
    "  loop invariant 0 <= i;\n" ^
    "  loop invariant \\forall size_t j; (0 <= j && j < i) ==> (array[j] != element);\n" ^
    "  loop assigns i;\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework input expected

(* No observed difference*)
let test_sl_to_acsl_spec_search _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "case {\n" ^
    "  (\\exists size_t off . 0<=off<length && array[off]==element)\n" ^
    "    => ens[r] r>=array && r<array+length && *r==element;\n" ^
    "  (\\forall size_t off . (0<=off<length ==> array[off]!=element))\n" ^
    "    => ens[r] r==NULL;\n" ^
    "};"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid_read(array + (0 .. length - 1));\n" ^
    "  assigns \\nothing;\n" ^
    "  behavior case1:\n" ^
    "    assumes \\exists size_t off; 0 <= off && off < length && array[off] == element;\n" ^
    "    ensures \\result >= array && \\result < array + length && \\old(*\\result) == element;\n" ^
    "  behavior case2:\n" ^
    "    assumes \\forall size_t off; (0 <= off && off < length) ==> (array[off] != element);\n" ^
    "    ensures \\result == NULL;\n" ^
    "*/"
  in
  test_framework input expected

let test_sl_to_acsl_mutable_arr _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "ens \\forall size_t j. (0<=j<length => array[j]'==0);"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid_read(array + (0 .. length - 1));\n" ^
    "  assigns array[(0 .. length - 1)];\n" ^
    "  ensures \\forall size_t j; (0 <= j && j < length) ==> (array[j] == 0);\n" ^
    "*/"
  in
  test_framework input expected

let test_sl_to_acsl_mutable_arr_loop _ctx =
  let input =
    "req array->int*(i,length-i) && i<=length && Term[length-i]\n" ^
    "&& \\forall size_t j. (i<=j<length => array[j]'==0);\n" ^
    "ens i'==length;"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= length;\n" ^
    "  loop invariant \\forall size_t j; (0 <= j && j < i) ==> (array[j] == 0);\n" ^
    "  loop assigns i, array[(0 .. length - 1)];\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework input expected

let test_sl_to_acsl_search_replace _ctx =
  let input =
    "req array->int*(0,length-1);\n" ^
    "ens \\forall size_t j. (0<=j<length && arr[j]==old => array[j]'==new)" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]!=old => array[j]'==array[j]);"
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid_read(array + (0 .. length - 1));\n" ^
    "  assigns array[(0 .. length - 1)];\n" ^
    "  ensures \\forall size_t j; ((0 <= j && j < length && \\old(arr[j]) == old) ==> (array[j] == new))" ^
    " && \\forall size_t j; (0 <= j && j < length && \\old(arr[j]) != old) ==> (array[j] == \\old(array[j]));\n" ^
    "*/"
  in
  test_framework input expected

let test_sl_to_acsl_search_replace_loop _ctx =
  let input =
    "req array->int*(0,length-1) && Term[length - i]\n" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]==old => array[j]'==new)" ^
    "&& \\forall size_t j. (0<=j<length && arr[j]!=old => array[j]'==array[j]);" ^
    "ens i'==length;"
  in
  let expected =
    "/*@\n" ^
    "  loop invariant \\forall size_t j; ((0 <= j && j < length && arr[j] == old) ==> (array[j] == new)) && \\forall size_t j; (0 <= j && j < length && arr[j] != old) ==> (array[j] == array[j]);\n" ^
    "  loop assigns i, array[(0 .. length - 1)];\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_incr_max _ctx =
  let input =
    "req p!=q && p->int*(a) && q->int*(b);\n" ^
    "case {\n" ^
    "  a>=b => ens p->int*(a+1) && q->int*(b);\n" ^
    "  a<b  => ens p->int*(a) && q->int*(b+1);\n" ^
    "};"
  in
  let expected =
    "/*@\n" ^
    "  requires p != q && \\valid(p) && \\valid(q);\n" ^
    "  assigns *p, *q;\n" ^
    "  behavior case1:\n" ^
    "    assumes *p >= *q;\n" ^
    "    ensures *p == \\old(*p) + 1 && *q == \\old(*q);\n" ^
    "  behavior case2:\n" ^
    "    assumes *p < *q;\n" ^
    "    ensures *p == \\old(*p) && *q == \\old(*q) + 1;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_incr_max_spatial_notation _ctx =
  let input =
    "req p->int*(a) ** q->int*(b);\n" ^
    "case {\n" ^
    "  a>=b => ens p->int*(a+1) && q->int*(b);\n" ^
    "  a<b  => ens p->int*(a) && q->int*(b+1);\n" ^
    "};"
  in
  let expected =
    "/*@\n" ^
    "  requires p != q && \\valid(p) && \\valid(q);\n" ^
    "  assigns *p, *q;\n" ^
    "  behavior case1:\n" ^
    "    assumes *p >= *q;\n" ^
    "    ensures *p == \\old(*p) + 1 && *q == \\old(*q);\n" ^
    "  behavior case2:\n" ^
    "    assumes *p < *q;\n" ^
    "    ensures *p == \\old(*p) && *q == \\old(*q) + 1;\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_abs_diff_pure_notation _ctx =
  let input =
    "req (a < b ==> b - a <= INT_MAX) &&\n" ^
    "    (b <= a ==> a - b <= INT_MIN);\n" ^
    "ens[r] (a < b ==> a + r == b) &&\n" ^
    "       (b <= a ==> a - r == b);"
  in
  let expected =
    "/*@\n" ^
    "  requires ((a < b) ==> (b - a <= INT_MAX)) && ((b <= a) ==> (a - b <= INT_MIN));\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures ((a < b) ==> (a + \\result == b)) && ((b <= a) ==> (a - \\result == b));\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_max_abs _ctx =
  let input =
    "req (a > INT_MIN) && (b > INT_MIN);\n" ^
    "ens[r] (r >= 0) &&\n" ^
    "       (r >= a && r >= -a && r >= b && r >= -b) &&\n" ^
    "       (r == a || r == -a || r == b || r == -b);"
  in
  let expected =
    "/*@\n" ^
    "  requires a > INT_MIN && b > INT_MIN;\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures \\result >= 0 && \\result >= a && \\result >= -a && \\result >= b && \\result >= -b && (\\result == a || \\result == -a || \\result == b || \\result == -b);\n" ^
    "*/"
  in
  test_framework input expected

let test_translate_all_zero_array _ctx =
  let input =
    "req (n >= 0) && t->int*(0, n-1);\n" ^
    "ens (\\result != 0) <==>\n" ^
    "    (\\forall integer j. (0 <= j && j < n) ==> t[j] == 0);"
  in
  let expected =
    "/*@\n" ^
    "  requires n >= 0 && \\valid_read(t + (0 .. n - 1));\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures ((\\result != 0) ==> (\\forall integer j; (0 <= j && j < n) ==> (\\old(t[j]) == 0)))" ^
    " && ((\\forall integer j; (0 <= j && j < n) ==> (\\old(t[j]) == 0)) ==> (\\result != 0));\n" ^
    "*/"
  in
  test_framework input expected


let suite =
  "translate" >::: [
    "swap" >:: test_translate_swap;
    "no_swap" >:: test_translate_no_swap;
    "triple_swap"  >:: test_translate_triple_swap;
    "swap_type_mismatch" >:: test_translate_swap_type_mismatch;
    "swap_prime_notation_sugar"  >:: test_translate_swap_prime_notation_sugar;
    "swap_old_notation_sugar" >:: test_translate_swap_old_notation_sugar;
    "case_single" >:: test_translate_case_single;
    "case_two" >:: test_translate_case_two;
    "case_operators" >:: test_translate_case_operators;
    "loop_terminating_case_expr" >:: test_translate_loop_terminating_case_expr;
    "loop_case_expr_change_var" >:: test_translate_loop_terminating_case_expr_change_var;
    "loop_terminating_triple_case_expr"  >:: test_translate_loop_terminating_triple_case_expr;
    "loop_terminating_conj_expr" >:: test_translate_loop_terminating_conj_expr;
    "translate_for_loop" >:: test_translate_for_loop;
    "translate_ens_res" >:: test_translate_ens_res;
    "translate_for_loop_search_forall_index" >:: test_translate_for_loop_search_forall_index;
    "spec_search" >:: test_sl_to_acsl_spec_search;
    "mutable_arr" >:: test_sl_to_acsl_mutable_arr;
    "mutable_arr_loop" >:: test_sl_to_acsl_mutable_arr_loop;
    "search_replace" >:: test_sl_to_acsl_search_replace;
    "search_replace_loop" >:: test_sl_to_acsl_search_replace_loop;
    "incr_max" >:: test_translate_incr_max;
    "incr_max_spatial_notation" >:: test_translate_incr_max_spatial_notation;
    "abs_diff_pure_notation" >:: test_translate_abs_diff_pure_notation;
    "max_abs" >:: test_translate_max_abs;
    "all_zero_array" >:: test_translate_all_zero_array;
  ]

let () = run_test_tt_main suite
