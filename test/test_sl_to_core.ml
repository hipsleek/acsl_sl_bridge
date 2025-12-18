open OUnit2

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let test_framework (input : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") input actual 

let test_sl_to_core_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_no_swap _ctx =
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a)\n" ^
    "ensures H'(a) == H(a)\n" ^
    "assigns { *a }"
  in
  test_framework expected actual

let test_sl_to_core_triple_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b) && valid(c)\n" ^
    "ensures H'(a) == H(c) && H'(b) == H(a) && H'(c) == H(b)\n" ^
    "assigns { *a, *b, *c }"
  in
  test_framework expected actual

let test_sl_to_core_swap_type_mismatch _ctx =
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_swap_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_swap_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected actual

let test_sl_to_core_case_swap _ctx =
  let input =
    "case {\n" ^
    "  a==b => req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a<=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a<b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a>=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a>b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "behavior case1\n" ^
    "assumes a == b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(a)\n" ^
    "assigns { *a, *b }\n" ^

    "behavior case2\n" ^
    "assumes a != b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }\n" ^

    "behavior case3\n" ^
    "assumes a <= b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }\n" ^

    "behavior case4\n" ^
    "assumes a < b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }\n" ^

    "behavior case5\n" ^
    "assumes a >= b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }\n" ^

    "behavior case6\n" ^
    "assumes a > b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected actual

(* NEW: Loop_case translation using /\\ syntax (two clauses). *)
let test_sl_to_core_loop_case_term _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind loop\n" ^
    "params ()\n" ^
    "assumes i < 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "assigns { i }\n" ^
    "variant 30 - i"
  in
  test_framework expected actual

let test_sl_to_core_loop_simple_term_and_frame _ctx =
  let input =
    "req i<=10 && Term[10-i]; ens i'==10 && a'==a;"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind loop\n" ^
    "params ()\n" ^
    "assumes i <= 10\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "assigns { a, i }\n" ^
    "variant 10 - i"
  in
  test_framework expected actual

let test_sl_to_core_ens_result _ctx =
  let input =
    "ens[r] r==a+10;"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures \\result == a + 10\n" ^
    "assigns {}"
  in
  test_framework expected actual

let suite =
  "sl_to_core" >::: [
    "swap"                         >:: test_sl_to_core_swap;
    "no_swap"                      >:: test_sl_to_core_no_swap;
    "triple_swap"                  >:: test_sl_to_core_triple_swap;
    "swap_type_mismatch"           >:: test_sl_to_core_swap_type_mismatch;
    "swap_prime_sugar"             >:: test_sl_to_core_swap_prime_sugar;
    "swap_old_sugar"               >:: test_sl_to_core_swap_old_sugar;
    "case_swap"                    >:: test_sl_to_core_case_swap;
    "loop_case_term"               >:: test_sl_to_core_loop_case_term;
    "loop_simple_term_and_frame"   >:: test_sl_to_core_loop_simple_term_and_frame;
    "sl_to_core_ens_result"        >:: test_sl_to_core_ens_result;
  ]

let () = run_test_tt_main suite
