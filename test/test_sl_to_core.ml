open OUnit2

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf



let test_sl_to_core_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

let test_sl_to_core_no_swap _ctx =
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a)\n" ^
    "ensures H'(a) == H(a)\n" ^
    "frame {a}"
  in
  assert_equal expected actual

let test_sl_to_core_triple_swap _ctx =
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout, c:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b) && valid(c)\n" ^
    "ensures H'(a) == H(c) && H'(b) == H(a) && H'(c) == H(b)\n" ^
    "frame {a, b, c}"
  in
  assert_equal expected actual

let test_sl_to_core_swap_type_mismatch _ctx =
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

let test_sl_to_core_swap_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

let test_sl_to_core_swap_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

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
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes a == b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(a)\n" ^
    "frame {a}\n" ^
    "assumes a != b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}\n" ^
    "assumes a <= b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}\n" ^
    "assumes a < b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}\n" ^
    "assumes a >= b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}\n" ^
    "assumes a > b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

let test_sl_to_core_case_loop_term _ctx =
  let input =
    "case {\n" ^
    "  i<30  => req Term[30-i]; ens i'==30;\n" ^
    "  i>=30 => req Term[];     ens i'==i;\n" ^
    "};"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params ()\n" ^
    "assumes i < 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n" ^
    "variant 30-i\n" ^
    "assumes i >= 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_equal expected actual

let test_sl_to_core_conj_loop_term _ctx =
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  let actual    = Core_printer.string_of_spec core_spec in
  let expected =
    "params ()\n" ^
    "assumes i < 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n" ^
    "variant 30-i\n" ^
    "assumes i >= 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_equal expected actual

let test_sl_to_core_case_guard_uses_post_phase _ctx =
  let input = "case { a==b => req a->int*(u); ens a->int*(u); };" in
  let sl_spec   = parse_spec input in
  let core_spec =Spec_to_core.spec_to_core sl_spec in
  match core_spec.Core.behaviors with
  | [ b ] -> begin
      match b.Core.assumes with
      | [ Core.P_eq (Core.T_var (Core.Post, "a"),
                     Core.T_var (Core.Post, "b")) ] ->
          ()
      | _ ->
          let actual = Core_printer.string_of_spec core_spec in
          assert_failure
            (Printf.sprintf
               "Expected assumes on post-phase vars a,b.\nGot Core spec:\n%s\n"
               actual)
    end
  | _ ->
      assert_failure "Expected exactly one behavior"

let suite =
  "sl_to_core" >::: [
    "swap"                    >:: test_sl_to_core_swap;
    "no_swap"                 >:: test_sl_to_core_no_swap;
    "triple_swap"             >:: test_sl_to_core_triple_swap;
    "swap_type_mismatch"      >:: test_sl_to_core_swap_type_mismatch;
    "swap_prime_sugar"        >:: test_sl_to_core_swap_prime_sugar;
    "swap_old_sugar"          >:: test_sl_to_core_swap_old_sugar;
    "case_swap"               >:: test_sl_to_core_case_swap;
    "case_loop_term"          >:: test_sl_to_core_case_loop_term;
    "conj_loop_term"          >:: test_sl_to_core_conj_loop_term;
    "case_guard_post_phase"   >:: test_sl_to_core_case_guard_uses_post_phase;
  ]

let () = run_test_tt_main suite
