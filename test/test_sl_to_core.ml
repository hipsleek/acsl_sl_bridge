let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let test_sl_to_core_swap () =
  let test_name = "sl_to_core_swap" in
  let input =
    "req a->int*(u) && b->int*(v);\n" ^
    "ens a->int*(v) && b->int*(u);"
  in
  let sl_spec = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual = Core.string_of_spec core_spec in
  let expected = 
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_no_swap () =
  let test_name = "sl_to_core_no_swap" in
  let input =
    "req a->int*(u);\n" ^
    "ens a->int*(u);"
  in
  let sl_spec = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual = Core.string_of_spec core_spec in
  let expected =
    "params (a:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a)\n" ^
    "ensures H'(a) == H(a)\n" ^
    "frame {a}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_triple_swap () =
  let test_name = "sl_to_core_triple_swap" in
  let input =
    "req a->int*(u) && b->int*(v) && c->int*(w);\n" ^
    "ens a->int*(w) && b->int*(u) && c->int*(v);"
  in
  let sl_spec = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual = Core.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout, c:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b) && valid(c)\n" ^
    "ensures H'(a) == H(c) && H'(b) == H(a) && H'(c) == H(b)\n" ^
    "frame {a, b, c}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_swap_type_mismatch () =
  let test_name = "sl_to_core_swap_type_mismatch" in
  let input =
    "req a->int*(u) && b->char*(v);\n" ^
    "ens a->char*(v) && b->int*(u);"
  in
  let sl_spec = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual = Core.string_of_spec core_spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_case_swap () =
  let test_name = "sl_to_core_case_swap" in
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
  let sl_spec = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual = Core.string_of_spec core_spec in
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
  assert_string_equality test_name expected actual

let () =
  test_sl_to_core_swap ();
  test_sl_to_core_no_swap ();
  test_sl_to_core_triple_swap ();
  test_sl_to_core_swap_type_mismatch ();
  test_sl_to_core_case_swap ();
