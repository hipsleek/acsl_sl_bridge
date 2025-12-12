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

let test_sl_to_core_swap_prime_sugar () =
  let test_name = "sl_to_core_swap_prime_sugar" in
  let input =
    "ens (*a)'==(*b) && (*b)'==(*a);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual    = Core.string_of_spec core_spec in
  (* semantics match the prev swap spec *)
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_swap_old_sugar () =
  let test_name = "sl_to_core_swap_old_sugar" in
  let input =
    "ens (*a)==\\old(*b) && (*b)==\\old(*a);"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual    = Core.string_of_spec core_spec in
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

let test_sl_to_core_case_loop_term () =
  let test_name = "sl_to_core_case_loop_term" in
  let input =
    "case {\n" ^
    "  i<30  => req Term[30-i]; ens i'==30;\n" ^
    "  i>=30 => req Term[];     ens i'==i;\n" ^
    "};"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual    = Core.string_of_spec core_spec in
  let expected =
    "params ()\n" ^
    "assumes i < 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n" ^
    "assumes i >= 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_string_equality test_name expected actual

let test_sl_to_core_conj_loop_term () =
  let test_name = "sl_to_core_conj_loop_term" in
  let input =
    "req i<30 && Term[30-i]; ens i'==30;\n" ^
    "/\\ req i>=30 && Term[]; ens i'==i;"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  let actual    = Core.string_of_spec core_spec in
  let expected =
    "params ()\n" ^
    "assumes i < 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n" ^
    "assumes i >= 30\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_string_equality test_name expected actual


let test_sl_to_core_case_guard_uses_post_phase () =
  let test_name = "sl_to_core_case_guard_uses_post_phase" in
  let input =
    "case { a==b => req a->int*(u); ens a->int*(u); };"
  in
  let sl_spec   = parse_spec input in
  let core_spec = Sl_to_core.spec_to_core sl_spec in
  match core_spec.Core.behaviors with
  | [ b ] ->
      begin
        match b.Core.assumes with
        | [ Core.P_eq (Core.T_var (Core.Post, "a"),
                       Core.T_var (Core.Post, "b")) ] ->
            ()
        | _ ->
            let actual = Core.string_of_spec core_spec in
            failwith
              (Printf.sprintf
                 "%s failed.\nExpected assumes on post-phase vars a,b.\nGot Core spec:\n%s\n"
                 test_name actual)
      end
  | _ ->
      failwith
        (Printf.sprintf "%s failed: expected exactly one behavior" test_name)

let () =
  test_sl_to_core_swap ();
  test_sl_to_core_no_swap ();
  test_sl_to_core_triple_swap ();
  test_sl_to_core_swap_type_mismatch ();
  test_sl_to_core_swap_prime_sugar ();
  test_sl_to_core_swap_old_sugar ();
  test_sl_to_core_case_swap ();
  test_sl_to_core_case_loop_term ();
  test_sl_to_core_case_guard_uses_post_phase ();
  test_sl_to_core_conj_loop_term ();
