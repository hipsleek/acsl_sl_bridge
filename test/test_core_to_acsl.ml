let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let mk_core_atom p t v : Core.heap_atom =
  { Core.loc = p; ty = t; value = v }

(*Unit tests*)
let test_core_to_acsl_swap () =
  let test_name = "core_to_acsl_swap" in
  let core_spec : Core.spec =
    {
      Core.pre =
        [ mk_core_atom "a" "int" "u";
          mk_core_atom "b" "int" "v";
        ];
      Core.post =
        [ mk_core_atom "a" "int" "v";
          mk_core_atom "b" "int" "u";
        ];
    }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_no_swap () =
  let test_name = "core_to_acsl_no_swap" in
  let core_spec : Core.spec =
    {
      Core.pre  = [ mk_core_atom "a" "int" "u" ];
      Core.post = [ mk_core_atom "a" "int" "u" ];
    }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a);
  assigns  *a;
  ensures  *a == \\old(*a);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_triple_swap () =
  let test_name = "core_to_acsl_triple_swap" in
  let core_spec : Core.spec =
    {
      Core.pre =
        [ mk_core_atom "a" "int" "u";
          mk_core_atom "b" "int" "v";
          mk_core_atom "c" "int" "w";
        ];
      Core.post =
        [ mk_core_atom "a" "int" "w";
          mk_core_atom "b" "int" "u";
          mk_core_atom "c" "int" "v";
        ];
    }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b) && \\valid(c);
  assigns  *a, *b, *c;
  ensures  *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_swap_type_mismatch () =
  let test_name = "core_to_acsl_swap_type_mismatch" in
  let core_spec : Core.spec =
    {
      Core.pre =
        [ mk_core_atom "a" "int"  "u";
          mk_core_atom "b" "char" "v";
        ];
      Core.post =
        [ mk_core_atom "a" "char" "v";
          mk_core_atom "b" "int"  "u";
        ];
    }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_string_equality test_name expected actual

let () =
  test_core_to_acsl_swap ();
  test_core_to_acsl_no_swap ();
  test_core_to_acsl_triple_swap ();
  test_core_to_acsl_swap_type_mismatch ();
