let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let mk_inout_param (name : string) : Core.param =
  Core.mk_param Core.InOut name

let mk_basic_spec (ptrs : string list) (eqs : Core.predicate list) : Core.spec =
  {
    Core.params = List.map mk_inout_param ptrs;
    frame    = ptrs;
    requires = List.map Core.valid ptrs;
    ensures  = eqs;
  }

(*Unit tests*)
let test_core_to_acsl_swap () =
  let test_name = "core_to_acsl_swap" in
  let ptrs = ["a"; "b"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "b");
      Core.eq (Core.heap_post "b") (Core.heap_pre "a");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
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
  let ptrs = ["a"; "b"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "a");
      Core.eq (Core.heap_post "b") (Core.heap_pre "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*a) && *b == \\old(*b);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_triple_swap () =
  let test_name = "core_to_acsl_swap" in
  let ptrs = ["a"; "b"; "c"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "c");
      Core.eq (Core.heap_post "b") (Core.heap_pre "a");
      Core.eq (Core.heap_post "c") (Core.heap_pre "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b) && \\valid(c);
  assigns  *a, *b, *c;
  ensures  *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  assert_string_equality test_name expected actual

(* let test_core_to_acsl_swap_type_mismatch () =
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
  assert_string_equality test_name expected actual *)

let () =
  test_core_to_acsl_swap ();
  test_core_to_acsl_no_swap ();
  test_core_to_acsl_triple_swap ();
  (* test_core_to_acsl_swap_type_mismatch (); *)
