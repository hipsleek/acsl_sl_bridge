open Core

(* Helper: assert expected and actual equality *)
let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

(* Helper: Build atom *)
let mk_atom p t v =
  { Core.loc = p; ty = t; value = v }

let test_core_string_of_heap_atom_int () =
  let heap = [ mk_atom "a" "int" "u" ] in
  let actual = Core.string_of_heap heap in
  let expected = "a->int*(u)" in
  assert_string_equality "core_string_of_heap_atom_int" expected actual

let test_core_string_of_heap_atom_char () =
  let heap = [ mk_atom "a" "char" "u" ] in
  let actual = Core.string_of_heap heap in
  let expected = "a->char*(u)" in
  assert_string_equality "core_string_of_heap_atom_char" expected actual

let test_core_string_of_heap_formula () =
  let heap =
    [
      mk_atom "a" "int" "u";
      mk_atom "b" "int" "v";
    ]
  in
  let actual = Core.string_of_heap heap in
  let expected = "a->int*(u) && b->int*(v)" in
  assert_string_equality "core_string_of_heap_formula" expected actual

let test_core_string_of_spec_swap () =
  let pre =
    [
      mk_atom "a" "int" "u";
      mk_atom "b" "int" "v";
    ]
  in
  let post =
    [
      mk_atom "a" "int" "v";
      mk_atom "b" "int" "u";
    ]
  in
  let spec_swap : Core.spec = { pre; post } in
  let actual = Core.string_of_spec spec_swap in
  let expected =
    "req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);"
  in
  assert_string_equality "core_string_of_spec_swap" expected actual

let () =
  test_core_string_of_heap_atom_int ();
  test_core_string_of_heap_atom_char ();
  test_core_string_of_heap_formula ();
  test_core_string_of_spec_swap ()
