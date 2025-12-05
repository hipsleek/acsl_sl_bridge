open Ast

(*Helper Function to assert expected and actual equality*)
let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

(*Test cases*)

let test_string_of_spec_atom_int () =
  let atom = Atom (PointTo ("a", "int", "u")) in

  let actual = string_of_heap atom in

  let expected = "a->int*(u)" in

  assert_string_equality "string_of_spec_atom_int" actual expected

let test_string_of_spec_atom_char () =
  let atom = Atom (PointTo ("a", "char", "u")) in

  let actual = string_of_heap atom in

  let expected = "a->char*(u)" in

  assert_string_equality "string_of_spec_atom_char" actual expected

let test_string_of_spec_formula () =
  let atom1 = Atom (PointTo ("a", "int", "u")) in
  let atom2 = Atom (PointTo ("b", "int", "v")) in
  let h_pre = Sep (atom1, atom2) in

  let actual = string_of_heap h_pre in

  let expected = "a->int*(u) && b->int*(v)" in

  assert_string_equality "string_of_spec_formula" actual expected


let test_string_of_spec_swap () =
  let h_pre =
    Sep (
      Atom (PointTo ("a", "int", "u")),
      Atom (PointTo ("b", "int", "v"))
    )
  in

  let h_post =
    Sep (
      Atom (PointTo ("a", "int", "v")),
      Atom (PointTo ("b", "int", "u"))
    )
  in

  let spec_swap = { pre = h_pre; post = h_post } in
  let actual = string_of_spec spec_swap in

  let expected =
    "req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);"
  in

  assert_string_equality "string_of_spec_swap" actual expected

  open Ast

let test_spec_of_pointer_pairs_swap () =
  let test_name = "spec_of_pointer_pairs_swap" in
  let pairs = [ ("a", "b"); ("b", "a") ] in
  let spec = spec_of_pointer_pairs pairs in
  let actual = string_of_spec spec in
  let expected =
    "req a->int*(v0) && b->int*(v1); ens a->int*(v1) && b->int*(v0);"
  in
  assert_string_equality test_name expected actual


let () =
  test_string_of_spec_atom_int ();
  test_string_of_spec_atom_char ();
  test_string_of_spec_formula ();
  test_string_of_spec_swap ();
  test_spec_of_pointer_pairs_swap ()
