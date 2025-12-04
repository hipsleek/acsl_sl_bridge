open Ast

(*Helper Function to assert expected and actual equality*)
let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

(*Test cases*)
let test_string_of_spec_empty () =
  let empty = Emp in

  let actual = string_of_heap empty in

  let expected = "" in

  assert_string_equality "string_of_spec_empty" actual expected

let test_string_of_spec_atom () =
  let atom = Atom (PointTo ("a", "u")) in

  let actual = string_of_heap atom in

  let expected = "a->int*(u)" in

  assert_string_equality "string_of_spec_atom" actual expected

let test_string_of_spec_formula () =
  let atom1 = Atom (PointTo ("a", "u")) in
  let atom2 = Atom (PointTo ("b", "v")) in
  let h_pre = Sep (atom1, atom2) in

  let actual = string_of_heap h_pre in

  let expected = "a->int*(u) && b->int*(v)" in

  assert_string_equality "string_of_spec_formula" actual expected


let test_string_of_spec_swap () =
  let h_pre =
    Sep (
      Atom (PointTo ("a", "u")),
      Atom (PointTo ("b", "v"))
    )
  in

  let h_post =
    Sep (
      Atom (PointTo ("a", "v")),
      Atom (PointTo ("b", "u"))
    )
  in

  let spec_swap = { pre = h_pre; post = h_post } in
  let actual = string_of_spec spec_swap in

  let expected =
    "req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);"
  in

  assert_string_equality "string_of_spec_swap" actual expected

let () =
  test_string_of_spec_empty ();
  test_string_of_spec_atom ();
  test_string_of_spec_formula ();
  test_string_of_spec_swap ()
