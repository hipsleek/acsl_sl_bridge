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
  let actual = string_of_base_spec spec_swap in

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


let test_spec_of_pointer_eq_eq () =
  let test_name = "spec_of_pointer_eq_neq" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in

  let spec = Case [case_one] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_neq () =
  let test_name = "spec_of_pointer_eq_neq" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  (* case 2 *)
  let heap_a_u_b_v = Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v"))) in
  let heap_a_v_b_u = Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u"))) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = E_neq (E_ptr "a", E_ptr "b");
      pre = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [case_one; case_two] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u); a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_lte () =
  let test_name = "spec_of_pointer_eq_lte" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  (* case 2 *)
  let heap_a_u_b_v = Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v"))) in
  let heap_a_v_b_u = Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u"))) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = E_lte (E_ptr "a", E_ptr "b");
      pre = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [case_one; case_two] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u); a<=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_lt () =
  let test_name = "spec_of_pointer_eq_lt" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  (* case 2 *)
  let heap_a_u_b_v = Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v"))) in
  let heap_a_v_b_u = Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u"))) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = E_lt (E_ptr "a", E_ptr "b");
      pre = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [case_one; case_two] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u); a<b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_gte () =
  let test_name = "spec_of_pointer_eq_gte" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  (* case 2 *)
  let heap_a_u_b_v = Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v"))) in
  let heap_a_v_b_u = Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u"))) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = E_gte (E_ptr "a", E_ptr "b");
      pre = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [case_one; case_two] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u); a>=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_gt () =
  let test_name = "spec_of_pointer_eq_gt" in
  (* Case 1 *)
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  (* case 2 *)
  let heap_a_u_b_v = Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v"))) in
  let heap_a_v_b_u = Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u"))) in

  let case_one : case_spec =
    {
      test = E_eq (E_ptr "a", E_ptr "b");
      pre = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = E_gt (E_ptr "a", E_ptr "b");
      pre = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [case_one; case_two] in

  let actual = Ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u); a>b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};" in
  assert_string_equality test_name expected actual



let () =
  test_string_of_spec_atom_int ();
  test_string_of_spec_atom_char ();
  test_string_of_spec_formula ();
  test_string_of_spec_swap ();
  test_spec_of_pointer_pairs_swap ();

  test_spec_of_pointer_eq_eq ();
  test_spec_of_pointer_eq_neq ();
  test_spec_of_pointer_eq_gte ();
  test_spec_of_pointer_eq_gt ();
  test_spec_of_pointer_eq_lte ();
  test_spec_of_pointer_eq_lt ();
