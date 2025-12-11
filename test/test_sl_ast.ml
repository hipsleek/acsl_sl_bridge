open Sl_ast

let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

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

let test_string_of_spec_sugar_prime_swap () =
  let spec = Sugar_prime [ ("a", "b"); ("b", "a") ] in
  let actual = Sl_ast.string_of_spec spec in
  let expected = "ens (*a)'==(*b) && (*b)'==(*a);" in
  assert_string_equality "string_of_spec_sugar_prime_swap" expected actual

let test_string_of_spec_sugar_old_swap () =
  let spec = Sugar_old [ ("a", "b"); ("b", "a") ] in
  let actual = Sl_ast.string_of_spec spec in
  let expected = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  assert_string_equality "string_of_spec_sugar_old_swap" expected actual

let test_string_of_conditional_eq_ptrs () =
  let c = E_eq (A_var "a", A_var "b") in
  let actual = string_of_expr c in
  let expected = "a==b" in
  assert_string_equality "string_of_conditional_eq_ptrs" expected actual

let test_string_of_conditional_lt_int () =
  let c = E_lt (A_var "i", A_int 30) in
  let actual = string_of_expr c in
  let expected = "i<30" in
  assert_string_equality "string_of_conditional_lt_int" expected actual

let test_string_of_arith_sub_in_conditional () =
  let c = E_eq (A_sub (A_int 30, A_var "i"), A_int 0) in
  let actual = string_of_expr c in
  let expected = "30-i==0" in
  assert_string_equality "string_of_arith_sub_in_conditional" expected actual

let test_string_of_arith_post_var () =
  let e = A_post_var "i" in
  let actual = string_of_arith e in
  let expected = "i'" in
  assert_string_equality "string_of_arith_post_var" expected actual

let test_string_of_arith_old_var () =
  let e = A_old (A_var "i") in
  let actual = string_of_arith e in
  let expected = "\\old(i)" in
  assert_string_equality "string_of_arith_old_var" expected actual

let test_spec_of_pointer_eq_eq () =
  let test_name = "spec_of_pointer_eq_eq" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in

  let spec = Case [case_one] in
  let actual = Sl_ast.string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u);};" in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_neq () =
  let test_name = "spec_of_pointer_eq_neq" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let heap_a_u_b_v =
    Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v")))
  in
  let heap_a_v_b_u =
    Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u")))
  in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in
  let case_two : case_spec =
    {
      test = E_neq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u_b_v;
      post = Post_heap(heap_a_v_b_u);
    }
  in

  let spec = Case [case_one; case_two] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_lte () =
  let test_name = "spec_of_pointer_eq_lte" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let heap_a_u_b_v =
    Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v")))
  in
  let heap_a_v_b_u =
    Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u")))
  in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in
  let case_two : case_spec =
    {
      test = E_lte (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u_b_v;
      post = Post_heap(heap_a_v_b_u);
    }
  in

  let spec = Case [case_one; case_two] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_lt () =
  let test_name = "spec_of_pointer_eq_lt" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let heap_a_u_b_v =
    Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v")))
  in
  let heap_a_v_b_u =
    Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u")))
  in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in
  let case_two : case_spec =
    {
      test = E_lt (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u_b_v;
      post = Post_heap(heap_a_v_b_u);
    }
  in

  let spec = Case [case_one; case_two] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_gte () =
  let test_name = "spec_of_pointer_eq_gte" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let heap_a_u_b_v =
    Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v")))
  in
  let heap_a_v_b_u =
    Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u")))
  in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in
  let case_two : case_spec =
    {
      test = E_gte (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u_b_v;
      post = Post_heap(heap_a_v_b_u);
    }
  in

  let spec = Case [case_one; case_two] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  assert_string_equality test_name expected actual

let test_spec_of_pointer_eq_gt () =
  let test_name = "spec_of_pointer_eq_gt" in
  let heap_a_u = Atom (PointTo ("a", "int", "u")) in

  let heap_a_u_b_v =
    Sep (Atom (PointTo ("a", "int", "u")), Atom (PointTo ("b", "int", "v")))
  in
  let heap_a_v_b_u =
    Sep (Atom (PointTo ("a", "int", "v")), Atom (PointTo ("b", "int", "u")))
  in

  let case_one : case_spec =
    {
      test = E_eq (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u;
      post = Post_heap(heap_a_u);
    }
  in
  let case_two : case_spec =
    {
      test = E_gt (A_var "a", A_var "b");
      term = None;
      pre = heap_a_u_b_v;
      post = Post_heap(heap_a_v_b_u);
    }
  in

  let spec = Case [case_one; case_two] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);};"
  in
  assert_string_equality test_name expected actual


let test_loop_case_with_variant () =
  let heap_i_u = Atom (PointTo ("i", "int", "u")) in

  let case_loop : case_spec =
    {
      test = E_lt (A_var "i", A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = Post_expr (E_eq (A_post_var "i", A_int 30));
    }
  in
  let spec = Case [case_loop] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30;};"
  in
  assert_string_equality "loop_case_with_variant" expected actual

let test_loop_case_with_variant_prime () =
  let heap_i_u = Atom (PointTo ("i", "int", "u")) in

  let case_loop : case_spec =
    {
      test = E_lt (A_var "i", A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i"))); 
      pre  = heap_i_u;
      post = Post_expr (E_eq (A_post_var "i", A_var "i"));
    }
  in
  let spec = Case [case_loop] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==i;};"
  in
  assert_string_equality "loop_case_with_variant" expected actual

let test_loop_case_with_variant_old () =
  let heap_i_u = Atom (PointTo ("i", "int", "u")) in

  let case_loop : case_spec =
    {
      test = E_lt (A_var "i", A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = Post_expr (E_eq (A_var "i", A_old (A_var "i")));
    }
  in
  let spec   = Case [case_loop] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {i<30 => req Term[30-i]; ens i==\\old(i);};"
  in
  assert_string_equality "loop_case_with_variant_old" expected actual

let test_loop_case_with_variant_and_exit () =
  let heap_i_u = Atom (PointTo ("i", "int", "u")) in

  let case1 : case_spec =
    {
      test = E_lt (A_var "i", A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = Post_expr (E_eq (A_post_var "i", A_int 30));
    }
  in
  let case2 : case_spec =
    {
      test = E_gte (A_var "i", A_int 30);
      term = Some Term_none;
      pre  = heap_i_u;
      post = Post_expr (E_eq (A_post_var "i", A_var "i"));
    }
  in

  let spec = Case [case1; case2] in
  let actual = Sl_ast.string_of_spec spec in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30; \
     i>=30 => req Term[]; ens i'==i;};"
  in
  assert_string_equality "loop_case_with_variant_and_exit" expected actual

let () =
  test_string_of_spec_atom_int ();
  test_string_of_spec_atom_char ();
  test_string_of_spec_formula ();
  test_string_of_spec_swap ();
  test_string_of_spec_sugar_prime_swap ();
  test_string_of_spec_sugar_old_swap ();

  test_string_of_conditional_eq_ptrs ();
  test_string_of_conditional_lt_int ();
  test_string_of_arith_sub_in_conditional ();
  test_string_of_arith_post_var ();
  test_string_of_arith_old_var ();

  test_spec_of_pointer_eq_eq ();
  test_spec_of_pointer_eq_neq ();
  test_spec_of_pointer_eq_gte ();
  test_spec_of_pointer_eq_gt ();
  test_spec_of_pointer_eq_lte ();
  test_spec_of_pointer_eq_lt ();

  test_loop_case_with_variant ();
  test_loop_case_with_variant_prime ();
  test_loop_case_with_variant_old ();
  test_loop_case_with_variant_and_exit ();
