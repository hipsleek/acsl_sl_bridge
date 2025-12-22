 open OUnit2
open Sl_ast
open Sl_ast_printer

let test_framework (expected : string) (actual : string) : unit =
  assert_equal
    ~printer:(fun s -> "\n" ^ s ^ "\n")
    expected
    actual
 let v (x : string) : expr = EVar x
let i (n : int) : expr = EConstInt n
 let add a b : expr = EBinop (BAdd, a, b)
let sub a b : expr = EBinop (BSub, a, b)
 let eq a b : expr = EBinop (BEq, a, b)
let neq a b : expr = EBinop (BNeq, a, b)
let lt a b : expr = EBinop (BLt, a, b)
let lte a b : expr = EBinop (BLe, a, b)
let gte a b : expr = EBinop (BGe, a, b)
let gt a b : expr = EBinop (BGt, a, b)

let post (e : expr) : expr = EPost e
let old (e : expr) : expr = EOld e
let deref (e : expr) : expr = EDeref e
 let pt (p : string) (ty : string) (x : string) : sl =
  SHeap (HPt { loc = v p; ty; value = v x })

let sep2 a b : sl = SSep [ a; b ]
let and2 a b : sl = SAnd [ a; b ]

let req (p : sl) : clause = CReq p
let ens (p : sl) : clause = CEns p
let term (e : expr option) : clause = CVar e

let beh ?name ?(assumes = STrue) (body : clause list) : behavior =
  { name; assumes; body }
 let test_string_of_spec_atom_int _ =
  let atom = pt "a" "int" "u" in
  test_framework "a->int*(u)" (string_of_sl atom)

let test_string_of_spec_atom_char _ =
  let atom = pt "a" "char" "u" in
  test_framework "a->char*(u)" (string_of_sl atom)

let test_string_of_spec_formula _ =
  let h_pre = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  test_framework "a->int*(u) ** b->int*(v)" (string_of_sl h_pre)

let test_string_of_spec_swap _ =
  let pre = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let post_ = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in
  let spec_swap : spec =
    { ret = None; behaviors = [ beh [ req pre; ens post_ ] ] }
  in
  let expected =
    "req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);"
  in
  test_framework expected (string_of_spec spec_swap)
 let test_string_of_spec_sugar_prime_swap _ =
  let e1 = eq (post (deref (v "a"))) (deref (v "b")) in
  let e2 = eq (post (deref (v "b"))) (deref (v "a")) in
  let post_ = and2 (SPure e1) (SPure e2) in
  let spec = { ret = None; behaviors = [ beh [ ens post_ ] ] } in
  test_framework "ens (*a)' == (*b) && (*b)' == (*a);" (string_of_spec spec)

let test_string_of_spec_sugar_old_swap _ =
  let e1 = eq (deref (v "a")) (old (deref (v "b"))) in
  let e2 = eq (deref (v "b")) (old (deref (v "a"))) in
  let post_ = and2 (SPure e1) (SPure e2) in
  let spec = { ret = None; behaviors = [ beh [ ens post_ ] ] } in
  test_framework "ens (*a) == \\old(*b) && (*b) == \\old(*a);" (string_of_spec spec)
 let test_string_of_conditional_eq_ptrs _ =
  let e = eq (v "a") (v "b") in
  test_framework "a == b" (string_of_expr e)

let test_string_of_conditional_lt_int _ =
  let e = lt (v "i") (i 30) in
  test_framework "i < 30" (string_of_expr e)

let test_string_of_arith_sub_in_conditional _ =
  let e = eq (sub (i 30) (v "i")) (i 0) in
  test_framework "30 - i == 0" (string_of_expr e)

let test_string_of_arith_post_var _ =
  test_framework "i'" (string_of_expr (post (v "i")))

let test_string_of_arith_old_var _ =
  test_framework "\\old(i)" (string_of_expr (old (v "i")))
 let test_spec_of_pointer_eq_eq _ =
  let heap_a_u = pt "a" "int" "u" in
  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let spec = { ret = None; behaviors = [ b1 ] } in
  test_framework
    "case {a == b => req a->int*(u); ens a->int*(u);};"
    (string_of_spec spec)

let test_spec_of_pointer_eq_neq _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let heap_a_v_b_u = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in

  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let b2 =
    beh
      ~assumes:(SPure (neq (v "a") (v "b")))
      [ req heap_a_u_b_v; ens heap_a_v_b_u ]
  in

  let spec = { ret = None; behaviors = [ b1; b2 ] } in
  let expected =
    "case {a == b => req a->int*(u); ens a->int*(u); \
     a != b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_lte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let heap_a_v_b_u = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in

  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let b2 =
    beh
      ~assumes:(SPure (lte (v "a") (v "b")))
      [ req heap_a_u_b_v; ens heap_a_v_b_u ]
  in

  let spec = { ret = None; behaviors = [ b1; b2 ] } in
  let expected =
    "case {a == b => req a->int*(u); ens a->int*(u); \
     a <= b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_lt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let heap_a_v_b_u = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in

  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let b2 =
    beh
      ~assumes:(SPure (lt (v "a") (v "b")))
      [ req heap_a_u_b_v; ens heap_a_v_b_u ]
  in

  let spec = { ret = None; behaviors = [ b1; b2 ] } in
  let expected =
    "case {a == b => req a->int*(u); ens a->int*(u); \
     a < b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_gte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let heap_a_v_b_u = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in

  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let b2 =
    beh
      ~assumes:(SPure (gte (v "a") (v "b")))
      [ req heap_a_u_b_v; ens heap_a_v_b_u ]
  in

  let spec = { ret = None; behaviors = [ b1; b2 ] } in
  let expected =
    "case {a == b => req a->int*(u); ens a->int*(u); \
     a >= b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_gt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = sep2 (pt "a" "int" "u") (pt "b" "int" "v") in
  let heap_a_v_b_u = sep2 (pt "a" "int" "v") (pt "b" "int" "u") in

  let b1 =
    beh
      ~assumes:(SPure (eq (v "a") (v "b")))
      [ req heap_a_u; ens heap_a_u ]
  in
  let b2 =
    beh
      ~assumes:(SPure (gt (v "a") (v "b")))
      [ req heap_a_u_b_v; ens heap_a_v_b_u ]
  in

  let spec = { ret = None; behaviors = [ b1; b2 ] } in
  let expected =
    "case {a == b => req a->int*(u); ens a->int*(u); \
     a > b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_loop_case_with_variant _ =
  let b =
    beh
      ~assumes:(SPure (lt (v "i") (i 30)))
      [ term (Some (sub (i 30) (v "i"))); ens (SPure (eq (post (v "i")) (i 30))) ]
  in
  test_framework
    "case {i < 30 => req Term[30 - i]; ens i' == 30;};"
    (string_of_spec { ret = None; behaviors = [ b ] })

let test_loop_case_with_variant_prime _ =
  let b =
    beh
      ~assumes:(SPure (lt (v "i") (i 30)))
      [ term (Some (sub (i 30) (v "i"))); ens (SPure (eq (post (v "i")) (v "i"))) ]
  in
  test_framework
    "case {i < 30 => req Term[30 - i]; ens i' == i;};"
    (string_of_spec { ret = None; behaviors = [ b ] })

let test_loop_case_with_variant_old _ =
  let b =
    beh
      ~assumes:(SPure (lt (v "i") (i 30)))
      [ term (Some (sub (i 30) (v "i"))); ens (SPure (eq (v "i") (old (v "i")))) ]
  in
  test_framework
    "case {i < 30 => req Term[30 - i]; ens i == \\old(i);};"
    (string_of_spec { ret = None; behaviors = [ b ] })

let test_loop_case_with_variant_and_exit _ =
  let b1 =
    beh
      ~assumes:(SPure (lt (v "i") (i 30)))
      [ term (Some (sub (i 30) (v "i"))); ens (SPure (eq (post (v "i")) (i 30))) ]
  in
  let b2 =
    beh
      ~assumes:(SPure (gte (v "i") (i 30)))
      [ term None; ens (SPure (eq (post (v "i")) (v "i"))) ]
  in
  let expected =
    "case {i < 30 => req Term[30 - i]; ens i' == 30; \
     i >= 30 => req Term[]; ens i' == i;};"
  in
  test_framework expected (string_of_spec { ret = None; behaviors = [ b1; b2 ] })

let test_loop_single_req_ens_conj_post _ =
  let post_conj =
    and2
      (SPure (eq (post (v "i")) (i 10)))
      (SPure (eq (post (v "a"))
                 (add (v "a") (sub (post (v "i")) (v "i")))))
  in
  let b =
    beh
      ~assumes:(SPure (lte (v "i") (i 10)))
      [ term (Some (sub (i 10) (v "i"))); ens post_conj ]
  in
  let expected =
    "case {i <= 10 => req Term[10 - i]; ens i' == 10 && a' == a + i' - i;};"
  in
  test_framework expected (string_of_spec { ret = None; behaviors = [ b ] })
 let test_ens_result_binder _ =
  let b = beh [ ens (SPure (eq (v "r") (add (v "a") (i 10)))) ] in
  let spec = { ret = Some "r"; behaviors = [ b ] } in
  test_framework "ens[r] r == a + 10;" (string_of_spec spec)

let test_loop_case_with_forall_index_variant _ =
  let b =
    beh
      ~assumes:
        (SAnd
           [
             (* 0 <= i && i <= length *)
             SAnd
               [
                 SPure (lte (i 0) (v "i"));
                 SPure (lte (v "i") (v "length"));
               ];

             (* forall size_t j. (0<=j && j<i) ==> *(array + j) != element *)
             SForall
               ( [ ("j", Some (SUser "size_t")) ],
                 SImplies
                   ( SAnd
                       [
                         SPure (lte (i 0) (v "j"));
                         SPure (lt (v "j") (v "i"));
                       ],
                     SPure
                       (neq
                          (deref (add (v "array") (v "j")))
                          (v "element")) ) );
           ])
      [
        term (Some (sub (v "length") (v "i")));
        ens STrue;
      ]
  in
  test_framework
    "case {0 <= i && i <= length && \\forall j:size_t. (0 <= j && j < i) => (*(array + j)) != element => req Term[length - i]; ens \\true;};"
    (string_of_spec { ret = None; behaviors = [ b ] })

let suite =
  "sl_ast_printer tests" >::: [
    "string_of_spec_atom_int" >:: test_string_of_spec_atom_int;
    "string_of_spec_atom_char" >:: test_string_of_spec_atom_char;
    "string_of_spec_formula" >:: test_string_of_spec_formula;
    "string_of_spec_swap" >:: test_string_of_spec_swap;
    "string_of_spec_sugar_prime_swap" >:: test_string_of_spec_sugar_prime_swap;
    "string_of_spec_sugar_old_swap" >:: test_string_of_spec_sugar_old_swap;

    "string_of_conditional_eq_ptrs" >:: test_string_of_conditional_eq_ptrs;
    "string_of_conditional_lt_int" >:: test_string_of_conditional_lt_int;
    "string_of_arith_sub_in_conditional" >:: test_string_of_arith_sub_in_conditional;
    "string_of_arith_post_var" >:: test_string_of_arith_post_var;
    "string_of_arith_old_var" >:: test_string_of_arith_old_var;

    "spec_of_pointer_eq_eq" >:: test_spec_of_pointer_eq_eq;
    "spec_of_pointer_eq_neq" >:: test_spec_of_pointer_eq_neq;
    "spec_of_pointer_eq_gte" >:: test_spec_of_pointer_eq_gte;
    "spec_of_pointer_eq_gt" >:: test_spec_of_pointer_eq_gt;
    "spec_of_pointer_eq_lte" >:: test_spec_of_pointer_eq_lte;
    "spec_of_pointer_eq_lt" >:: test_spec_of_pointer_eq_lt;

    "loop_case_with_variant" >:: test_loop_case_with_variant;
    "loop_case_with_variant_prime" >:: test_loop_case_with_variant_prime;
    "loop_case_with_variant_old" >:: test_loop_case_with_variant_old;
    "loop_case_with_variant_and_exit" >:: test_loop_case_with_variant_and_exit;
    "loop_single_req_ens_conj_post" >:: test_loop_single_req_ens_conj_post;

    "ens_result_binder" >:: test_ens_result_binder;

    "loop_case_with_forall_index_variant" >:: test_loop_case_with_forall_index_variant;
  ]

let () = run_test_tt_main suite
