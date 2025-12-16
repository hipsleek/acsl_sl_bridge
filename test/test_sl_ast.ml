open OUnit2
open Sl_ast
open Sl_ast_printer

let test_framework (expected : string) (actual : string) : unit =
  assert_equal
    ~printer:(fun s -> "\n" ^ s ^ "\n")
    expected
    actual

(* ---------- Helpers to keep tests readable ---------- *)

let pt p t v : assertion =
  A_heap_atom (PointTo (p, t, v))

let ( * ) a b : assertion = A_sep (a, b)

let pure (p : pure_atom) : assertion = A_pure p

let ( &&& ) a b : assertion = A_and (a, b)

let eq e1 e2 : assertion = pure (P_eq (e1, e2))
let neq e1 e2 : assertion = pure (P_neq (e1, e2))
let lt e1 e2 : assertion = pure (P_lt (e1, e2))
let lte e1 e2 : assertion = pure (P_lte (e1, e2))
let gte e1 e2 : assertion = pure (P_gte (e1, e2))
let gt e1 e2 : assertion = pure (P_gt (e1, e2))

(* ---------- Assertion printing tests (was heap printing) ---------- *)

let test_string_of_spec_atom_int _ =
  let atom = pt "a" "int" "u" in
  let actual = string_of_assertion atom in
  let expected = "a->int*(u)" in
  test_framework expected actual

let test_string_of_spec_atom_char _ =
  let atom = pt "a" "char" "u" in
  let actual = string_of_assertion atom in
  let expected = "a->char*(u)" in
  test_framework expected actual

let test_string_of_spec_formula _ =
  let h_pre = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let actual = string_of_assertion h_pre in
  let expected = "a->int*(u) ** b->int*(v)" in
  test_framework expected actual

let test_string_of_spec_swap _ =
  let pre  = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let post = (pt "a" "int" "v") * (pt "b" "int" "u") in
  let spec_swap : base_spec = { pre; post } in
  let actual = string_of_base_spec spec_swap in
  let expected =
    "req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);"
  in
  test_framework expected actual

(* ---------- Sugar tests (sugar is now an assertion node) ---------- *)

let test_string_of_spec_sugar_prime_swap _ =
  let spec =
    Ens (A_sugar_prime [ ("a", "b"); ("b", "a") ])
  in
  let actual = string_of_spec spec in
  let expected = "ens (*a)'==(*b) && (*b)'==(*a);"
  in
  test_framework expected actual

let test_string_of_spec_sugar_old_swap _ =
  let spec =
    Ens (A_sugar_old [ ("a", "b"); ("b", "a") ])
  in
  let actual = string_of_spec spec in
  let expected = "ens (*a)==\\old(*b) && (*b)==\\old(*a);"
  in
  test_framework expected actual


(* ---------- Pure / arith printing tests ---------- *)

let test_string_of_conditional_eq_ptrs _ =
  let p = P_eq (A_var "a", A_var "b") in
  let actual = string_of_pure_atom p in
  let expected = "a==b" in
  test_framework expected actual

let test_string_of_conditional_lt_int _ =
  let p = P_lt (A_var "i", A_int 30) in
  let actual = string_of_pure_atom p in
  let expected = "i<30" in
  test_framework expected actual

let test_string_of_arith_sub_in_conditional _ =
  let p = P_eq (A_sub (A_int 30, A_var "i"), A_int 0) in
  let actual = string_of_pure_atom p in
  let expected = "30-i==0" in
  test_framework expected actual

let test_string_of_arith_post_var _ =
  let e = A_post_var "i" in
  let actual = string_of_arith e in
  let expected = "i'" in
  test_framework expected actual

let test_string_of_arith_old_var _ =
  let e = A_old (A_var "i") in
  let actual = string_of_arith e in
  let expected = "\\old(i)" in
  test_framework expected actual

(* ---------- Case printing tests (guard/pre/post are assertions now) ---------- *)

let test_spec_of_pointer_eq_eq _ =
  let heap_a_u = pt "a" "int" "u" in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in

  let spec = Case [ case_one ] in
  let actual = string_of_spec spec in
  let expected = "case {a==b => req a->int*(u); ens a->int*(u);};" in
  test_framework expected actual

let test_spec_of_pointer_eq_neq _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = neq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [ case_one; case_two ] in
  let actual = string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a!=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected actual

let test_spec_of_pointer_eq_lte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = lte (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [ case_one; case_two ] in
  let actual = string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected actual

let test_spec_of_pointer_eq_lt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = lt (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [ case_one; case_two ] in
  let actual = string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected actual

let test_spec_of_pointer_eq_gte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = gte (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [ case_one; case_two ] in
  let actual = string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected actual

let test_spec_of_pointer_eq_gt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    {
      test = eq (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u;
      post = heap_a_u;
    }
  in
  let case_two : case_spec =
    {
      test = gt (A_var "a") (A_var "b");
      term = None;
      pre  = heap_a_u_b_v;
      post = heap_a_v_b_u;
    }
  in

  let spec = Case [ case_one; case_two ] in
  let actual = string_of_spec spec in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected actual

(* ---------- Loop/variant style cases (post is an assertion; conj uses A_and) ---------- *)

let test_loop_case_with_variant _ =
  let heap_i_u = pt "i" "int" "u" in

  let case_loop : case_spec =
    {
      test = lt (A_var "i") (A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = eq (A_post_var "i") (A_int 30);
    }
  in
  let spec = Case [ case_loop ] in
  let actual = string_of_spec spec in
  let expected = "case {i<30 => req Term[30-i]; ens i'==30;};" in
  test_framework expected actual

let test_loop_case_with_variant_prime _ =
  let heap_i_u = pt "i" "int" "u" in

  let case_loop : case_spec =
    {
      test = lt (A_var "i") (A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = eq (A_post_var "i") (A_var "i");
    }
  in
  let spec = Case [ case_loop ] in
  let actual = string_of_spec spec in
  let expected = "case {i<30 => req Term[30-i]; ens i'==i;};" in
  test_framework expected actual

let test_loop_case_with_variant_old _ =
  let heap_i_u = pt "i" "int" "u" in

  let case_loop : case_spec =
    {
      test = lt (A_var "i") (A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = eq (A_var "i") (A_old (A_var "i"));
    }
  in
  let spec = Case [ case_loop ] in
  let actual = string_of_spec spec in
  let expected = "case {i<30 => req Term[30-i]; ens i==\\old(i);};" in
  test_framework expected actual

let test_loop_case_with_variant_and_exit _ =
  let heap_i_u = pt "i" "int" "u" in

  let case1 : case_spec =
    {
      test = lt (A_var "i") (A_int 30);
      term = Some (Term (A_sub (A_int 30, A_var "i")));
      pre  = heap_i_u;
      post = eq (A_post_var "i") (A_int 30);
    }
  in
  let case2 : case_spec =
    {
      test = gte (A_var "i") (A_int 30);
      term = Some Term_none;
      pre  = heap_i_u;
      post = eq (A_post_var "i") (A_var "i");
    }
  in

  let spec = Case [ case1; case2 ] in
  let actual = string_of_spec spec in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30; \
     i>=30 => req Term[]; ens i'==i;};"
  in
  test_framework expected actual

let test_loop_single_req_ens_conj_post _ =
  let dummy_pre = pt "_" "int" "_" in

  let post_conj =
    eq (A_post_var "i") (A_int 10)
    &&&
    eq
      (A_post_var "a")
      (A_add (A_var "a", A_sub (A_post_var "i", A_var "i")))
  in

  let loop_case : case_spec =
    {
      test = lte (A_var "i") (A_int 10);
      term = Some (Term (A_sub (A_int 10, A_var "i")));
      pre  = dummy_pre;
      post = post_conj;
    }
  in

  let spec = Case [ loop_case ] in
  let actual = string_of_spec spec in
  let expected =
    "case {i<=10 => req Term[10-i]; ens i'==10 && a'==a+i'-i;};"
  in
  test_framework expected actual

(* ---------- Test suite ---------- *)

let suite =
  "sl_ast_printer tests" >::: [
    "string_of_spec_atom_int"            >:: test_string_of_spec_atom_int;
    "string_of_spec_atom_char"           >:: test_string_of_spec_atom_char;
    "string_of_spec_formula"             >:: test_string_of_spec_formula;
    "string_of_spec_swap"                >:: test_string_of_spec_swap;
    "string_of_spec_sugar_prime_swap"    >:: test_string_of_spec_sugar_prime_swap;
    "string_of_spec_sugar_old_swap"      >:: test_string_of_spec_sugar_old_swap;

    "string_of_conditional_eq_ptrs"      >:: test_string_of_conditional_eq_ptrs;
    "string_of_conditional_lt_int"       >:: test_string_of_conditional_lt_int;
    "string_of_arith_sub_in_conditional" >:: test_string_of_arith_sub_in_conditional;
    "string_of_arith_post_var"           >:: test_string_of_arith_post_var;
    "string_of_arith_old_var"            >:: test_string_of_arith_old_var;

    "spec_of_pointer_eq_eq"              >:: test_spec_of_pointer_eq_eq;
    "spec_of_pointer_eq_neq"             >:: test_spec_of_pointer_eq_neq;
    "spec_of_pointer_eq_gte"             >:: test_spec_of_pointer_eq_gte;
    "spec_of_pointer_eq_gt"              >:: test_spec_of_pointer_eq_gt;
    "spec_of_pointer_eq_lte"             >:: test_spec_of_pointer_eq_lte;
    "spec_of_pointer_eq_lt"              >:: test_spec_of_pointer_eq_lt;

    "loop_case_with_variant"             >:: test_loop_case_with_variant;
    "loop_case_with_variant_prime"       >:: test_loop_case_with_variant_prime;
    "loop_case_with_variant_old"         >:: test_loop_case_with_variant_old;
    "loop_case_with_variant_and_exit"    >:: test_loop_case_with_variant_and_exit;
    "loop_single_req_ens_conj_post"      >:: test_loop_single_req_ens_conj_post;
  ]

let () = run_test_tt_main suite
