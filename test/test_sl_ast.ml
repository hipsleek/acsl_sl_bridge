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
  AHeapAtom (PointTo (p, t, v))

let ( * ) a b : assertion = ASep (a, b)

let pure (p : pure_atom) : assertion = APure p

let ( &&& ) a b : assertion = AAnd (a, b)

let eq e1 e2 : assertion = pure (PEq (e1, e2))
let neq e1 e2 : assertion = pure (PNeq (e1, e2))
let lt e1 e2 : assertion = pure (PLt (e1, e2))
let lte e1 e2 : assertion = pure (PLte (e1, e2))
let gte e1 e2 : assertion = pure (PGte (e1, e2))
let gt e1 e2 : assertion = pure (PGt (e1, e2))

(* ---------- Assertion printing tests ---------- *)

let test_string_of_spec_atom_int _ =
  let atom = pt "a" "int" "u" in
  test_framework "a->int*(u)" (string_of_assertion atom)

let test_string_of_spec_atom_char _ =
  let atom = pt "a" "char" "u" in
  test_framework "a->char*(u)" (string_of_assertion atom)

let test_string_of_spec_formula _ =
  let h_pre = (pt "a" "int" "u") * (pt "b" "int" "v") in
  test_framework "a->int*(u) ** b->int*(v)" (string_of_assertion h_pre)

let test_string_of_spec_swap _ =
  let pre  = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let post = (pt "a" "int" "v") * (pt "b" "int" "u") in
  let spec_swap : base_spec = { pre; post } in
  let expected =
    "req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);"
  in
  test_framework expected (string_of_base_spec spec_swap)

(* ---------- Sugar tests ---------- *)

let test_string_of_spec_sugar_prime_swap _ =
  let spec =
    Ens { ret = None; post = ASugarPrime [ ("a", "b"); ("b", "a") ] }
  in
  test_framework "ens (*a)'==(*b) && (*b)'==(*a);" (string_of_spec spec)

let test_string_of_spec_sugar_old_swap _ =
  let spec =
    Ens { ret = None; post = ASugarOld [ ("a", "b"); ("b", "a") ] }
  in
  test_framework "ens (*a)==\\old(*b) && (*b)==\\old(*a);" (string_of_spec spec)

(* ---------- Pure / arith printing tests ---------- *)

let test_string_of_conditional_eq_ptrs _ =
  let p = PEq (AVar "a", AVar "b") in
  test_framework "a==b" (string_of_pure_atom p)

let test_string_of_conditional_lt_int _ =
  let p = PLt (AVar "i", AInt 30) in
  test_framework "i<30" (string_of_pure_atom p)

let test_string_of_arith_sub_in_conditional _ =
  let p = PEq (ASub (AInt 30, AVar "i"), AInt 0) in
  test_framework "30-i==0" (string_of_pure_atom p)

let test_string_of_arith_post_var _ =
  test_framework "i'" (string_of_arith (APostVar "i"))

let test_string_of_arith_old_var _ =
  test_framework "\\old(i)" (string_of_arith (AOld (AVar "i")))

(* ---------- Case printing tests ---------- *)

let test_spec_of_pointer_eq_eq _ =
  let heap_a_u = pt "a" "int" "u" in
  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let spec = Case [ case_one ] in
  test_framework "case {a==b => req a->int*(u); ens a->int*(u);};" (string_of_spec spec)

let test_spec_of_pointer_eq_neq _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let case_two : case_spec =
    { test = neq (AVar "a") (AVar "b"); term = None; pre = heap_a_u_b_v; post = heap_a_v_b_u }
  in

  let spec = Case [ case_one; case_two ] in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a!=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_lte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let case_two : case_spec =
    { test = lte (AVar "a") (AVar "b"); term = None; pre = heap_a_u_b_v; post = heap_a_v_b_u }
  in

  let spec = Case [ case_one; case_two ] in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_lt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let case_two : case_spec =
    { test = lt (AVar "a") (AVar "b"); term = None; pre = heap_a_u_b_v; post = heap_a_v_b_u }
  in

  let spec = Case [ case_one; case_two ] in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a<b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_gte _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let case_two : case_spec =
    { test = gte (AVar "a") (AVar "b"); term = None; pre = heap_a_u_b_v; post = heap_a_v_b_u }
  in

  let spec = Case [ case_one; case_two ] in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>=b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

let test_spec_of_pointer_eq_gt _ =
  let heap_a_u = pt "a" "int" "u" in
  let heap_a_u_b_v = (pt "a" "int" "u") * (pt "b" "int" "v") in
  let heap_a_v_b_u = (pt "a" "int" "v") * (pt "b" "int" "u") in

  let case_one : case_spec =
    { test = eq (AVar "a") (AVar "b"); term = None; pre = heap_a_u; post = heap_a_u }
  in
  let case_two : case_spec =
    { test = gt (AVar "a") (AVar "b"); term = None; pre = heap_a_u_b_v; post = heap_a_v_b_u }
  in

  let spec = Case [ case_one; case_two ] in
  let expected =
    "case {a==b => req a->int*(u); ens a->int*(u); \
     a>b => req a->int*(u) ** b->int*(v); ens a->int*(v) ** b->int*(u);};"
  in
  test_framework expected (string_of_spec spec)

(* ---------- Loop/variant style cases ---------- *)

let test_loop_case_with_variant _ =
  let heap_i_u = pt "i" "int" "u" in
  let case_loop : case_spec =
    {
      test = lt (AVar "i") (AInt 30);
      term = Some (Term (ASub (AInt 30, AVar "i")));
      pre  = heap_i_u;
      post = eq (APostVar "i") (AInt 30);
    }
  in
  test_framework "case {i<30 => req Term[30-i]; ens i'==30;};" (string_of_spec (Case [case_loop]))

let test_loop_case_with_variant_prime _ =
  let heap_i_u = pt "i" "int" "u" in
  let case_loop : case_spec =
    {
      test = lt (AVar "i") (AInt 30);
      term = Some (Term (ASub (AInt 30, AVar "i")));
      pre  = heap_i_u;
      post = eq (APostVar "i") (AVar "i");
    }
  in
  test_framework "case {i<30 => req Term[30-i]; ens i'==i;};" (string_of_spec (Case [case_loop]))

let test_loop_case_with_variant_old _ =
  let heap_i_u = pt "i" "int" "u" in
  let case_loop : case_spec =
    {
      test = lt (AVar "i") (AInt 30);
      term = Some (Term (ASub (AInt 30, AVar "i")));
      pre  = heap_i_u;
      post = eq (AVar "i") (AOld (AVar "i"));
    }
  in
  test_framework "case {i<30 => req Term[30-i]; ens i==\\old(i);};" (string_of_spec (Case [case_loop]))

let test_loop_case_with_variant_and_exit _ =
  let heap_i_u = pt "i" "int" "u" in

  let case1 : case_spec =
    {
      test = lt (AVar "i") (AInt 30);
      term = Some (Term (ASub (AInt 30, AVar "i")));
      pre  = heap_i_u;
      post = eq (APostVar "i") (AInt 30);
    }
  in
  let case2 : case_spec =
    {
      test = gte (AVar "i") (AInt 30);
      term = Some TermNone;
      pre  = heap_i_u;
      post = eq (APostVar "i") (AVar "i");
    }
  in
  let expected =
    "case {i<30 => req Term[30-i]; ens i'==30; \
     i>=30 => req Term[]; ens i'==i;};"
  in
  test_framework expected (string_of_spec (Case [case1; case2]))

let test_loop_single_req_ens_conj_post _ =
  let dummy_pre = pt "_" "int" "_" in

  let post_conj =
    eq (APostVar "i") (AInt 10)
    &&&
    eq
      (APostVar "a")
      (AAdd (AVar "a", ASub (APostVar "i", AVar "i")))
  in

  let loop_case : case_spec =
    {
      test = lte (AVar "i") (AInt 10);
      term = Some (Term (ASub (AInt 10, AVar "i")));
      pre  = dummy_pre;
      post = post_conj;
    }
  in

  let expected =
    "case {i<=10 => req Term[10-i]; ens i'==10 && a'==a+i'-i;};"
  in
  test_framework expected (string_of_spec (Case [loop_case]))

(* ---------- ens[r] binder ---------- *)

let test_ens_result_binder _ =
  let post = eq AResult (AAdd (AVar "a", AInt 10)) in
  let spec = Ens { ret = Some "r"; post } in
  test_framework "ens[r] r==a+10;" (string_of_spec spec)

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

    "ens_result_binder"                  >:: test_ens_result_binder;
  ]

let () = run_test_tt_main suite
