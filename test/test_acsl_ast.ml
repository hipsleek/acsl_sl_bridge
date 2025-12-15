open OUnit2
open Acsl_ast
open Acsl_ast_printer

let test_acsl_term_var _ctx =
  let actual = acsl_term (TVar "a") in
  let expected = "a" in
  assert_equal expected actual

let test_acsl_term_int _ctx =
  let actual = acsl_term (TInt 42) in
  let expected = "42" in
  assert_equal expected actual

let test_acsl_term_deref _ctx =
  let actual = acsl_term (TDeref (TVar "a")) in
  let expected = "*a" in
  assert_equal expected actual

let test_acsl_term_old _ctx =
  let actual = acsl_term (TOld (TDeref (TVar "a"))) in
  let expected = "\\old(*a)" in
  assert_equal expected actual

let test_acsl_term_valid _ctx =
  let actual = acsl_term (TApp ("\\valid", [ TVar "a" ])) in
  let expected = "\\valid(a)" in
  assert_equal expected actual

let test_acsl_term_binop_eq _ctx =
  let actual = acsl_term (TBinOp (Eq, TVar "a", TVar "b")) in
  let expected = "a == b" in
  assert_equal expected actual

let test_acsl_term_binop_lte _ctx =
  let actual = acsl_term (TBinOp (Lte, TVar "x", TInt 5)) in
  let expected = "x <= 5" in
  assert_equal expected actual

let test_acsl_contract_flat _ctx =
  let assigns = [ TDeref (TVar "a"); TDeref (TVar "b") ] in
  let behavior =
    {
      b_name = None;
      b_assumes = [];
      b_requires =
        [
          TApp ("\\valid", [ TVar "a" ]);
          TApp ("\\valid", [ TVar "b" ]);
        ];
      b_ensures =
        [
          TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "b")));
          TBinOp (Eq, TDeref (TVar "b"), TOld (TDeref (TVar "a")));
        ];
    }
  in
  let contract = { assigns; behaviors = [ behavior ] } in
  let actual = acsl_contract contract in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_equal expected actual

let test_acsl_contract_cases _ctx =
  let assigns = [ TDeref (TVar "a"); TDeref (TVar "b") ] in

  let b1 =
    {
      b_name = Some "alias";
      b_assumes = [ TBinOp (Eq, TVar "a", TVar "b") ];
      b_requires =
        [ TApp ("\\valid", [ TVar "a" ]); TApp ("\\valid", [ TVar "b" ]) ];
      b_ensures = [ TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "a"))) ];
    }
  in

  let b2 =
    {
      b_name = Some "no_alias";
      b_assumes = [ TBinOp (Neq, TVar "a", TVar "b") ];
      b_requires =
        [ TApp ("\\valid", [ TVar "a" ]); TApp ("\\valid", [ TVar "b" ]) ];
      b_ensures =
        [
          TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "b")));
          TBinOp (Eq, TDeref (TVar "b"), TOld (TDeref (TVar "a")));
        ];
    }
  in

  let contract = { assigns; behaviors = [ b1; b2 ] } in
  let actual = acsl_contract contract in
  let expected =
"/*@
  assigns  *a, *b;
  behavior alias:
    assumes a == b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*a);
  behavior no_alias:
    assumes a != b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_equal expected actual

let test_acsl_loop_contract_simple _ctx =
  let lc : loop_contract =
    {
      l_invariants = [ TBinOp (Lte, TVar "i", TInt 30) ];
      l_assigns    = [ TVar "i" ];
      l_variant    = Some (TBinOp (Sub, TInt 30, TVar "i"));
    }
  in
  let actual = acsl_loop_contract lc in
  let expected =
"/*@
  loop invariant i <= 30;
  loop assigns i;
  loop variant 30 - i;
*/"
  in
  assert_equal expected actual

let test_acsl_loop_contract_with_two_assigns_and_variant _ctx =
  let lc : loop_contract =
    {
      l_invariants =
        [ TBinOp (Lte, TVar "i", TInt 10) ];
      l_assigns =
        [ TVar "a"; TVar "i" ];
      l_variant =
        Some (TBinOp (Sub, TInt 10, TVar "i"));
    }
  in
  let actual = acsl_loop_contract lc in
  let expected =
"/*@
  loop invariant i <= 10;
  loop assigns a, i;
  loop variant 10 - i;
*/"
  in
  assert_equal expected actual


let suite =
  "acsl_ast" >::: [
    "acsl_term_var"              >:: test_acsl_term_var;
    "acsl_term_int"              >:: test_acsl_term_int;
    "acsl_term_deref"            >:: test_acsl_term_deref;
    "acsl_term_old"              >:: test_acsl_term_old;
    "acsl_term_valid"            >:: test_acsl_term_valid;
    "acsl_term_binop_eq"         >:: test_acsl_term_binop_eq;
    "acsl_term_binop_lte"        >:: test_acsl_term_binop_lte;

    "acsl_contract_flat"         >:: test_acsl_contract_flat;
    "acsl_contract_cases"        >:: test_acsl_contract_cases;

    "acsl_loop_contract_simple"  >:: test_acsl_loop_contract_simple;
    "acsl_loop_contract_with_two_assigns_and_variant" >:: test_acsl_loop_contract_with_two_assigns_and_variant
  ]

let () = run_test_tt_main suite
