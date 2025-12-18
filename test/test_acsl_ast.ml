open OUnit2
open Acsl_ast
open Acsl_ast_printer

let test_framework (expected : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let test_acsl_term_var _ctx =
  test_framework "a" (acsl_term (TVar "a"))

let test_acsl_term_int _ctx =
  test_framework "42" (acsl_term (TInt 42))

let test_acsl_term_deref _ctx =
  test_framework "*a" (acsl_term (TDeref (TVar "a")))

let test_acsl_term_old _ctx =
  test_framework "\\old(*a)" (acsl_term (TOld (TDeref (TVar "a"))))

let test_acsl_term_app_valid _ctx =
  test_framework "\\valid(a)" (acsl_term (TApp ("\\valid",[TVar "a"])))

let test_acsl_term_result _ctx =
  test_framework "\\result" (acsl_term TResult)

let test_acsl_term_arith_add _ctx =
  test_framework "a + 10" (acsl_term (TBinOp (Add,TVar "a",TInt 10)))

let test_acsl_term_arith_sub _ctx =
  test_framework "30 - i" (acsl_term (TBinOp (Sub,TInt 30,TVar "i")))

let test_acsl_pred_true_false _ctx =
  test_framework "\\true" (acsl_pred PTrue);
  test_framework "\\false" (acsl_pred PFalse)

let test_acsl_pred_rel_eq _ctx =
  let p = PRel (Eq,TVar "a",TVar "b") in
  test_framework "a == b" (acsl_pred p)

let test_acsl_pred_rel_lte _ctx =
  let p = PRel (Lte,TVar "x",TInt 5) in
  test_framework "x <= 5" (acsl_pred p)

let test_acsl_pred_app_valid _ctx =
  let p = PApp ("\\valid",[TVar "a"]) in
  test_framework "\\valid(a)" (acsl_pred p)

let test_acsl_pred_not _ctx =
  let p = PNot (PRel (Eq,TVar "a",TVar "b")) in
  test_framework "!(a == b)" (acsl_pred p)

let test_acsl_pred_and _ctx =
  let p = PAnd [PRel (Lt,TVar "i",TInt 10);PRel (Gt,TVar "i",TInt 0)] in
  test_framework "i < 10 && i > 0" (acsl_pred p)

let test_acsl_pred_or _ctx =
  let p = POr [PRel (Eq,TVar "a",TVar "b");PRel (Neq,TVar "a",TVar "c")] in
  test_framework "a == b || a != c" (acsl_pred p)

let test_acsl_pred_implies _ctx =
  let p = PImplies (PRel (Lt,TVar "i",TInt 10),PRel (Eq,TVar "i",TInt 10)) in
  test_framework "(i < 10) ==> (i == 10)" (acsl_pred p)

let test_acsl_pred_forall _ctx =
  let p = PForall ([("j",Some "integer")],PRel (Lte,TVar "j",TVar "i")) in
  test_framework "\\forall integer j; j <= i" (acsl_pred p)

let test_acsl_pred_exists _ctx =
  let p = PExists ([("k",None)],PRel (Eq,TVar "k",TInt 0)) in
  test_framework "\\exists k; k == 0" (acsl_pred p)

(* let test_acsl_contract_flat _ctx =
  let requires = [PApp ("\\valid",[TVar "a"]);PApp ("\\valid",[TVar "b"])] in
  let assigns = AList [TDeref (TVar "a");TDeref (TVar "b")] in
  let behavior =
    {
      b_name=None;
      b_assumes=[];
      b_ensures=
        [
          PRel (Eq,TDeref (TVar "a"),TOld (TDeref (TVar "b")));
          PRel (Eq,TDeref (TVar "b"),TOld (TDeref (TVar "a")));
        ];
    }
  in
  let contract = {requires;assigns;behaviors=[behavior]} in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns *a, *b;
  ensures *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework expected (acsl_contract contract)

let test_acsl_contract_cases _ctx =
  let requires = [PApp ("\\valid",[TVar "a"]);PApp ("\\valid",[TVar "b"])] in
  let assigns = AList [TDeref (TVar "a");TDeref (TVar "b")] in
  let b1 =
    {
      b_name=Some "alias";
      b_assumes=[PRel (Eq,TVar "a",TVar "b")];
      b_ensures=[PRel (Eq,TDeref (TVar "a"),TOld (TDeref (TVar "a")))];
    }
  in
  let b2 =
    {
      b_name=Some "no_alias";
      b_assumes=[PRel (Neq,TVar "a",TVar "b")];
      b_ensures=
        [
          PRel (Eq,TDeref (TVar "a"),TOld (TDeref (TVar "b")));
          PRel (Eq,TDeref (TVar "b"),TOld (TDeref (TVar "a")));
        ];
    }
  in
  let contract = {requires;assigns;behaviors=[b1;b2]} in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns *a, *b;
  behavior alias:
    assumes a == b;
    ensures *a == \\old(*a);
  behavior no_alias:
    assumes a != b;
    ensures *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework expected (acsl_contract contract)

let test_acsl_contract_with_result_ensures _ctx =
  let c =
    {
      requires=[];
      assigns=ANothing;
      behaviors=
        [
          {
            b_name=None;
            b_assumes=[];
            b_ensures=[PRel (Eq,TResult,TBinOp (Add,TOld (TVar "a"),TInt 10))];
          };
        ];
    }
  in
  let expected =
"/*@
  requires \\true;
  assigns \\nothing;
  ensures \\result == \\old(a) + 10;
*/"
  in
  test_framework expected (acsl_contract c)

let test_acsl_loop_contract_simple _ctx =
  let lc =
    {
      l_invariants=[PRel (Lte,TVar "i",TInt 30)];
      l_assigns=AList [TVar "i"];
      l_variant=Some (TBinOp (Sub,TInt 30,TVar "i"));
    }
  in
  let expected =
"/*@
  loop invariant i <= 30;
  loop assigns i;
  loop variant 30 - i;
*/"
  in
  test_framework expected (acsl_loop_contract lc)

let test_acsl_loop_contract_with_two_assigns_and_variant _ctx =
  let lc =
    {
      l_invariants=[PRel (Lte,TVar "i",TInt 10)];
      l_assigns=AList [TVar "a";TVar "i"];
      l_variant=Some (TBinOp (Sub,TInt 10,TVar "i"));
    }
  in
  let expected =
"/*@
  loop invariant i <= 10;
  loop assigns a, i;
  loop variant 10 - i;
*/"
  in
  test_framework expected (acsl_loop_contract lc)

let test_acsl_loop_contract_defaults _ctx =
  let lc = {l_invariants=[];l_assigns=ANothing;l_variant=None} in
  let expected =
"/*@
  loop invariant \\true;
  loop assigns \\nothing;
*/"
  in
  test_framework expected (acsl_loop_contract lc)

  *)

let test_acsl_assigns_nothing _ctx =
  test_framework "\\nothing" (acsl_assigns ANothing)

let test_acsl_assigns_list _ctx =
  test_framework "*a, *b" (acsl_assigns (AList [TDeref (TVar "a");TDeref (TVar "b")])) 

let suite =
  "acsl_ast" >::: [
    "acsl_term_var" >:: test_acsl_term_var;
    "acsl_term_int" >:: test_acsl_term_int;
    "acsl_term_deref" >:: test_acsl_term_deref;
    "acsl_term_old" >:: test_acsl_term_old;
    "acsl_term_app_valid" >:: test_acsl_term_app_valid;
    "acsl_term_result" >:: test_acsl_term_result;
    "acsl_term_arith_add" >:: test_acsl_term_arith_add;
    "acsl_term_arith_sub" >:: test_acsl_term_arith_sub;

    "acsl_pred_true_false" >:: test_acsl_pred_true_false;
    "acsl_pred_rel_eq" >:: test_acsl_pred_rel_eq;
    "acsl_pred_rel_lte" >:: test_acsl_pred_rel_lte;
    "acsl_pred_app_valid" >:: test_acsl_pred_app_valid;
    "acsl_pred_not" >:: test_acsl_pred_not;
    "acsl_pred_and" >:: test_acsl_pred_and;
    "acsl_pred_or" >:: test_acsl_pred_or;
    "acsl_pred_implies" >:: test_acsl_pred_implies;
    "acsl_pred_forall" >:: test_acsl_pred_forall;
    "acsl_pred_exists" >:: test_acsl_pred_exists;

    "acsl_assigns_nothing" >:: test_acsl_assigns_nothing;
    "acsl_assigns_list" >:: test_acsl_assigns_list;
(* 
    "acsl_contract_flat" >:: test_acsl_contract_flat;
    "acsl_contract_cases" >:: test_acsl_contract_cases;
    "acsl_contract_with_result_ensures" >:: test_acsl_contract_with_result_ensures;

    "acsl_loop_contract_simple" >:: test_acsl_loop_contract_simple;
    "acsl_loop_contract_with_two_assigns_and_variant" >:: test_acsl_loop_contract_with_two_assigns_and_variant;
    "acsl_loop_contract_defaults" >:: test_acsl_loop_contract_defaults; *)
  ]

let () = run_test_tt_main suite
