open OUnit2
open Core_printer

module C = Core

let test_framework expected actual =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let mk_inout_param (name : C.var) : C.param = { C.name; mode = C.InOut }

let tvar_pre x  = C.TVar (C.Pre, x)
let tvar_post x = C.TVar (C.Post, x)

let theap_pre p  = C.THeap (C.Pre, p)
let theap_post p = C.THeap (C.Post, p)

let pred_valid p =
  C.PAtom (C.APred ("valid", [ C.TPtr p ]))

let pred_rel r t1 t2 =
  C.PAtom (C.ARel (r, t1, t2))

let mk_behavior ?name (clauses : C.clause list) : C.behavior =
  { C.b_name = name; clauses }

let mk_spec ?(kind=C.FunctionContract) (params : C.param list) (behaviors : C.behavior list) : C.spec =
  { C.kind = kind; params; behaviors }



let test_core_string_of_term_heap_pre _ =
  test_framework "H(a)" (string_of_term (C.THeap (C.Pre, "a")))

let test_core_string_of_term_heap_post _ =
  test_framework "H'(a)" (string_of_term (C.THeap (C.Post, "a")))

let test_core_string_of_term_var_pre _ =
  test_framework "u" (string_of_term (C.TVar (C.Pre, "u")))

let test_core_string_of_term_var_post _ =
  test_framework "u'" (string_of_term (C.TVar (C.Post, "u")))

let test_core_string_of_term_int _ =
  test_framework "42" (string_of_term (C.TInt 42))

let test_core_string_of_term_ptr _ =
  test_framework "p" (string_of_term (C.TPtr "p"))

let test_core_string_of_term_result _ =
  test_framework "\\result" (string_of_term C.TResult)

let test_core_string_of_term_app _ =
  let t =
    C.TApp ("f", [ C.TPtr "a"; C.TInt 1; C.TArith (C.Add, C.TInt 2, C.TInt 3) ])
  in
  test_framework "f(a, 1, 2 + 3)" (string_of_term t)



let test_core_string_of_predicate_valid _ =
  test_framework "valid(a)" (string_of_predicate (pred_valid "a"))

let test_core_string_of_predicate_eq_heaps _ =
  let p = pred_rel C.Eq (theap_pre "a") (theap_post "b") in
  test_framework "H(a) == H'(b)" (string_of_predicate p)

let test_core_string_of_predicate_true_false _ =
  test_framework "true" (string_of_predicate C.PTrue);
  test_framework "false" (string_of_predicate C.PFalse)

let test_core_string_of_predicate_not _ =
  let p = C.PNot (pred_rel C.Eq (C.TPtr "a") (C.TPtr "b")) in
  test_framework "not (a == b)" (string_of_predicate p)let test_core_string_of_predicate_or _ =
  let p =
    C.POr
      [
        pred_rel C.Lt (tvar_pre "i") (C.TInt 10);
        pred_rel C.Gt (tvar_pre "i") (C.TInt 20);
      ]
  in
  test_framework "i < 10 || i > 20" (string_of_predicate p)

let test_core_string_of_predicate_implies _ =
  let p =
    C.PImplies
      ( pred_rel C.Lt (tvar_pre "i") (C.TInt 10),
        pred_rel C.Eq (tvar_post "i") (C.TInt 10) )
  in
  test_framework "(i < 10) ==> (i' == 10)" (string_of_predicate p)

let test_core_string_of_predicate_forall _ =
  let bs = [ { C.b_name = "j"; b_ty = Some "size_t" } ] in
  let body = pred_rel C.Lte (tvar_pre "j") (tvar_pre "i") in
  let p = C.PForall (bs, body) in
  test_framework "forall size_t j. j <= i" (string_of_predicate p)

let test_core_string_of_predicate_exists _ =
  let bs = [ { C.b_name = "k"; b_ty = None } ] in
  let body = pred_rel C.Eq (tvar_pre "k") (C.TInt 0) in
  let p = C.PExists (bs, body) in
  test_framework "exists k. k == 0" (string_of_predicate p)

let test_core_string_of_atom_apred _ =
  let p = C.PAtom (C.APred ("foo", [ C.TPtr "x"; C.TInt 9 ])) in
  test_framework "foo(x, 9)" (string_of_predicate p)



let test_core_string_of_assignable_var _ =
  test_framework "i" (Core_printer.string_of_assignable (C.AsVar "i"))

let test_core_string_of_assignable_heap _ =
  test_framework "*a" (Core_printer.string_of_assignable (C.AsHeap "a"))

let test_core_string_of_assignable_range _ =
  let a = C.AsRange ("arr", C.TInt 0, C.TArith (C.Sub, C.TInt 10, tvar_pre "i")) in
  test_framework "arr+(0..10 - i)" (Core_printer.string_of_assignable a)

let test_core_string_of_assignable_term _ =
  let a = C.AsTerm (C.TApp ("loc", [ C.TPtr "p" ])) in
  test_framework "assign(loc(p))" (Core_printer.string_of_assignable a)



let test_core_string_of_spec_swap _ =
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in
  let bhv =
    mk_behavior
      [
        C.Assumes (pred_rel C.Neq (C.TPtr "a") (C.TPtr "b"));
        C.Requires (pred_valid "a");
        C.Requires (pred_valid "b");
        C.Ensures (pred_rel C.Eq (theap_post "a") (theap_pre "b"));
        C.Ensures (pred_rel C.Eq (theap_post "b") (theap_pre "a"));
        C.Assigns [ C.AsHeap "a"; C.AsHeap "b" ];
      ]
  in
  let spec_swap = mk_spec params [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params(a:inout, b:inout)\n" ^
    "behavior <anon>:\n" ^
    "  assumes a != b\n" ^
    "  requires valid(a)\n" ^
    "  requires valid(b)\n" ^
    "  ensures H'(a) == H(b)\n" ^
    "  ensures H'(b) == H(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected (string_of_spec spec_swap)

let test_core_string_of_spec_empty _ =
  let bhv = mk_behavior [] in
  let spec_empty = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:"
  in
  test_framework expected (string_of_spec spec_empty)

let test_core_string_of_spec_with_variant _ =
  let bhv = mk_behavior [ C.Variant (C.TInt 42) ] in
  let spec = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  variant 42"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_simple_contract _ =
  let bhv =
    mk_behavior
      [
        C.Requires (pred_valid "a");
        C.Requires (pred_valid "b");
        C.Ensures (pred_rel C.Eq (theap_post "a") (theap_pre "b"));
        C.Ensures (pred_rel C.Eq (theap_post "b") (theap_pre "a"));
        C.Assigns [ C.AsHeap "a"; C.AsHeap "b" ];
      ]
  in
  let spec =
    mk_spec
      [ { C.name = "a"; mode = C.InOut }; { C.name = "b"; mode = C.InOut } ]
      [ bhv ]
  in
  let expected =
    "kind(function)\n" ^
    "params(a:inout, b:inout)\n" ^
    "behavior <anon>:\n" ^
    "  requires valid(a)\n" ^
    "  requires valid(b)\n" ^
    "  ensures H'(a) == H(b)\n" ^
    "  ensures H'(b) == H(a)\n" ^
    "  assigns { *a, *b }"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_two_assigns_and_variant _ =
  let bhv =
    mk_behavior
      [
        C.Assumes (pred_rel C.Lte (tvar_post "i") (C.TInt 10));
        C.Ensures (pred_rel C.Eq (tvar_post "i") (C.TInt 10));
        C.Ensures (pred_rel C.Eq (tvar_post "a") (tvar_post "a"));
        C.Variant (C.TArith (C.Sub, C.TInt 10, tvar_post "i"));
      ]
  in
  let spec = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes i' <= 10\n" ^
    "  ensures i' == 10\n" ^
    "  ensures a' == a'\n" ^
    "  variant 10 - i'"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_result_ens _ =
  let bhv =
    mk_behavior
      [
        C.Ensures (pred_rel C.Eq C.TResult (C.TArith (C.Add, tvar_pre "a", C.TInt 10)));
      ]
  in
  let spec = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  ensures \\result == a + 10"
  in
  test_framework expected (string_of_spec spec)

let test_core_behavior_name_print _ =
  let bhv = mk_behavior ~name:"case1" [] in
  let spec = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior case1:"
  in
  test_framework expected (string_of_spec spec)

let test_core_spec_kind_is_printed _ =
  let bhv = mk_behavior [] in
  let s1 = mk_spec ~kind:C.FunctionContract [] [ bhv ] in
  let s2 = mk_spec ~kind:C.LoopContract [] [ bhv ] in
  assert_bool
    "Expected FunctionContract and LoopContract to print differently"
    (string_of_spec s1 <> string_of_spec s2)

let test_core_string_of_spec_forall_index_loop_like _ =
  let bhv =
    mk_behavior
      [
        (* assumes 0 <= i && i <= length *)
        C.Assumes
          (C.PAnd
             [
               pred_rel C.Lte (C.TInt 0) (tvar_post "i");
               pred_rel C.Lte (tvar_post "i") (tvar_post "length");
             ]);

        (* assumes forall size_t j. (0<=j && j<i) ==> array[j] != element *)
        C.Assumes
          (C.PForall
             ( [ { C.b_name = "j"; b_ty = Some "size_t" } ],
               C.PImplies
                 ( C.PAnd
                     [
                       pred_rel C.Lte (C.TInt 0) (tvar_post "j");
                       pred_rel C.Lt (tvar_post "j") (tvar_post "i");
                     ],
                   C.PAtom
                     (C.ARel
                        ( C.Neq,
                          (* FIX: array is a term now, not a string *)
                          C.TIndex (C.Post, tvar_post "array", tvar_post "j"),
                          tvar_post "element" )) ) ));

        (* variant length - i *)
        C.Variant (C.TArith (C.Sub, tvar_post "length", tvar_post "i"));
      ]
  in
  let spec = mk_spec [] [ bhv ] in
  let expected =
    "kind(function)\n" ^
    "params()\n" ^
    "behavior <anon>:\n" ^
    "  assumes 0 <= i' && i' <= length'\n" ^
    "  assumes forall size_t j. (0 <= j' && j' < i') ==> (array'[j'] != element')\n" ^
    "  variant length' - i'"
  in
  test_framework expected (string_of_spec spec)


let suite =
  "core printer tests" >::: [
    "term_heap_pre" >:: test_core_string_of_term_heap_pre;
    "term_heap_post" >:: test_core_string_of_term_heap_post;
    "term_var_pre" >:: test_core_string_of_term_var_pre;
    "term_var_post" >:: test_core_string_of_term_var_post;
    "term_int" >:: test_core_string_of_term_int;
    "term_ptr" >:: test_core_string_of_term_ptr;
    "term_result" >:: test_core_string_of_term_result;
    "term_app" >:: test_core_string_of_term_app;

    "predicate_valid" >:: test_core_string_of_predicate_valid;
    "predicate_eq_heaps" >:: test_core_string_of_predicate_eq_heaps;
    "pred_true_false" >:: test_core_string_of_predicate_true_false;
    "pred_not" >:: test_core_string_of_predicate_not;
    "pred_or" >:: test_core_string_of_predicate_or;
    "pred_implies" >:: test_core_string_of_predicate_implies;
    "pred_forall" >:: test_core_string_of_predicate_forall;
    "pred_exists" >:: test_core_string_of_predicate_exists;
    "atom_apred" >:: test_core_string_of_atom_apred;

    "assignable_var" >:: test_core_string_of_assignable_var;
    "assignable_heap" >:: test_core_string_of_assignable_heap;
    "assignable_range" >:: test_core_string_of_assignable_range;
    "assignable_term" >:: test_core_string_of_assignable_term;

    "spec_swap" >:: test_core_string_of_spec_swap;
    "spec_empty" >:: test_core_string_of_spec_empty;
    "spec_with_variant" >:: test_core_string_of_spec_with_variant;
    "spec_simple_contract" >:: test_core_string_of_spec_simple_contract;
    "spec_two_assigns_and_variant" >:: test_core_string_of_spec_two_assigns_and_variant;
    "spec_result_ens" >:: test_core_string_of_spec_result_ens;

    "behavior_name_print" >:: test_core_behavior_name_print;
    "spec_kind_is_printed" >:: test_core_spec_kind_is_printed;

    "test_core_string_of_spec_forall_index_loop_like" >:: test_core_string_of_spec_forall_index_loop_like;
  ]

let () = run_test_tt_main suite
