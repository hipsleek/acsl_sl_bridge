open OUnit2
open Core
open Core_printer

let test_framework expected actual =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let mk_inout_param name : param = { name; mode = InOut }

let tvar_pre x= TVar (Pre, x)
let tvar_post x = TVar (Post, x)

let theap_pre p= THeap (Pre, p)
let theap_post p = THeap (Post, p)

let pred_valid p =
  PAtom (APred ("valid", [TPtr p]))

let pred_rel r t1 t2 =
  PAtom (ARel (r, t1, t2))

let mk_behavior ?name (clauses : clause list) : behavior =
  { b_name = name; clauses }

let mk_spec ?(kind=FunctionContract) (params : param list) (behaviors : behavior list) : spec =
  { kind; params; behaviors }



let test_core_string_of_term_heap_pre _ =
  test_framework "H(a)" (string_of_term (THeap (Pre, "a")))

let test_core_string_of_term_heap_post _ =
  test_framework "H'(a)" (string_of_term (THeap (Post, "a")))

let test_core_string_of_term_var_pre _ =
  test_framework "u" (string_of_term (TVar (Pre, "u")))

let test_core_string_of_term_var_post _ =
  test_framework "u" (string_of_term (TVar (Post, "u")))

let test_core_string_of_term_int _ =
  test_framework "42" (string_of_term (TInt 42))

let test_core_string_of_term_ptr _ =
  test_framework "p" (string_of_term (TPtr "p"))

let test_core_string_of_term_result _ =
  test_framework "\\result" (string_of_term TResult)

let test_core_string_of_term_app _ =
  let t = TApp ("f", [TPtr "a"; TInt 1; TArith (Add, TInt 2, TInt 3)]) in
  test_framework "f(a, 1, 2 + 3)" (string_of_term t)



let test_core_string_of_predicate_valid _ =
  test_framework "valid(a)" (string_of_predicate (pred_valid "a"))

let test_core_string_of_predicate_eq_heaps _ =
  let p = pred_rel Eq (theap_pre "a") (theap_post "b") in
  test_framework "H(a) == H'(b)" (string_of_predicate p)

let test_core_string_of_predicate_true_false _ =
  test_framework "true"(string_of_predicate PTrue);
  test_framework "false" (string_of_predicate PFalse)

let test_core_string_of_predicate_not _ =
  let p = PNot (pred_rel Eq (TPtr "a") (TPtr "b")) in
  test_framework "not (a == b)" (string_of_predicate p)

let test_core_string_of_predicate_or _ =
  let p =
    POr
      [
        pred_rel Lt (tvar_pre "i") (TInt 10);
        pred_rel Gt (tvar_pre "i") (TInt 20);
      ]
  in
  test_framework "i < 10 || i > 20" (string_of_predicate p)

let test_core_string_of_predicate_implies _ =
  let p =
    PImplies
      ( pred_rel Lt (tvar_pre "i") (TInt 10),
        pred_rel Eq (tvar_post "i") (TInt 10) )
  in
  test_framework "(i < 10) ==> (i == 10)" (string_of_predicate p)

let test_core_string_of_predicate_forall _ =
  let bs = [ { b_name = "j"; b_ty = Some "size_t" } ] in
  let body = pred_rel Lte (tvar_pre "j") (tvar_pre "i") in
  let p = PForall (bs, body) in
  test_framework "forall size_t j. j <= i" (string_of_predicate p)

let test_core_string_of_predicate_exists _ =
  let bs = [ { b_name = "k"; b_ty = None } ] in
  let body = pred_rel Eq (tvar_pre "k") (TInt 0) in
  let p = PExists (bs, body) in
  test_framework "exists k. k == 0" (string_of_predicate p)

let test_core_string_of_atom_apred _ =
  let p = PAtom (APred ("foo", [TPtr "x"; TInt 9])) in
  test_framework "foo(x, 9)" (string_of_predicate p)



let test_core_string_of_assignable_var _ =
  test_framework "i" (Core_printer.string_of_assignable (AsVar "i"))

let test_core_string_of_assignable_heap _ =
  test_framework "*a" (Core_printer.string_of_assignable (AsHeap "a"))

let test_core_string_of_assignable_range _ =
  let a = AsRange ("arr", TInt 0, TArith (Sub, TInt 10, tvar_pre "i")) in
  
  test_framework "arr+(0..10 - i)" (Core_printer.string_of_assignable a)

let test_core_string_of_assignable_term _ =
  let a = AsTerm (TApp ("loc", [TPtr "p"])) in
  test_framework "assign(loc(p))" (Core_printer.string_of_assignable a)



let test_core_string_of_spec_swap _ =
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in
  let bhv =
    mk_behavior
      [
        Assumes (pred_rel Neq (TPtr "a") (TPtr "b"));
        Requires (pred_valid "a");
        Requires (pred_valid "b");
        Ensures (pred_rel Eq (theap_post "a") (theap_pre "b"));
        Ensures (pred_rel Eq (theap_post "b") (theap_pre "a"));
        Assigns [ AsHeap "a"; AsHeap "b" ];
      ]
  in
  let spec_swap = mk_spec params [bhv] in
  let expected =
    "kind function\n" ^
    "params (a:inout, b:inout)\n" ^
    "assumes a != b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected (string_of_spec spec_swap)

let test_core_string_of_spec_empty _ =
  let bhv = mk_behavior [] in
  let spec_empty = mk_spec [] [bhv] in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "assigns {}"
  in
  test_framework expected (string_of_spec spec_empty)

let test_core_string_of_spec_with_variant _ =
  let bhv = mk_behavior [ Variant (TInt 42) ] in
  let spec = mk_spec [] [bhv] in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "assigns {}\n" ^
    "variant 42"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_simple_contract _ =
  let bhv =
    mk_behavior
      [
        Requires (pred_valid "a");
        Requires (pred_valid "b");
        Ensures (pred_rel Eq (theap_post "a") (theap_pre "b"));
        Ensures (pred_rel Eq (theap_post "b") (theap_pre "a"));
        Assigns [ AsHeap "a"; AsHeap "b" ];
      ]
  in
  let spec =
    mk_spec
      [ { name = "a"; mode = InOut }; { name = "b"; mode = InOut } ]
      [ bhv ]
  in
  let expected =
    "kind function\n" ^
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "assigns { *a, *b }"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_two_assigns_and_variant _ =
  let bhv =
    mk_behavior
      [
        Assumes (pred_rel Lte (tvar_post "i") (TInt 10));
        Ensures (pred_rel Eq (tvar_post "i") (TInt 10));
        Ensures (pred_rel Eq (tvar_post "a") (tvar_post "a"));
        Variant (TArith (Sub, TInt 10, tvar_post "i"));
      ]
  in
  let spec = mk_spec [] [bhv] in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes i <= 10\n" ^
    "requires true\n" ^
    "ensures i == 10 && a == a\n" ^
    "assigns {}\n" ^
    "variant 10 - i"
  in
  test_framework expected (string_of_spec spec)

let test_core_string_of_spec_result_ens _ =
  let bhv =
    mk_behavior
      [
        Ensures (pred_rel Eq TResult (TArith (Add, tvar_pre "a", TInt 10)));
      ]
  in
  let spec = mk_spec [] [bhv] in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures \\result == a + 10\n" ^
    "assigns {}"
  in
  test_framework expected (string_of_spec spec)


let test_core_behavior_name_print _ =
  let bhv = mk_behavior ~name:"case1" [] in
  let spec = mk_spec [] [bhv] in
  let expected =
    "kind function\n" ^
    "params ()\n" ^
    "behavior case1\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "assigns {}"
  in
  test_framework expected (string_of_spec spec)


let test_core_spec_kind_is_printed _ =
  let bhv = mk_behavior [] in
  let s1 = mk_spec ~kind:FunctionContract [] [bhv] in
  let s2 = mk_spec ~kind:LoopContract [] [bhv] in
  assert_bool
    "Expected FunctionContract and LoopContract to print differently"
    (string_of_spec s1 <> string_of_spec s2)

let suite =
  "core printer tests" >::: [
    "term_heap_pre">:: test_core_string_of_term_heap_pre;
    "term_heap_post">:: test_core_string_of_term_heap_post;
    "term_var_pre">:: test_core_string_of_term_var_pre;
    "term_var_post">:: test_core_string_of_term_var_post;
    "term_int">:: test_core_string_of_term_int;
    "term_ptr">:: test_core_string_of_term_ptr;
    "term_result">:: test_core_string_of_term_result;
    "term_app">:: test_core_string_of_term_app;

    "predicate_valid">:: test_core_string_of_predicate_valid;
    "predicate_eq_heaps">:: test_core_string_of_predicate_eq_heaps;
    "pred_true_false">:: test_core_string_of_predicate_true_false;
    "pred_not">:: test_core_string_of_predicate_not;
    "pred_or">:: test_core_string_of_predicate_or;
    "pred_implies">:: test_core_string_of_predicate_implies;
    "pred_forall">:: test_core_string_of_predicate_forall;
    "pred_exists">:: test_core_string_of_predicate_exists;
    "atom_apred">:: test_core_string_of_atom_apred;

    "assignable_var">:: test_core_string_of_assignable_var;
    "assignable_heap">:: test_core_string_of_assignable_heap;
    "assignable_range">:: test_core_string_of_assignable_range;
    "assignable_term">:: test_core_string_of_assignable_term;

    "spec_swap">:: test_core_string_of_spec_swap;
    "spec_empty">:: test_core_string_of_spec_empty;
    "spec_with_variant">:: test_core_string_of_spec_with_variant;
    "spec_simple_contract" >:: test_core_string_of_spec_simple_contract;
    "spec_two_assigns_and_variant" >:: test_core_string_of_spec_two_assigns_and_variant;
    "spec_result_ens">:: test_core_string_of_spec_result_ens;

    "behavior_name_print">:: test_core_behavior_name_print;
    "spec_kind_is_printed" >:: test_core_spec_kind_is_printed;
  ]

let () = run_test_tt_main suite
