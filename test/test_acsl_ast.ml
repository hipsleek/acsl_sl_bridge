open OUnit2
module A = Acsl_ast
open Acsl_ast_printer

let test_framework (expected : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let test_acsl_term_var _ctx =
  test_framework "a" (acsl_term (A.TVar "a"))

let test_acsl_term_int _ctx =
  test_framework "42" (acsl_term (A.TInt 42))

let test_acsl_term_deref _ctx =
  test_framework "*a" (acsl_term (A.TDeref (A.TVar "a")))

let test_acsl_term_old _ctx =
  test_framework "\\old(*a)" (acsl_term (A.TOld (A.TDeref (A.TVar "a"))))

let test_acsl_term_app_valid _ctx =
  test_framework "\\valid(a)" (acsl_term (A.TApp ("\\valid",[A.TVar "a"])))

let test_acsl_term_result _ctx =
  test_framework "\\result" (acsl_term A.TResult)

let test_acsl_term_arith_add _ctx =
  test_framework "a + 10" (acsl_term (A.TBinOp (A.Add, A.TVar "a", A.TInt 10)))

let test_acsl_term_arith_sub _ctx =
  test_framework "30 - i" (acsl_term (A.TBinOp (A.Sub, A.TInt 30, A.TVar "i")))

let test_acsl_pred_true_false _ctx =
  test_framework "\\true" (acsl_pred A.PTrue);
  test_framework "\\false" (acsl_pred A.PFalse)

let test_acsl_pred_rel_eq _ctx =
  let p = A.PRel (A.Eq, A.TVar "a", A.TVar "b") in
  test_framework "a == b" (acsl_pred p)

let test_acsl_pred_rel_lte _ctx =
  let p = A.PRel (A.Lte, A.TVar "x", A.TInt 5) in
  test_framework "x <= 5" (acsl_pred p)

let test_acsl_pred_app_valid _ctx =
  let p = A.PApp ("\\valid",[A.TVar "a"]) in
  test_framework "\\valid(a)" (acsl_pred p)

let test_acsl_pred_not _ctx =
  let p = A.PNot (A.PRel (A.Eq, A.TVar "a", A.TVar "b")) in
  test_framework "!(a == b)" (acsl_pred p)

let test_acsl_pred_and _ctx =
  let p =
    A.PAnd
      [ A.PRel (A.Lt, A.TVar "i", A.TInt 10)
      ; A.PRel (A.Gt, A.TVar "i", A.TInt 0)
      ]
  in
  test_framework "i < 10 && i > 0" (acsl_pred p)

let test_acsl_pred_or _ctx =
  let p =
    A.POr
      [ A.PRel (A.Eq, A.TVar "a", A.TVar "b")
      ; A.PRel (A.Neq, A.TVar "a", A.TVar "c")
      ]
  in
  test_framework "a == b || a != c" (acsl_pred p)

let test_acsl_pred_implies _ctx =
  let p =
    A.PImplies
      ( A.PRel (A.Lt, A.TVar "i", A.TInt 10)
      , A.PRel (A.Eq, A.TVar "i", A.TInt 10)
      )
  in
  test_framework "(i < 10) ==> (i == 10)" (acsl_pred p)

let test_acsl_pred_forall _ctx =
  let p = A.PForall ([("j",Some "integer")], A.PRel (A.Lte, A.TVar "j", A.TVar "i")) in
  test_framework "\\forall integer j; j <= i" (acsl_pred p)

let test_acsl_pred_exists _ctx =
  let p = A.PExists ([("k",None)], A.PRel (A.Eq, A.TVar "k", A.TInt 0)) in
  test_framework "\\exists k; k == 0" (acsl_pred p)


(* Replace the old multi-line string literals in the relevant expected values
   with this explicit "\n" ^ concatenation style. *)

let test_acsl_contract_flat _ctx =
  let requires =
    [ A.PApp ("\\valid", [ A.TVar "a" ])
    ; A.PApp ("\\valid", [ A.TVar "b" ])
    ]
  in
  let assigns = A.AList [ A.TDeref (A.TVar "a"); A.TDeref (A.TVar "b") ] in
  let behavior : A.behavior =
    {
      b_name = None;
      b_assumes = [];
      b_ensures =
        [
          A.PRel (A.Eq, A.TDeref (A.TVar "a"), A.TOld (A.TDeref (A.TVar "b")));
          A.PRel (A.Eq, A.TDeref (A.TVar "b"), A.TOld (A.TDeref (A.TVar "a")));
        ];
    }
  in
  let contract : A.contract = { requires; assigns; behaviors = [ behavior ] } in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework expected (acsl_contract contract)

let test_acsl_contract_cases _ctx =
  let requires =
    [ A.PApp ("\\valid", [ A.TVar "a" ])
    ; A.PApp ("\\valid", [ A.TVar "b" ])
    ]
  in
  let assigns = A.AList [ A.TDeref (A.TVar "a"); A.TDeref (A.TVar "b") ] in
  let b1 : A.behavior =
    {
      b_name = Some "alias";
      b_assumes = [ A.PRel (A.Eq, A.TVar "a", A.TVar "b") ];
      b_ensures =
        [ A.PRel (A.Eq, A.TDeref (A.TVar "a"), A.TOld (A.TDeref (A.TVar "a"))) ];
    }
  in
  let b2 : A.behavior =
    {
      b_name = Some "no_alias";
      b_assumes = [ A.PRel (A.Neq, A.TVar "a", A.TVar "b") ];
      b_ensures =
        [
          A.PRel (A.Eq, A.TDeref (A.TVar "a"), A.TOld (A.TDeref (A.TVar "b")));
          A.PRel (A.Eq, A.TDeref (A.TVar "b"), A.TOld (A.TDeref (A.TVar "a")));
        ];
    }
  in
  let contract : A.contract = { requires; assigns; behaviors = [ b1; b2 ] } in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  behavior alias:\n" ^
    "    assumes a == b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior no_alias:\n" ^
    "    assumes a != b;\n" ^
    "    ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework expected (acsl_contract contract)

let test_acsl_contract_with_result_ensures _ctx =
  let c : A.contract =
    {
      requires = [];
      assigns = A.ANothing;
      behaviors =
        [
          {
            b_name = None;
            b_assumes = [];
            b_ensures =
              [
                A.PRel
                  ( A.Eq
                  , A.TResult
                  , A.TBinOp (A.Add, A.TOld (A.TVar "a"), A.TInt 10)
                  );
              ];
          };
        ];
    }
  in
  let expected =
    "/*@\n" ^
    "  requires \\true;\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures \\result == \\old(a) + 10;\n" ^
    "*/"
  in
  test_framework expected (acsl_contract c)

let test_acsl_loop_contract_simple _ctx =
  let lc : A.loop_contract =
    {
      l_invariants = [ A.PRel (A.Lte, A.TVar "i", A.TInt 30) ];
      l_assigns = A.AList [ A.TVar "i" ];
      l_variant = Some (A.TBinOp (A.Sub, A.TInt 30, A.TVar "i"));
    }
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= 30;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
  in
  test_framework expected (acsl_loop_contract lc)

let test_acsl_loop_contract_with_two_assigns_and_variant _ctx =
  let lc : A.loop_contract =
    {
      l_invariants =
        [
          (* i <= 10 *)
          A.PRel (A.Lte, A.TVar "i", A.TInt 10);

          (* a == \at(a,LoopEntry) + (i-\at(i,LoopEntry)) *)
          A.PRel
            ( A.Eq,
              A.TVar "a",
              A.TBinOp
                ( A.Add,
                  A.TAt (A.TVar "a", A.LoopEntry),
                  A.TBinOp
                    ( A.Sub,
                      A.TVar "i",
                      A.TAt (A.TVar "i", A.LoopEntry) ) ) );
        ];
      l_assigns = A.AList [ A.TVar "a"; A.TVar "i" ];
      l_variant = Some (A.TBinOp (A.Sub, A.TInt 10, A.TVar "i"));
    }
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= 10;\n" ^
    "  loop invariant a == \\at(a, LoopEntry) + (i - \\at(i, LoopEntry));\n" ^
    "  loop assigns a, i;\n" ^
    "  loop variant 10 - i;\n" ^
    "*/"
  in
  test_framework expected (acsl_loop_contract lc)


let test_acsl_loop_contract_defaults _ctx =
  let lc : A.loop_contract =
    { l_invariants = []; l_assigns = A.ANothing; l_variant = None }
  in
  let expected =
    "/*@\n" ^
    "  loop invariant \\true;\n" ^
    "  loop assigns \\nothing;\n" ^
    "*/"
  in
  test_framework expected (acsl_loop_contract lc)

let test_acsl_assigns_nothing _ctx =
  test_framework "\\nothing" (acsl_assigns ANothing)

let test_acsl_assigns_list _ctx =
  test_framework "*a, *b"
    (acsl_assigns (AList [ TDeref (TVar "a"); TDeref (TVar "b") ]))

let test_acsl_loop_contract_with_forall_and_index _ctx =
  let lc : A.loop_contract =
    {
      l_invariants =
        [
          (* 0 <= i <= length *)
          A.PAnd
            [
              A.PRel (A.Lte, A.TInt 0, A.TVar "i");
              A.PRel (A.Lte, A.TVar "i", A.TVar "length");
            ];

          (* \forall size_t j; 0 <= j < i ==> array[j] != element *)
          A.PForall
            ( [ ("j", Some "size_t") ],
              A.PImplies
                ( A.PAnd
                    [
                      A.PRel (A.Lte, A.TInt 0, A.TVar "j");
                      A.PRel (A.Lt, A.TVar "j", A.TVar "i");
                    ],
                  A.PRel
                    ( A.Neq,
                      A.TIndex (A.TVar "array", A.TVar "j"),
                      A.TVar "element" ) ) );
        ];
      l_assigns = A.AList [ A.TVar "i" ];
      l_variant = Some (A.TBinOp (A.Sub, A.TVar "length", A.TVar "i"));
    }
  in
  let expected =
    "/*@\n" ^
    "  loop invariant 0 <= i && i <= length;\n" ^
    "  loop invariant \\forall size_t j; (0 <= j && j < i) ==> (array[j] != element);\n" ^
    "  loop assigns i;\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework expected (acsl_loop_contract lc)

let test_acsl_term_range_prints _ctx =
  let t : A.term = A.TRange (A.TInt 0, A.TInt 10) in
  let expected = "(0 .. 10)" in
  test_framework expected (acsl_term t)

let test_acsl_term_ptr_plus_range_prints _ctx =
  let t : A.term =
    A.TBinOp
      ( A.Add,
        A.TVar "array",
        A.TRange (A.TInt 0, A.TBinOp (A.Sub, A.TVar "length", A.TInt 1)) )
  in
  let expected = "array + (0 .. length - 1)" in
  test_framework expected (acsl_term t)

let test_acsl_pred_valid_plus_range_prints _ctx =
  let p : A.predicate =
    A.PApp
      ( "\\valid",
        [
          A.TBinOp
            ( A.Add,
              A.TVar "array",
              A.TRange (A.TInt 0, A.TBinOp (A.Sub, A.TVar "length", A.TInt 1)) );
        ] )
  in
  let expected = "\\valid(array + (0 .. length - 1))" in
  test_framework expected (acsl_pred p)

let test_acsl_contract_requires_valid_plus_range_prints _ctx =
  let c : A.contract =
    {
      A.requires =
        [
          A.PApp
            ( "\\valid",
              [
                A.TBinOp
                  ( A.Add,
                    A.TVar "array",
                    A.TRange
                      (A.TInt 0, A.TBinOp (A.Sub, A.TVar "length", A.TInt 1)) );
              ] );
        ];
      A.assigns = A.ANothing;
      A.behaviors = [];
    }
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(array + (0 .. length - 1));\n" ^
    "  assigns \\nothing;\n" ^
    "*/"
  in
  test_framework expected (acsl_contract c)


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


    "acsl_contract_flat" >:: test_acsl_contract_flat;
    "acsl_contract_cases" >:: test_acsl_contract_cases;
    "acsl_contract_with_result_ensures" >:: test_acsl_contract_with_result_ensures;

    "acsl_loop_contract_simple" >:: test_acsl_loop_contract_simple;
    "acsl_loop_contract_with_two_assigns_and_variant" >:: test_acsl_loop_contract_with_two_assigns_and_variant;
    "acsl_loop_contract_defaults" >:: test_acsl_loop_contract_defaults;

    "acsl_loop_contract_with_forall_and_index" >:: test_acsl_loop_contract_with_forall_and_index;

    "acsl_term_range_prints" >:: test_acsl_term_range_prints;
    "acsl_term_ptr_plus_range_prints" >:: test_acsl_term_ptr_plus_range_prints;
    "acsl_pred_valid_plus_range_prints" >:: test_acsl_pred_valid_plus_range_prints;
    "acsl_contract_requires_valid_plus_range_prints" >:: test_acsl_contract_requires_valid_plus_range_prints;
  ]

let () = run_test_tt_main suite
