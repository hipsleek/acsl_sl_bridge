(* test/test_core_to_acsl.ml *)
open OUnit2

module C = Core
module A = Acsl_ast

let test_framework (expected : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

(* ---------- Builders for the *new* Core AST ---------- *)

let mk_inout_param (name : string) : C.param =
  { C.name; mode = C.InOut }

let mk_valid (p : string) : C.predicate =
  C.PAtom (C.APred ("valid", [ C.TPtr p ]))

let mk_heap_pre (p : string) : C.term =
  C.THeap (C.Pre, p)

let mk_heap_post (p : string) : C.term =
  C.THeap (C.Post, p)

let mk_ptr (p : string) : C.term =
  C.TPtr p

let mk_var_pre (x : string) : C.term =
  C.TVar (C.Pre, x)

let mk_var_post (x : string) : C.term =
  C.TVar (C.Post, x)

let mk_int (n : int) : C.term =
  C.TInt n

let mk_result : C.term =
  C.TResult

let mk_sub (t1 : C.term) (t2 : C.term) : C.term =
  C.TArith (C.Sub, t1, t2)

let mk_add (t1 : C.term) (t2 : C.term) : C.term =
  C.TArith (C.Add, t1, t2)

let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
  C.PAtom (C.ARel (r, t1, t2))

let mk_eq  t1 t2 = mk_rel C.Eq  t1 t2
let mk_neq t1 t2 = mk_rel C.Neq t1 t2
let mk_lt  t1 t2 = mk_rel C.Lt  t1 t2
let mk_lte t1 t2 = mk_rel C.Lte t1 t2
let mk_gte t1 t2 = mk_rel C.Gte t1 t2

let mk_assigns_heaps (ptrs : string list) : C.assignable list =
  ptrs |> List.map (fun p -> C.AsHeap p)

let mk_basic_function_spec (ptrs : string list) (ens : C.predicate list) : C.spec =
  let params = List.map mk_inout_param ptrs in
  let requires =
    match ptrs with
    | [] -> C.PTrue
    | _  -> C.PAnd (List.map mk_valid ptrs)
  in
  let assigns = mk_assigns_heaps ptrs in
  let behavior : C.behavior =
    {
      C.b_name = None;
      clauses =
        [
          C.Assumes C.PTrue;
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures (C.PAnd ens);
        ];
    }
  in
  { C.kind = C.FunctionContract; params; behaviors = [ behavior ] }

(* ---------- Unit tests (expected OUTPUTS unchanged) ---------- *)

let test_core_to_acsl_swap _ctx =
  let ptrs = [ "a"; "b" ] in
  let ens =
    [
      mk_eq (mk_heap_post "a") (mk_heap_pre "b");
      mk_eq (mk_heap_post "b") (mk_heap_pre "a");
    ]
  in
  let core_spec = mk_basic_function_spec ptrs ens in
  let actual    = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns *a, *b;
  ensures *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework expected actual

let test_core_to_acsl_no_swap _ctx =
  let ptrs = [ "a"; "b" ] in
  let ens =
    [
      mk_eq (mk_heap_post "a") (mk_heap_pre "a");
      mk_eq (mk_heap_post "b") (mk_heap_pre "b");
    ]
  in
  let core_spec = mk_basic_function_spec ptrs ens in
  let actual    = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns *a, *b;
  ensures *a == \\old(*a) && *b == \\old(*b);
*/"
  in
  test_framework expected actual

let test_core_to_acsl_triple_swap _ctx =
  let ptrs = [ "a"; "b"; "c" ] in
  let ens =
    [
      mk_eq (mk_heap_post "a") (mk_heap_pre "c");
      mk_eq (mk_heap_post "b") (mk_heap_pre "a");
      mk_eq (mk_heap_post "c") (mk_heap_pre "b");
    ]
  in
  let core_spec = mk_basic_function_spec ptrs ens in
  let actual    = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b) && \\valid(c);
  assigns *a, *b, *c;
  ensures *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  test_framework expected actual

let test_core_to_acsl_case_behaviors _ctx =
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in

  let requires = C.PAnd [ mk_valid "a"; mk_valid "b" ] in
  let assigns  = mk_assigns_heaps [ "a"; "b" ] in

  let b1 : C.behavior =
    {
      b_name = Some "case1";
      clauses =
        [
          C.Assumes (mk_eq (mk_ptr "a") (mk_ptr "b"));
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures (mk_eq (mk_heap_post "a") (mk_heap_pre "a"));
        ];
    }
  in

  let b2 : C.behavior =
    {
      b_name = Some "case2";
      clauses =
        [
          C.Assumes (mk_neq (mk_ptr "a") (mk_ptr "b"));
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures
            (C.PAnd
               [
                 mk_eq (mk_heap_post "a") (mk_heap_pre "b");
                 mk_eq (mk_heap_post "b") (mk_heap_pre "a");
               ]);
        ];
    }
  in

  let core_spec : C.spec =
    {
      kind = C.FunctionContract;
      params;
      behaviors = [ b1; b2 ];
    }
  in

  let actual    = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns *a, *b;
  behavior case1:
    assumes a == b;
    ensures *a == \\old(*a);
  behavior case2:
    assumes a != b;
    ensures *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  test_framework expected actual

let test_core_to_acsl_loop_simple _ctx =
  let core_spec : C.spec =
    {
      kind = C.LoopContract;
      params = [];
      behaviors =
        [
          {
            b_name = None;
            clauses =
              [
                C.Assumes (mk_lt (mk_var_post "i") (mk_int 30));
                C.Assigns [ C.AsVar "i" ];
                C.Variant (mk_sub (mk_int 30) (mk_var_post "i"));
              ];
          };
          {
            b_name = None;
            clauses =
              [
                C.Assumes (mk_gte (mk_var_post "i") (mk_int 30));
              ];
          };
        ];
    }
  in

  let actual    = Core_to_acsl.spec_to_acsl core_spec in

  let expected =
"/*@
  loop invariant i < 30;
  loop assigns i;
  loop variant 30 - i;
*/"
  in
  test_framework expected actual

let test_core_to_acsl_loop_term_and_effects _ctx =
  let core_spec : C.spec =
    {
      kind = C.LoopContract;
      params = [];
      behaviors =
        [
          {
            b_name = None;
            clauses =
              [
                C.Assumes (mk_lte (mk_var_post "i") (mk_int 10));
                C.Assigns [ C.AsVar "a"; C.AsVar "i" ];
                C.Variant (mk_sub (mk_int 10) (mk_var_post "i"));
                (* ensures exist in Core but are ignored by loop printing in expected output *)
                C.Ensures
                  (C.PAnd
                     [
                       mk_eq (mk_var_post "i") (mk_int 10);
                       mk_eq (mk_var_post "a") (mk_var_post "a");
                     ]);
              ];
          };
        ];
    }
  in

  let actual    = Core_to_acsl.spec_to_acsl core_spec in

  let expected =
"/*@
  loop invariant i <= 10;
  loop assigns a, i;
  loop variant 10 - i;
*/"
  in
  test_framework expected actual

let test_core_to_acsl_result_ens _ctx =
  let core_spec : C.spec =
    {
      kind = C.FunctionContract;
      params = [];
      behaviors =
        [
          {
            b_name = None;
            clauses =
              [
                C.Assumes C.PTrue;
                C.Requires C.PTrue;
                C.Assigns [];
                C.Ensures (mk_eq mk_result (mk_add (mk_var_pre "a") (mk_int 10)));
              ];
          };
        ];
    }
  in

  let actual    = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\true;
  assigns \\nothing;
  ensures \\result == \\old(a) + 10;
*/"
  in
  test_framework expected actual

let suite =
  "core_to_acsl tests" >::: [
    "core_to_acsl_swap"               >:: test_core_to_acsl_swap;
    "core_to_acsl_no_swap"            >:: test_core_to_acsl_no_swap;
    "core_to_acsl_triple_swap"        >:: test_core_to_acsl_triple_swap;
    "core_to_acsl_case_behaviors"     >:: test_core_to_acsl_case_behaviors;
    "core_to_acsl_loop_simple"        >:: test_core_to_acsl_loop_simple;
    "core_to_acsl_loop_term_and_effects" >:: test_core_to_acsl_loop_term_and_effects;
    "core_to_acsl_result_ens"         >:: test_core_to_acsl_result_ens;
  ]

let () = run_test_tt_main suite
