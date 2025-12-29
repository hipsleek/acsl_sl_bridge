open OUnit2

module C = Core
module A = Acsl_ast

let test_framework (expected : string) (actual : string) : unit =
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected actual

let mk_var (ph:C.phase) (x:string) : C.term = C.TVar (ph, x)

let mk_and (ps:C.predicate list) : C.predicate =
  match ps with
  | [] -> C.PTrue
  | [p] -> p
  | _ -> C.PAnd ps

let mk_or (ps:C.predicate list) : C.predicate =
  match ps with
  | [] -> C.PFalse
  | [p] -> p
  | _ -> C.POr ps

let mk_inout_param (name : string) : C.param =
  { C.name; mode = C.InOut }

let mk_valid (p : string) : C.predicate =
  C.PAtom (C.APred ("valid", [ C.TPtr p ]))

let mk_valid_read_range (base : C.term) (lo : C.term) (hi : C.term) : C.predicate =
  C.PAtom (C.APred ("valid_read_range", [ base; lo; hi ]))

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
let mk_gt  t1 t2 = mk_rel C.Gt  t1 t2
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*a) && *b == \\old(*b);\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b) && \\valid(c);\n" ^
    "  assigns *a, *b, *c;\n" ^
    "  ensures *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);\n" ^
    "*/"
  in
  test_framework expected actual


let test_core_to_acsl_swap_type_mismatch _ctx =
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  behavior case1:\n" ^
    "    assumes a == b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case2:\n" ^
    "    assumes a != b;\n" ^
    "    ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework expected actual


let test_core_to_acsl_case_single _ctx =
  let params = [ mk_inout_param "a" ] in
  let requires = mk_valid "a" in
  let assigns  = mk_assigns_heaps [ "a" ] in
  let b1 : C.behavior =
    {
      b_name = None;
      clauses =
        [
          C.Assumes (mk_eq (mk_ptr "a") (mk_ptr "b")); (* assumes a==b, b is just a scalar var in ACSL *)
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures (mk_eq (mk_heap_post "a") (mk_heap_pre "a"));
        ];
    }
  in
  let core_spec : C.spec = { kind = C.FunctionContract; params; behaviors = [ b1 ] } in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a);\n" ^
    "  assigns *a;\n" ^
    "  ensures *a == \\old(*a);\n" ^
    "*/"
  in
  test_framework expected actual


let test_core_to_acsl_case_operators _ctx =
  let params = [ mk_inout_param "a" ] in
  let requires = mk_valid "a" in
  let assigns  = mk_assigns_heaps [ "a" ] in

  let mk_case name assume_pred : C.behavior =
    {
      b_name = Some name;
      clauses =
        [
          C.Assumes assume_pred;
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures (mk_eq (mk_heap_post "a") (mk_heap_pre "a"));
        ];
    }
  in

  let b1 = mk_case "case1" (mk_lt  (mk_ptr "a") (mk_ptr "b")) in
  let b2 = mk_case "case2" (mk_lte (mk_ptr "a") (mk_ptr "b")) in
  let b3 = mk_case "case3" (mk_gt  (mk_ptr "a") (mk_ptr "b")) in
  let b4 = mk_case "case4" (mk_gte (mk_ptr "a") (mk_ptr "b")) in

  let core_spec : C.spec =
    { kind = C.FunctionContract; params; behaviors = [ b1; b2; b3; b4 ] }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a);\n" ^
    "  assigns *a;\n" ^
    "  behavior case1:\n" ^
    "    assumes a < b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case2:\n" ^
    "    assumes a <= b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case3:\n" ^
    "    assumes a > b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "  behavior case4:\n" ^
    "    assumes a >= b;\n" ^
    "    ensures *a == \\old(*a);\n" ^
    "*/"
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
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
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
                C.Ensures
                  (C.PAnd
                     [
                       mk_eq (mk_var_post "i") (mk_int 10);
                       mk_eq
                         (mk_var_post "a")
                         (mk_add
                            (mk_var_pre "a")
                            (mk_sub (mk_var_post "i") (mk_var_pre "i")));
                     ]);
              ];
          };
        ];
    }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= 10;\n" ^
    "  loop invariant a == \\at(a, LoopEntry) + (i - \\at(i, LoopEntry));\n" ^
    "  loop assigns a, i;\n" ^
    "  loop variant 10 - i;\n" ^
    "*/"
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
    "/*@\n" ^
    "  requires \\true;\n" ^
    "  assigns \\nothing;\n" ^
    "  ensures \\result == a + 10;\n" ^
    "*/"
  in
  test_framework expected actual

let test_core_to_acsl_loop_search_forall_index _ctx =
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
                C.Assumes
                  (mk_and
                     [
                       mk_rel C.Lte (mk_int 0) (mk_var C.Pre "i");
                       mk_rel C.Lte (mk_var C.Pre "i") (mk_var C.Pre "length");
                       C.PForall
                         ( [ { C.b_name = "j"; b_ty = Some "size_t" } ],
                           C.PImplies
                             ( mk_and
                                 [
                                   mk_rel C.Lte (mk_int 0) (mk_var C.Pre "j");
                                   mk_rel C.Lt (mk_var C.Pre "j") (mk_var C.Pre "i");
                                 ],
                               mk_rel C.Neq
                                 (C.TIndex (C.Pre, mk_var C.Pre "array", mk_var C.Pre "j"))
                                 (mk_var C.Pre "element") ) );
                     ]);

                C.Requires C.PTrue;
                C.Assigns [ C.AsVar "i" ];

                C.Ensures
                  (mk_or
                     [
                       mk_rel C.Eq (mk_var C.Post "i") (mk_var C.Post "length");
                       mk_and
                         [
                           C.PAtom
                             (C.APred
                                ( "\\return",
                                  [
                                    C.TLoad
                                      ( C.Post,
                                        C.TArith (C.Add, mk_ptr "array", mk_var C.Post "i") );
                                  ] ));
                           mk_rel C.Neq
                             (C.TIndex (C.Post, mk_var C.Post "array", mk_var C.Post "i"))
                             (mk_var C.Post "element");
                           mk_rel C.Lte (mk_int 0) (mk_var C.Post "i");
                           mk_rel C.Lt (mk_var C.Post "i") (mk_var C.Post "length");
                         ];
                     ]);

                C.Variant (C.TArith (C.Sub, mk_var C.Pre "length", mk_var C.Pre "i"));
              ];
          };
        ];
    }
  in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  loop invariant i <= length;\n" ^
    "  loop invariant 0 <= i;\n" ^
    "  loop invariant \\forall size_t j; (0 <= j && j < i) ==> (array[j] != element);\n" ^
    "  loop assigns i;\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework expected actual

let test_core_to_acsl_incr_max _ctx =
  let params = [ mk_inout_param "p"; mk_inout_param "q" ] in
  let requires =
    C.PAnd [ mk_neq (mk_ptr "p") (mk_ptr "q"); mk_valid "p"; mk_valid "q" ]
  in
  let assigns = mk_assigns_heaps [ "p"; "q" ] in

  let b1 : C.behavior =
    {
      b_name = Some "case1";
      clauses =
        [
          C.Assumes (mk_gte (C.TLoad (C.Pre, mk_ptr "p")) (C.TLoad (C.Pre, mk_ptr "q")));
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures
            (C.PAnd
               [
                 mk_eq (mk_heap_post "p") (mk_add (mk_heap_pre "p") (mk_int 1));
                 mk_eq (mk_heap_post "q") (mk_heap_pre "q");
               ]);
        ];
    }
  in

  let b2 : C.behavior =
    {
      b_name = Some "case2";
      clauses =
        [
          C.Assumes (mk_lt (C.TLoad (C.Pre, mk_ptr "p")) (C.TLoad (C.Pre, mk_ptr "q")));
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures
            (C.PAnd
               [
                 mk_eq (mk_heap_post "p") (mk_heap_pre "p");
                 mk_eq (mk_heap_post "q") (mk_add (mk_heap_pre "q") (mk_int 1));
               ]);
        ];
    }
  in

  let core_spec : C.spec =
    { kind = C.FunctionContract; params; behaviors = [ b1; b2 ] }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  requires p != q && \\valid(p) && \\valid(q);\n" ^
    "  assigns *p, *q;\n" ^
    "  behavior case1:\n" ^
    "    assumes *p >= *q;\n" ^
    "    ensures *p == \\old(*p) + 1 && *q == \\old(*q);\n" ^
    "  behavior case2:\n" ^
    "    assumes *p < *q;\n" ^
    "    ensures *p == \\old(*p) && *q == \\old(*q) + 1;\n" ^
    "*/"
  in
  test_framework expected actual

let test_core_to_acsl_spec_search _ctx =
  let params = [ mk_inout_param "array" ] in
  let requires = mk_valid_read_range
      (mk_var_pre "array")
      (mk_int 0)
      (mk_sub (mk_var_pre "length") (mk_int 1))
  in
  let assigns : C.assignable list = [] in

  let off_binder = { C.b_name = "off"; b_ty = Some "size_t" } in

  let exists_assumes =
    C.PExists
      ( [ off_binder ],
        mk_and
          [
            mk_rel C.Lte (mk_int 0) (mk_var C.Pre "off");
            mk_rel C.Lt (mk_var C.Pre "off") (mk_var C.Pre "length");
            mk_eq
              (C.TIndex (C.Pre, mk_var C.Pre "array", mk_var C.Pre "off"))
              (mk_var C.Pre "element");
          ] )
  in

  let forall_assumes =
    C.PForall
      ( [ off_binder ],
        C.PImplies
          ( mk_and
              [
                mk_rel C.Lte (mk_int 0) (mk_var C.Pre "off");
                mk_rel C.Lt (mk_var C.Pre "off") (mk_var C.Pre "length");
              ],
            mk_neq
              (C.TIndex (C.Pre, mk_var C.Pre "array", mk_var C.Pre "off"))
              (mk_var C.Pre "element" ) ) )
  in

  let b1 : C.behavior =
    {
      b_name = Some "case1";
      clauses =
        [
          C.Assumes exists_assumes;
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures
            (mk_and
               [
                 mk_rel C.Gte mk_result (mk_ptr "array");
                 mk_rel C.Lt mk_result (mk_add (mk_ptr "array") (mk_var_pre "length"));
                 mk_eq (C.TLoad (C.Pre, mk_result)) (mk_var_pre "element");
               ]);
        ];
    }
  in

  let b2 : C.behavior =
    {
      b_name = Some "case2";
      clauses =
        [
          C.Assumes forall_assumes;
          C.Requires requires;
          C.Assigns assigns;
          C.Ensures (mk_eq mk_result (C.TVar (C.Pre, "NULL")));
        ];
    }
  in

  let core_spec : C.spec =
    { kind = C.FunctionContract; params; behaviors = [ b1; b2 ] }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
    "/*@\n" ^
    "  requires \\valid_read(array + (0 .. length - 1));\n" ^
    "  assigns \\nothing;\n" ^
    "  behavior case1:\n" ^
    "    assumes \\exists size_t off; 0 <= off && off < length && array[off] == element;\n" ^
    "    ensures \\result >= array && \\result < array + length && \\old(*\\result) == element;\n" ^
    "  behavior case2:\n" ^
    "    assumes \\forall size_t off; (0 <= off && off < length) ==> (array[off] != element);\n" ^
    "    ensures \\result == NULL;\n" ^
    "*/"
  in
  test_framework expected actual

let suite =
  "core_to_acsl tests" >::: [
    "core_to_acsl_swap"               >:: test_core_to_acsl_swap;
    "core_to_acsl_no_swap"            >:: test_core_to_acsl_no_swap;
    "core_to_acsl_triple_swap"        >:: test_core_to_acsl_triple_swap;
    "core_to_acsl_swap_type_mismatch" >:: test_core_to_acsl_swap_type_mismatch;
    "core_to_acsl_case_behaviors"     >:: test_core_to_acsl_case_behaviors;
    "core_to_acsl_case_single"        >:: test_core_to_acsl_case_single;
    "core_to_acsl_case_operators"     >:: test_core_to_acsl_case_operators;
    "core_to_acsl_loop_simple"        >:: test_core_to_acsl_loop_simple;
    "core_to_acsl_loop_term_and_effects" >:: test_core_to_acsl_loop_term_and_effects;
    "core_to_acsl_result_ens"         >:: test_core_to_acsl_result_ens;
    "core_to_acsl_loop_search_forall_index" >:: test_core_to_acsl_loop_search_forall_index;
    "core_to_acsl_incr_max"           >:: test_core_to_acsl_incr_max;
    "core_to_acsl_spec_search"        >:: test_core_to_acsl_spec_search;
  ]

let () = run_test_tt_main suite
