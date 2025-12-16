open OUnit2
let test_framework (expected : string) (actual : string) : unit =
  assert_equal
    ~printer:(fun s -> "\n" ^ s ^ "\n")
    expected
    actual

let mk_inout_param (name : string) : Core.param =
  Core_builder.mk_param Core.InOut name

let mk_basic_spec (ptrs : string list) (eqs : Core.predicate list) : Core.spec =
  let params   = List.map mk_inout_param ptrs in
  let requires = List.map Core_builder.valid ptrs in
  let frame    = ptrs in
  let behavior : Core.behavior =
    {
      Core.assumes  = [];
      Core.requires = requires;
      Core.ensures  = eqs;
      Core.frame    = frame;
      Core.variant  = None;
    }
  in
  {
    Core.params    = params;
    Core.behaviors = [ behavior ];
  }

(* Unit tests *)

let test_core_to_acsl_swap _ctx =
  let ptrs = [ "a"; "b" ] in
  let eqs =
    [
      Core_builder.eq
        (Core_builder.heap_post "a")
        (Core_builder.heap_pre  "b");
      Core_builder.eq
        (Core_builder.heap_post "b")
        (Core_builder.heap_pre  "a");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
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
  let eqs =
    [
      Core_builder.eq
        (Core_builder.heap_post "a")
        (Core_builder.heap_pre  "a");
      Core_builder.eq
        (Core_builder.heap_post "b")
        (Core_builder.heap_pre  "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
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
  let eqs =
    [
      Core_builder.eq
        (Core_builder.heap_post "a")
        (Core_builder.heap_pre  "c");
      Core_builder.eq
        (Core_builder.heap_post "b")
        (Core_builder.heap_pre  "a");
      Core_builder.eq
        (Core_builder.heap_post "c")
        (Core_builder.heap_pre  "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
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

  (* case a == b *)
  let b1_requires = [ Core_builder.valid "a"; Core_builder.valid "b" ] in
  let b1_ensures =
    [
      Core_builder.eq
        (Core_builder.heap_post "a")
        (Core_builder.heap_pre  "a");
    ]
  in
  let b1_frame = [ "a" ] in
  let b1 : Core.behavior =
    {
      Core.assumes  = [ Core.P_eq (Core.T_ptr "a", Core.T_ptr "b") ];
      Core.requires = b1_requires;
      Core.ensures  = b1_ensures;
      Core.frame    = b1_frame;
      Core.variant  = None;
    }
  in

  (* case a != b *)
  let b2_requires = [ Core_builder.valid "a"; Core_builder.valid "b" ] in
  let b2_ensures  =
    [
      Core_builder.eq
        (Core_builder.heap_post "a")
        (Core_builder.heap_pre  "b");
      Core_builder.eq
        (Core_builder.heap_post "b")
        (Core_builder.heap_pre  "a");
    ]
  in
  let b2_frame = [ "a"; "b" ] in
  let b2 : Core.behavior =
    {
      Core.assumes  = [ Core.P_neq (Core.T_ptr "a", Core.T_ptr "b") ];
      Core.requires = b2_requires;
      Core.ensures  = b2_ensures;
      Core.frame    = b2_frame;
      Core.variant  = None;
    }
  in

  let core_spec : Core.spec =
    {
      Core.params    = params;
      Core.behaviors = [ b1; b2 ];
    }
  in

  let actual   = Core_to_acsl.spec_to_acsl core_spec in
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
  let core_spec : Core.spec =
    {
      params = [];
      behaviors =
        [
          {
            assumes  = [ P_lt (T_var (Post, "i"), T_int 30) ];
            requires = [];
            ensures  = [];
            frame    = [];
            variant  = Some (T_arith (Sub, T_int 30, T_var (Post, "i")));
          };
          {
            assumes  = [ P_gte (T_var (Post, "i"), T_int 30) ];
            requires = [];
            ensures  = [];
            frame    = [];
            variant  = None;
          };
        ];
    }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in

  let expected =
"/*@
  loop invariant i < 30;
  loop assigns i;
  loop variant 30 - i;
*/"
  in
  test_framework expected actual

(* NEW: loop with a single behavior carrying Term + pure ensures mentioning 'a' and 'i' *)
let test_core_to_acsl_loop_term_and_effects _ctx =
  let core_spec : Core.spec =
    {
      params = [];
      behaviors =
        [
          {
            assumes  = [ P_lte (T_var (Post, "i"), T_int 10) ];
            requires = [];
            ensures  =
              [
                P_eq (T_var (Post, "i"), T_int 10);
                P_eq
                  ( T_var (Post, "a"),
                    T_var (Post, "a") );
              ];
            frame    = [];
            variant  = Some (T_arith (Sub, T_int 10, T_var (Post, "i")));
          };
        ];
    }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  loop invariant i <= 10;
  loop assigns a, i;
  loop variant 10 - i;
*/"
  in
  test_framework expected actual

let test_core_to_acsl_result_ens _ctx =
  let core_spec : Core.spec =
    {
      params = [];
      behaviors =
        [
          {
            assumes  = [];
            requires = [];
            ensures  =
              [
                P_eq
                  ( T_result,
                    T_arith (Add, T_var (Pre, "a"), T_int 10) );
              ];
            frame    = [];
            variant  = None;
          };
        ];
    }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
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
    "core_to_acsl_swap" >:: test_core_to_acsl_swap;
    "core_to_acsl_no_swap" >:: test_core_to_acsl_no_swap;
    "core_to_acsl_triple_swap" >:: test_core_to_acsl_triple_swap;
    "core_to_acsl_case_behaviors" >:: test_core_to_acsl_case_behaviors;
    "core_to_acsl_loop_simple" >:: test_core_to_acsl_loop_simple;
    "core_to_acsl_loop_term_and_effects" >:: test_core_to_acsl_loop_term_and_effects;
    "core_to_acsl_result_ens" >:: test_core_to_acsl_result_ens;
  ]

let () = run_test_tt_main suite
