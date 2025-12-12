open OUnit2

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
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_equal expected actual

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
  assigns  *a, *b;
  ensures  *a == \\old(*a) && *b == \\old(*b);
*/"
  in
  assert_equal expected actual

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
  assigns  *a, *b, *c;
  ensures  *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  assert_equal expected actual

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
  assigns  *a, *b;
  behavior case1:
    assumes a == b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*a);
  behavior case2:
    assumes a != b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_equal expected actual


let suite =
  "core_to_acsl tests" >::: [
    "core_to_acsl_swap"           >:: test_core_to_acsl_swap;
    "core_to_acsl_no_swap"        >:: test_core_to_acsl_no_swap;
    "core_to_acsl_triple_swap"    >:: test_core_to_acsl_triple_swap;
    "core_to_acsl_case_behaviors" >:: test_core_to_acsl_case_behaviors;
  ]

let () = run_test_tt_main suite
