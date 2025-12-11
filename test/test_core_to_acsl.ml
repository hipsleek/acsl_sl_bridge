let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let mk_inout_param (name : string) : Core.param =
  Core.mk_param Core.InOut name

let mk_basic_spec (ptrs : string list) (eqs : Core.predicate list) : Core.spec =
  let params = List.map mk_inout_param ptrs in
  let requires = List.map Core.valid ptrs in
  let frame = ptrs in
  let behavior : Core.behavior =
    {
      Core.assumes = [];
      Core.requires = requires;
      Core.ensures = eqs;
      Core.frame = frame;
      Core.variant = None;
    }
  in
  {
    Core.params = params;
    Core.behaviors = [behavior];
  }


(* Unit tests *)
let test_core_to_acsl_swap () =
  let test_name = "core_to_acsl_swap" in
  let ptrs = ["a"; "b"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "b");
      Core.eq (Core.heap_post "b") (Core.heap_pre "a");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_no_swap () =
  let test_name = "core_to_acsl_no_swap" in
  let ptrs = ["a"; "b"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "a");
      Core.eq (Core.heap_post "b") (Core.heap_pre "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*a) && *b == \\old(*b);
*/"
  in
  assert_string_equality test_name expected actual

let test_core_to_acsl_triple_swap () =
  let test_name = "core_to_acsl_triple_swap" in
  let ptrs = ["a"; "b"; "c"] in
  let eqs =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "c");
      Core.eq (Core.heap_post "b") (Core.heap_pre "a");
      Core.eq (Core.heap_post "c") (Core.heap_pre "b");
    ]
  in
  let core_spec = mk_basic_spec ptrs eqs in
  let actual = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  requires \\valid(a) && \\valid(b) && \\valid(c);
  assigns  *a, *b, *c;
  ensures  *a == \\old(*c) && *b == \\old(*a) && *c == \\old(*b);
*/"
  in
  assert_string_equality test_name expected actual


let test_core_to_acsl_case_behaviors () =
  let test_name = "core_to_acsl_case_behaviors" in
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in

  (*case a == b *)
  let b1_requires = [ Core.valid "a"; Core.valid "b" ] in
  let b1_ensures =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "a");
    ]
  in
  let b1_frame = [ "a" ] in
  let b1 : Core.behavior =
    {
      Core.assumes = [ Core.P_eq (Core.T_ptr "a", Core.T_ptr "b") ];
      Core.requires = b1_requires;
      Core.ensures = b1_ensures;
      Core.frame = b1_frame;
      Core.variant = None;
    }
  in

  (*case a != b*)
  let b2_requires = [ Core.valid "a"; Core.valid "b" ] in
  let b2_ensures  =
    [
      Core.eq (Core.heap_post "a") (Core.heap_pre "b");
      Core.eq (Core.heap_post "b") (Core.heap_pre "a");
    ]
  in
  let b2_frame = [ "a"; "b" ] in
  let b2 : Core.behavior =
    {
      Core.assumes = [ Core.P_neq (Core.T_ptr "a", Core.T_ptr "b") ];
      Core.requires = b2_requires;
      Core.ensures = b2_ensures;
      Core.frame = b2_frame;
      Core.variant = None;
    }
  in

  let core_spec : Core.spec =
    {
      Core.params = params;
      Core.behaviors = [ b1; b2 ];
    }
  in

  let actual = Core_to_acsl.spec_to_acsl core_spec in
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
  assert_string_equality test_name expected actual

let test_core_to_acsl_loop_variant () =
  let test_name = "core_to_acsl_loop_variant" in
  let behavior : Core.behavior =
    {
      Core.assumes =
        [ Core.lte (Core.var_post "i") (Core.T_int 30) ];
      Core.requires = [];
      Core.ensures  = [];
      Core.frame    = [];
      Core.variant  = Some (Core.var_post "30-i");
    }
  in

  let core_spec : Core.spec =
    {
      Core.params    = [];
      Core.behaviors = [ behavior ];
    }
  in

  let actual   = Core_to_acsl.spec_to_acsl core_spec in
  let expected =
"/*@
  loop invariant i <= 30;
  loop assigns i;
  loop variant 30-i;
*/"
  in
  assert_string_equality test_name expected actual


let () =
  test_core_to_acsl_swap ();
  test_core_to_acsl_no_swap ();
  test_core_to_acsl_triple_swap ();
  test_core_to_acsl_case_behaviors ();
  test_core_to_acsl_loop_variant ();