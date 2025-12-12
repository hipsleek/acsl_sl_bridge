open OUnit2
open Core
open Core_builder
open Core_printer

let mk_inout_param name = mk_param InOut name

(* ---------------------- TERM TESTS ---------------------- *)

let test_core_string_of_term_heap_pre _ =
  let t = T_heap (Pre, "a") in
  assert_equal
    "H(a)"
    (string_of_term t)

let test_core_string_of_term_heap_post _ =
  let t = T_heap (Post, "a") in
  assert_equal
    "H'(a)"
    (string_of_term t)

let test_core_string_of_term_var_pre _ =
  let t = T_var (Pre, "u") in
  assert_equal
    "u"
    (string_of_term t)

let test_core_string_of_term_var_post _ =
  let t = T_var (Post, "u") in
  assert_equal
    "u"
    (string_of_term t)

let test_core_string_of_term_int _ =
  let t = T_int 42 in
  assert_equal
    "42"
    (string_of_term t)

(* ---------------------- PREDICATE TESTS ---------------------- *)

let test_core_string_of_predicate_valid _ =
  let p = P_valid "a" in
  assert_equal
    "valid(a)"
    (string_of_predicate p)

let test_core_string_of_predicate_eq_heaps _ =
  let p = P_eq (T_heap (Pre, "a"), T_heap (Post, "b")) in
  assert_equal
    "H(a) == H'(b)"
    (string_of_predicate p)

(* ---------------------- SPEC TESTS ---------------------- *)

let test_core_string_of_spec_swap _ =
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in
  let requires = [ valid "a"; valid "b" ] in
  let ensures =
    [
      eq (heap_post "a") (heap_pre "b");
      eq (heap_post "b") (heap_pre "a");
    ]
  in
  let frame = [ "a"; "b" ] in

  let behavior_swap : behavior =
    {
      assumes  = [ neq (T_ptr "a") (T_ptr "b") ];
      requires = requires;
      ensures  = ensures;
      frame    = frame;
      variant  = None;
    }
  in

  let spec_swap : Core.spec = { params; behaviors = [behavior_swap] } in
  let actual = string_of_spec spec_swap in

  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes a != b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in

  assert_equal expected actual

let test_core_string_of_spec_empty _ =
  let empty_behavior =
    {
      assumes = [];
      requires = [];
      ensures = [];
      frame = [];
      variant = None;
    }
  in

  let spec_empty = { params = []; behaviors = [empty_behavior] } in

  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in

  assert_equal
    expected
    (string_of_spec spec_empty)

let test_core_string_of_spec_with_variant _ =
  let b =
    {
      assumes  = [];
      requires = [];
      ensures  = [];
      frame    = [];
      variant  = Some (T_int 42);
    }
  in

  let spec   = { params = []; behaviors = [b] } in
  let actual = string_of_spec spec in

  (* Note: variant is currently NOT printed in output (consistent with your previous tests) *)
  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n"^
    "variant 42"
  in

  assert_equal expected actual

(* ---------------------- SUITE ---------------------- *)

let suite =
  "core printer tests" >::: [
    "term_heap_pre"        >:: test_core_string_of_term_heap_pre;
    "term_heap_post"       >:: test_core_string_of_term_heap_post;
    "term_var_pre"         >:: test_core_string_of_term_var_pre;
    "term_var_post"        >:: test_core_string_of_term_var_post;
    "term_int"             >:: test_core_string_of_term_int;

    "predicate_valid"      >:: test_core_string_of_predicate_valid;
    "predicate_eq_heaps"   >:: test_core_string_of_predicate_eq_heaps;

    "spec_swap"            >:: test_core_string_of_spec_swap;
    "spec_empty"           >:: test_core_string_of_spec_empty;
    "spec_with_variant"    >:: test_core_string_of_spec_with_variant;
  ]

let () = run_test_tt_main suite
