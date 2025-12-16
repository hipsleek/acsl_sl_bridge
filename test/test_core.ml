open OUnit2
open Core
open Core_builder
open Core_printer

let mk_inout_param name = mk_param InOut name

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

  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}\n"^
    "variant 42"
  in

  assert_equal expected actual

let test_core_string_of_spec_simple_contract _ =
  let b : behavior =
    {
      assumes  = [];
      requires = [ P_valid "a"; P_valid "b" ];
      ensures  =
        [
          P_eq (T_heap (Post, "a"), T_heap (Pre, "b"));
          P_eq (T_heap (Post, "b"), T_heap (Pre, "a"));
        ];
      frame    = [ "a"; "b" ];
      variant  = None;
    }
  in
  let spec   = { params = [ { name = "a"; mode = InOut }; { name = "b"; mode = InOut } ];
                 behaviors = [ b ] }
  in
  let actual = string_of_spec spec in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes true\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_equal expected actual

let test_core_string_of_spec_two_assigns_and_variant _ =
  let b : behavior =
    {
      assumes  = [ P_lte (T_var (Post, "i"), T_int 10) ];
      requires = [];
      ensures  =
        [
          P_eq (T_var (Post, "i"), T_int 10);
          P_eq (T_var (Post, "a"), T_var (Post, "a"));
        ];
      frame    = [];
      variant  = Some (T_arith (Sub, T_int 10, T_var (Post, "i")));
    }
  in
  let spec   = { params = []; behaviors = [ b ] } in
  let actual = string_of_spec spec in
  let expected =
    "params ()\n" ^
    "assumes i <= 10\n" ^
    "requires true\n" ^
    "ensures i == 10 && a == a\n" ^
    "frame {}\n" ^
    "variant 10-i"
  in
  assert_equal expected actual

let test_core_string_of_spec_result_ens _ =
  let b =
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
    }
  in

  let spec   = { params = []; behaviors = [ b ] } in
  let actual = string_of_spec spec in

  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures \\result == a+10\n" ^
    "frame {}"
  in

  assert_equal expected actual

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
    "spec_simple_contract" >:: test_core_string_of_spec_simple_contract;
    "spec_two_assigns_and_variant" >:: test_core_string_of_spec_two_assigns_and_variant;

    "spec_result_ens" >:: test_core_string_of_spec_result_ens;
  ]

let () = run_test_tt_main suite
