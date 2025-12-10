open Core

(* helper *)
let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected: %S\nGot:      %S\n"
         name expected actual)

let mk_inout_param name = mk_param InOut name

let test_core_string_of_term_heap_pre () =
  let t = T_heap (Pre, "a") in
  let actual = string_of_term t in
  let expected = "H(a)" in
  assert_string_equality "core_string_of_term_heap_pre" expected actual

let test_core_string_of_term_heap_post () =
  let t = T_heap (Post, "a") in
  let actual = string_of_term t in
  let expected = "H'(a)" in
  assert_string_equality "core_string_of_term_heap_post" expected actual

let test_core_string_of_term_var () =
  let t = T_var "u" in
  let actual = string_of_term t in
  let expected = "u" in
  assert_string_equality "core_string_of_term_var" expected actual

let test_core_string_of_term_int () =
  let t = T_int 42 in
  let actual = string_of_term t in
  let expected = "42" in
  assert_string_equality "core_string_of_term_int" expected actual



let test_core_string_of_predicate_valid () =
  let p = P_valid "a" in
  let actual = string_of_predicate p in
  let expected = "valid(a)" in
  assert_string_equality "core_string_of_predicate_valid" expected actual

let test_core_string_of_predicate_eq_heaps () =
  let p = P_eq (T_heap (Pre, "a"), T_heap (Post, "b")) in
  let actual = string_of_predicate p in
  let expected = "H(a) == H'(b)" in
  assert_string_equality "core_string_of_predicate_eq_heaps" expected actual



let test_core_string_of_spec_swap () =
  let params = [ mk_inout_param "a"; mk_inout_param "b" ] in

  let requires = [ valid "a"; valid "b" ] in
  let ensures =
    [
      eq (heap_post "a") (heap_pre "b");
      eq (heap_post "b") (heap_pre "a");
    ]
  in
  let frame = [ "a"; "b" ] in
  let variant = None in

  let behavior_swap : behavior =
    {
      assumes = [neq (T_ptr "a") (T_ptr "b")];
      requires;
      ensures;
      frame;
      variant;
    }
  in

  let spec_swap : Core.spec =
    { params; behaviors = [ behavior_swap ] }
  in

  let actual = Core.string_of_spec spec_swap in
  let expected =
    "params (a:inout, b:inout)\n" ^
    "assumes a != b\n" ^
    "requires valid(a) && valid(b)\n" ^
    "ensures H'(a) == H(b) && H'(b) == H(a)\n" ^
    "frame {a, b}"
  in
  assert_string_equality "core_string_of_spec_swap" expected actual

let test_core_string_of_spec_empty () =
  let empty_behavior : behavior =
    {
      assumes = [];
      requires = [];
      ensures = [];
      frame = [];
      variant = None;
    }
  in
  let spec_empty : Core.spec =
    {
      params = [];
      behaviors = [ empty_behavior ];
    }
  in
  let actual = Core.string_of_spec spec_empty in
  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_string_equality "core_string_of_spec_empty" expected actual

let test_core_string_of_spec_with_variant () =
  let b : behavior =
    {
      assumes  = [];
      requires = [];
      ensures  = [];
      frame    = [];
      variant  = Some (T_int 42);
    }
  in
  let spec : Core.spec =
    {
      params    = [];
      behaviors = [ b ];
    }
  in
  let actual = Core.string_of_spec spec in
  let expected =
    "params ()\n" ^
    "assumes true\n" ^
    "requires true\n" ^
    "ensures true\n" ^
    "frame {}"
  in
  assert_string_equality "core_string_of_spec_with_variant" expected actual

let () =
  test_core_string_of_term_heap_pre ();
  test_core_string_of_term_heap_post ();
  test_core_string_of_term_var ();
  test_core_string_of_term_int ();

  test_core_string_of_predicate_valid ();
  test_core_string_of_predicate_eq_heaps ();

  test_core_string_of_spec_swap ();
  test_core_string_of_spec_empty ();

  test_core_string_of_spec_with_variant ();
