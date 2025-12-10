open Acsl_ast

let assert_string_equality name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s failed.\nExpected:\n%s\nGot:\n%s\n" name expected actual)

let test_acsl_term_var () =
  let actual = acsl_term (TVar "a") in
  let expected = "a" in
  assert_string_equality "acsl_term_var" expected actual

let test_acsl_term_int () =
  let actual = acsl_term (TInt 42) in
  let expected = "42" in
  assert_string_equality "acsl_term_int" expected actual

let test_acsl_term_deref () =
  let actual = acsl_term (TDeref (TVar "a")) in
  let expected = "*a" in
  assert_string_equality "acsl_term_deref" expected actual

let test_acsl_term_old () =
  let actual = acsl_term (TOld (TDeref (TVar "a"))) in
  let expected = "\\old(*a)" in
  assert_string_equality "acsl_term_old" expected actual

let test_acsl_term_valid () =
  let actual = acsl_term (TApp ("\\valid", [TVar "a"])) in
  let expected = "\\valid(a)" in
  assert_string_equality "acsl_term_valid" expected actual

let test_acsl_term_binop_eq () =
  let actual = acsl_term (TBinOp (Eq, TVar "a", TVar "b")) in
  let expected = "a == b" in
  assert_string_equality "acsl_term_binop_eq" expected actual

let test_acsl_term_binop_lte () =
  let actual = acsl_term (TBinOp (Lte, TVar "x", TInt 5)) in
  let expected = "x <= 5" in
  assert_string_equality "acsl_term_binop_lte" expected actual


let test_acsl_contract_flat () =
  let assigns = [ TDeref (TVar "a"); TDeref (TVar "b") ] in

  let behavior =
    {
      b_name = None;
      b_assumes = [];
      b_requires = [ TApp ("\\valid", [TVar "a"]);
                     TApp ("\\valid", [TVar "b"]) ];
      b_ensures =
        [ TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "b")));
          TBinOp (Eq, TDeref (TVar "b"), TOld (TDeref (TVar "a"))); ];
    }
  in

  let contract = { assigns; behaviors = [behavior] } in
  let actual = acsl_contract contract in

  let expected =
"/*@
  requires \\valid(a) && \\valid(b);
  assigns  *a, *b;
  ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in

  assert_string_equality "acsl_contract_flat" expected actual

let test_acsl_contract_cases () =
  let assigns = [ TDeref (TVar "a"); TDeref (TVar "b") ] in

  let b1 =
    {
      b_name = Some "alias";
      b_assumes = [ TBinOp (Eq, TVar "a", TVar "b") ];
      b_requires = [ TApp ("\\valid", [TVar "a"]); TApp ("\\valid", [TVar "b"]) ];
      b_ensures = [ TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "a"))) ];
    }
  in

  let b2 =
    {
      b_name = Some "no_alias";
      b_assumes = [ TBinOp (Neq, TVar "a", TVar "b") ];
      b_requires = [ TApp ("\\valid", [TVar "a"]); TApp ("\\valid", [TVar "b"]) ];
      b_ensures =
        [ TBinOp (Eq, TDeref (TVar "a"), TOld (TDeref (TVar "b")));
          TBinOp (Eq, TDeref (TVar "b"), TOld (TDeref (TVar "a"))); ];
    }
  in

  let contract = { assigns; behaviors = [b1; b2] } in
  let actual = acsl_contract contract in

  let expected =
"/*@
  assigns  *a, *b;
  behavior alias:
    assumes a == b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*a);
  behavior no_alias:
    assumes a != b;
    requires \\valid(a) && \\valid(b);
    ensures  *a == \\old(*b) && *b == \\old(*a);
*/"
  in

  assert_string_equality "acsl_contract_cases" expected actual

let test_acsl_loop_contract_simple () =
  let lc : loop_contract =
    {
      l_invariants = [ TBinOp (Lte, TVar "i", TInt 30) ];
      l_assigns    = [ TVar "i" ];
      l_variant    = Some (TVar "30-i");
    }
  in
  let actual = acsl_loop_contract lc in
  let expected =
"/*@\n" ^
"  loop invariant i <= 30;\n" ^
"  loop assigns i;\n" ^
"  loop variant 30-i;\n" ^
"*/"
  in
  assert_string_equality "acsl_loop_contract_simple" expected actual

let () =
  test_acsl_term_var ();
  test_acsl_term_int ();
  test_acsl_term_deref ();
  test_acsl_term_old ();
  test_acsl_term_valid ();
  test_acsl_term_binop_eq ();
  test_acsl_term_binop_lte ();

  test_acsl_contract_flat ();
  test_acsl_contract_cases ();

  test_acsl_loop_contract_simple ();
