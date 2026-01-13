open OUnit2
open Acsl_ast
open Acsl_ast_printer

let test_framework (expected : string) (actual : string) : unit =
  assert_equal
    ~printer:(fun s -> "\n" ^ s ^ "\n")
    expected
    actual

let v (x : string) : expr = EVar x
let i (n : int) : expr = EConstInt n
let b (x : bool) : expr = EConstBool x
let res : expr = EResult
let nul : expr = ENull

let add a b : expr = EBinop (BAdd, a, b)
let sub a b : expr = EBinop (BSub, a, b)
let mul a b : expr = EBinop (BMul, a, b)
(* let div a b : expr = EBinop (BDiv, a, b) *)

let eq a b : pred = PCmp (BEq, a, b)
let neq a b : pred = PCmp (BNeq, a, b)
let lt a b : pred = PCmp (BLt, a, b)
let lte a b : pred = PCmp (BLe, a, b)
(* let gt a b : pred = PCmp (BGt, a, b) *)
(* let gte a b : pred = PCmp (BGe, a, b) *)

let and2 a b : pred = PAnd [ a; b ]
let or2 a b : pred = POr [ a; b ]
let notp p : pred = PNot p
let impl a b : pred = PImplies (a, b)
let iff a b : pred = PIff (a, b)

let ptrue : pred = PTrue
let pfalse : pred = PFalse

let old (e : expr) : expr = EOld e
let at_entry (e : expr) : expr = EAt (e, LoopEntry)
let at_curr (e : expr) : expr = EAt (e, LoopCurrent)
let at_label (e : expr) (lab : string) : expr = EAt (e, UserLabel lab)
let deref (e : expr) : expr = EDeref e
let idx a i : expr = EIndex (a, i)
let range lo hi : expr = ERange (lo, hi)
let app (f : string) (args : expr list) : expr = EApp (f, args)

let valid (e : expr) : pred = PValid e
let valid_read (e : expr) : pred = PValidRead e
let papp (f : string) (args : expr list) : pred = PApp (f, args)
let forall (bs : (ident * sort option) list) (p : pred) : pred = PForall (bs, p)
let exists (bs : (ident * sort option) list) (p : pred) : pred = PExists (bs, p)

let binder ?(s = None) (x : string) : (ident * sort option) = (x, s)

let a_var (x : string) : assigns_target = AVar x
let a_deref (e : expr) : assigns_target = ADeref e
let a_range (base : expr) (lo : expr) (hi : expr) : assigns_target = ARange (base, lo, hi)

let assigns_nothing : assigns = ANothing
let assigns_items (xs : assigns_target list) : assigns = AItems xs

let beh (name : ident option) ~(assumes : pred) ~(ensures : pred) : behavior =
  { name; assumes; ensures }



let funspec
    ?(requires : pred option = None)
    ?(assigns : assigns = ANothing)
    ?(behaviors : behavior list = [])
    ?(ensures : pred option = None)
    ?(complete_behaviors : bool = false)
    ?(disjoint_behaviors : bool = false)
    ()
  : fun_spec =
  { requires; assigns; behaviors; ensures; complete_behaviors; disjoint_behaviors }

let loopspec
    ?(invariants : pred list = [])
    ?(assigns : assigns = ANothing)
    ?(variant : expr option = None)
    ()
  : loop_spec =
  { invariants; assigns; variant }

let test_string_of_expr_var _ =
  test_framework "a" (string_of_expr (v "a"))

let test_string_of_expr_int _ =
  test_framework "123" (string_of_expr (i 123))

let test_string_of_expr_bool_true _ =
  test_framework "\\true" (string_of_expr (b true))

let test_string_of_expr_bool_false _ =
  test_framework "\\false" (string_of_expr (b false))

let test_string_of_expr_result _ =
  test_framework "\\result" (string_of_expr res)

let test_string_of_expr_null _ =
  test_framework "NULL" (string_of_expr nul)

let test_string_of_expr_old _ =
  test_framework "\\old(a)" (string_of_expr (old (v "a")))

let test_string_of_expr_at_loop_entry _ =
  test_framework "\\at(a, LoopEntry)" (string_of_expr (at_entry (v "a")))

let test_string_of_expr_at_loop_current _ =
  test_framework "\\at(a, LoopCurrent)" (string_of_expr (at_curr (v "a")))

let test_string_of_expr_at_user_label _ =
  test_framework "\\at(a, MyLabel)" (string_of_expr (at_label (v "a") "MyLabel"))

let test_string_of_expr_deref _ =
  test_framework "*p" (string_of_expr (deref (v "p")))

let test_string_of_expr_index _ =
  test_framework "t[i]" (string_of_expr (idx (v "t") (v "i")))

let test_string_of_expr_range _ =
  test_framework "(0 .. n - 1)" (string_of_expr (range (i 0) (sub (v "n") (i 1))))

let test_string_of_expr_app _ =
  test_framework "f(a, 1, \\result)" (string_of_expr (app "f" [ v "a"; i 1; res ]))

let test_string_of_expr_binop_precedence _ =
  test_framework "a + b * c" (string_of_expr (add (v "a") (mul (v "b") (v "c"))))

let test_string_of_expr_unop_precedence _ =
  test_framework "-(a + b)" (string_of_expr (EUnop (UNeg, add (v "a") (v "b"))))

let test_string_of_pred_true _ =
  test_framework "\\true" (string_of_pred ptrue)

let test_string_of_pred_false _ =
  test_framework "\\false" (string_of_pred pfalse)

let test_string_of_pred_valid _ =
  test_framework "\\valid(a)" (string_of_pred (valid (v "a")))

let test_string_of_pred_valid_read _ =
  test_framework "\\valid_read(array + (0 .. length - 1))"
    (string_of_pred (valid_read (add (v "array") (range (i 0) (sub (v "length") (i 1))))))

let test_string_of_pred_cmp _ =
  test_framework "a == b" (string_of_pred (eq (v "a") (v "b")))

let test_string_of_pred_not _ =
  test_framework "!(a == b)" (string_of_pred (notp (eq (v "a") (v "b"))))

let test_string_of_pred_and_or_precedence _ =
  test_framework "a == b && (c == d || e == f)"
    (string_of_pred (and2 (eq (v "a") (v "b")) (or2 (eq (v "c") (v "d")) (eq (v "e") (v "f")))))

let test_string_of_pred_implies _ =
  test_framework "(a == b) ==> (c == d)"
    (string_of_pred (impl (eq (v "a") (v "b")) (eq (v "c") (v "d"))))

let test_string_of_pred_iff _ =
  test_framework "(a == b) <==> (c == d)"
    (string_of_pred (iff (eq (v "a") (v "b")) (eq (v "c") (v "d"))))

let test_string_of_pred_forall _ =
  test_framework "\\forall integer i; (0 <= i) ==> (i < n)"
    (string_of_pred
       (forall
          [ binder ~s:(Some SInt) "i" ]
          (impl (lte (i 0) (v "i")) (lt (v "i") (v "n")))))

let test_string_of_pred_exists _ =
  test_framework "\\exists size_t off; 0 <= off && off < length && array[off] == element"
    (string_of_pred
       (exists
          [ binder ~s:(Some (SUser "size_t")) "off" ]
          (PAnd
             [
               lte (i 0) (v "off");
               lt (v "off") (v "length");
               eq (idx (v "array") (v "off")) (v "element");
             ])))

let test_string_of_pred_app _ =
  test_framework "P(a, 1)" (string_of_pred (papp "P" [ v "a"; i 1 ]))

let test_string_of_assigns_nothing _ =
  test_framework "\\nothing" (string_of_assigns assigns_nothing)

let test_string_of_assigns_items_basic _ =
  test_framework "*a, *b" (string_of_assigns (assigns_items [ a_deref (v "a"); a_deref (v "b") ]))

let test_string_of_assigns_items_range _ =
  test_framework "array[0 .. length - 1]"
    (string_of_assigns
       (assigns_items
          [
            a_range (v "array") (i 0) (sub (v "length") (i 1));
          ]))

let test_print_fun_spec_simple_swap _ =
  let spec =
    FunSpec
      (funspec
         ~requires:(Some (and2 (valid (v "a")) (valid (v "b"))))
         ~assigns:(assigns_items [ a_deref (v "a"); a_deref (v "b") ])
         ~ensures:(Some (and2 (eq (deref (v "a")) (old (deref (v "b")))) (eq (deref (v "b")) (old (deref (v "a"))))))
         ())
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid(a) && \\valid(b);\n" ^
    "  assigns *a, *b;\n" ^
    "  ensures *a == \\old(*b) && *b == \\old(*a);\n" ^
    "*/"
  in
  test_framework expected (string_of_spec spec)

let test_print_fun_spec_case_two _ =
  let b1 =
    beh
      (Some "case1")
      ~assumes:(eq (v "a") (v "b"))
      ~ensures:(eq (deref (v "a")) (old (deref (v "a"))))
  in
  let b2 =
    beh
      (Some "case2")
      ~assumes:(neq (v "a") (v "b"))
      ~ensures:(and2 (eq (deref (v "a")) (old (deref (v "b")))) (eq (deref (v "b")) (old (deref (v "a")))))
  in
  let spec =
    FunSpec
      (funspec
         ~requires:(Some (and2 (valid (v "a")) (valid (v "b"))))
         ~assigns:(assigns_items [ a_deref (v "a"); a_deref (v "b") ])
         ~behaviors:[ b1; b2 ]
         ~complete_behaviors:true
         ~disjoint_behaviors:true
         ())
  in
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
    "  complete behaviors;\n" ^
    "  disjoint behaviors;\n" ^
    "*/"
  in
  test_framework expected (string_of_spec spec)

let test_print_fun_spec_valid_read_assigns_array _ =
  let spec =
    FunSpec
      (funspec
         ~requires:(Some (valid_read (add (v "array") (range (i 0) (sub (v "length") (i 1))))))
         ~assigns:(assigns_items [ a_range (v "array") (i 0) (sub (v "length") (i 1)) ])
         ~ensures:(Some
                    (forall
                       [ binder ~s:(Some (SUser "size_t")) "j" ]
                       (impl
                          (PAnd [ lte (i 0) (v "j"); lt (v "j") (v "length") ])
                          (eq (idx (v "array") (v "j")) (i 0)))))
         ())
  in
  let expected =
    "/*@\n" ^
    "  requires \\valid_read(array + (0 .. length - 1));\n" ^
    "  assigns array[0 .. length - 1];\n" ^
    "  ensures \\forall size_t j; (0 <= j && j < length) ==> (array[j] == 0);\n" ^
    "*/"
  in
  test_framework expected (string_of_spec spec)

let test_print_loop_spec_basic _ =
  let ls =
    loopspec
      ~invariants:[ lt (v "i") (i 30) ]
      ~assigns:(assigns_items [ a_var "i" ])
      ~variant:(Some (sub (i 30) (v "i")))
      ()
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
  in
  test_framework expected (string_of_spec (LoopSpec ls))

let test_print_loop_spec_two_invariants _ =
  let ls =
    loopspec
      ~invariants:[ lt (v "i") (i 30); lte (i 20) (v "i") ]
      ~assigns:(assigns_items [ a_var "i" ])
      ~variant:(Some (sub (i 30) (v "i")))
      ()
  in
  let expected =
    "/*@\n" ^
    "  loop invariant i < 30;\n" ^
    "  loop invariant 20 <= i;\n" ^
    "  loop assigns i;\n" ^
    "  loop variant 30 - i;\n" ^
    "*/"
  in
  test_framework expected (string_of_spec (LoopSpec ls))

let test_print_loop_spec_assigns_array_range _ =
  let ls =
    loopspec
      ~invariants:[
        forall
          [ binder ~s:(Some (SUser "size_t")) "j" ]
          (impl
             (PAnd [ lte (i 0) (v "j"); lt (v "j") (v "i") ])
             (eq (idx (v "array") (v "j")) (i 0)))
      ]
      ~assigns:(assigns_items [ a_var "i"; a_range (v "array") (i 0) (sub (v "length") (i 1)) ])
      ~variant:(Some (sub (v "length") (v "i")))
      ()
  in
  let expected =
    "/*@\n" ^
    "  loop invariant \\forall size_t j; (0 <= j && j < i) ==> (array[j] == 0);\n" ^
    "  loop assigns i, array[0 .. length - 1];\n" ^
    "  loop variant length - i;\n" ^
    "*/"
  in
  test_framework expected (string_of_spec (LoopSpec ls))

let suite =
  "acsl_printer" >::: [
    "expr_var" >:: test_string_of_expr_var;
    "expr_int" >:: test_string_of_expr_int;
    "expr_bool_true" >:: test_string_of_expr_bool_true;
    "expr_bool_false" >:: test_string_of_expr_bool_false;
    "expr_result" >:: test_string_of_expr_result;
    "expr_null" >:: test_string_of_expr_null;
    "expr_old" >:: test_string_of_expr_old;
    "expr_at_loop_entry" >:: test_string_of_expr_at_loop_entry;
    "expr_at_loop_current" >:: test_string_of_expr_at_loop_current;
    "expr_at_user_label" >:: test_string_of_expr_at_user_label;
    "expr_deref" >:: test_string_of_expr_deref;
    "expr_index" >:: test_string_of_expr_index;
    "expr_range" >:: test_string_of_expr_range;
    "expr_app" >:: test_string_of_expr_app;
    "expr_prec_binop" >:: test_string_of_expr_binop_precedence;
    "expr_prec_unop" >:: test_string_of_expr_unop_precedence;

    "pred_true" >:: test_string_of_pred_true;
    "pred_false" >:: test_string_of_pred_false;
    "pred_valid" >:: test_string_of_pred_valid;
    "pred_valid_read" >:: test_string_of_pred_valid_read;
    "pred_cmp" >:: test_string_of_pred_cmp;
    "pred_not" >:: test_string_of_pred_not;
    "pred_and_or_prec" >:: test_string_of_pred_and_or_precedence;
    "pred_implies" >:: test_string_of_pred_implies;
    "pred_iff" >:: test_string_of_pred_iff;
    "pred_forall" >:: test_string_of_pred_forall;
    "pred_exists" >:: test_string_of_pred_exists;
    "pred_app" >:: test_string_of_pred_app;

    "assigns_nothing" >:: test_string_of_assigns_nothing;
    "assigns_items_basic" >:: test_string_of_assigns_items_basic;
    "assigns_items_range" >:: test_string_of_assigns_items_range;

    "fun_spec_simple_swap" >:: test_print_fun_spec_simple_swap;
    "fun_spec_case_two" >:: test_print_fun_spec_case_two;
    "fun_spec_valid_read_assigns_array" >:: test_print_fun_spec_valid_read_assigns_array;

    "loop_spec_basic" >:: test_print_loop_spec_basic;
    "loop_spec_two_invariants" >:: test_print_loop_spec_two_invariants;
    "loop_spec_assigns_array_range" >:: test_print_loop_spec_assigns_array_range;
  ]

let () = run_test_tt_main suite
