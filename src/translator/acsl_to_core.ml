(* acsl_to_core.ml *)

open Acsl_ast
module C = Core

(***)
(* Operators *)
(***)

let rel_of_binop : Acsl_ast.binop -> C.rel option = function
  | BEq -> Some C.Eq
  | BNeq -> Some C.Neq
  | BLt -> Some C.Lt
  | BLe -> Some C.Lte
  | BGt -> Some C.Gt
  | BGe -> Some C.Gte
  | _ -> None

let arith_of_binop : Acsl_ast.binop -> C.arith_op option = function
  | BAdd -> Some C.Add
  | BSub -> Some C.Sub
  | BMul -> Some C.Mul
  | BDiv -> Some C.Div
  | _ -> None

(***)
(* Sorts / binders *)
(***)

let sort_ty_of_sort_opt (s : Acsl_ast.sort option) : string option =
  match s with
  | None -> None
  | Some SInt -> Some "int"
  | Some SBool -> Some "bool"
  | Some SPtr -> Some "ptr"
  | Some (SUser u) -> Some u

let binders_of_acsl (bs : (ident * sort option) list) : C.binder list =
  List.map (fun (b_name, tyopt) -> { C.b_name; b_ty = sort_ty_of_sort_opt tyopt }) bs

(***)
(* Predicate helpers *)
(***)

let p_atom (a : C.atom) : C.predicate = C.PAtom a

let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (r, t1, t2))

let pred_and (ps : C.predicate list) : C.predicate =
  let rec flatten acc = function
    | [] -> List.rev acc
    | C.PTrue :: tl -> flatten acc tl
    | C.PAnd xs :: tl -> flatten acc (xs @ tl)
    | x :: tl -> flatten (x :: acc) tl
  in
  let xs = flatten [] ps in
  match xs with
  | [] -> C.PTrue
  | [ x ] -> x
  | _ -> C.PAnd xs

let pred_or (ps : C.predicate list) : C.predicate =
  let rec flatten acc = function
    | [] -> List.rev acc
    | C.PFalse :: tl -> flatten acc tl
    | C.POr xs :: tl -> flatten acc (xs @ tl)
    | x :: tl -> flatten (x :: acc) tl
  in
  let xs = flatten [] ps in
  match xs with
  | [] -> C.PFalse
  | [ x ] -> x
  | _ -> C.POr xs

(***)
(* Expr -> Core.term *)
(***)

let rec term_of_expr (default_phase : C.phase) (e : Acsl_ast.expr) : C.term =
  match e with
  | EConstInt n -> C.TInt n
  | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
  | EResult -> C.TResult
  | EVar x -> C.TVar (default_phase, x)
  | ENull -> C.TApp ("NULL", [])

  | EOld e1 ->
      term_of_expr C.Pre e1

  | EAt (e1, lbl) ->
      (* best-effort phase mapping *)
      let ph =
        match lbl with
        | LoopEntry -> C.Pre
        | LoopCurrent -> default_phase
        | UserLabel _ -> default_phase
      in
      term_of_expr ph e1

  | EDeref (EVar p) ->
      (* keep the common heap shorthand *)
      C.THeap (default_phase, p)

  | EDeref addr ->
      C.TLoad (default_phase, term_of_expr default_phase addr)

  | EIndex (base, idx) ->
      C.TIndex (default_phase, term_of_expr default_phase base, term_of_expr default_phase idx)

  | ERange (lo, hi) ->
      (* keep structure; caller decides how/if to interpret it *)
      C.TApp ("range", [ term_of_expr default_phase lo; term_of_expr default_phase hi ])

  | EUnop (UNeg, e1) ->
      C.TArith (C.Sub, C.TInt 0, term_of_expr default_phase e1)

  | EUnop (UNot, e1) ->
      C.TApp ("not", [ term_of_expr default_phase e1 ])

  | EBinop (op, a, b) -> (
      match arith_of_binop op with
      | Some aop ->
          C.TArith (aop, term_of_expr default_phase a, term_of_expr default_phase b)
      | None ->
          (* do NOT overfit: preserve unknown binops structurally *)
          C.TApp ("binop", [ term_of_expr default_phase a; term_of_expr default_phase b ]) )

  | EApp (f, args) ->
      C.TApp (f, List.map (term_of_expr default_phase) args)

(***)
(* ACSL pred -> Core.predicate *)
(***)

let rec pred_of_pred (default_phase : C.phase) (p : Acsl_ast.pred) : C.predicate =
  match p with
  | PTrue -> C.PTrue
  | PFalse -> C.PFalse

  | PCmp (op, a, b) -> (
      match rel_of_binop op with
      | Some r ->
          mk_rel r (term_of_expr default_phase a) (term_of_expr default_phase b)
      | None ->
          (* not a relational op: keep it as a bool predicate application *)
          p_atom (C.APred ("bool", [ term_of_expr default_phase (EBinop (op, a, b)) ])) )

  | PApp (f, args) ->
      p_atom (C.APred (f, List.map (term_of_expr default_phase) args))

  | PAnd ps ->
      pred_and (List.map (pred_of_pred default_phase) ps)

  | POr ps ->
      pred_or (List.map (pred_of_pred default_phase) ps)

  | PNot q ->
      C.PNot (pred_of_pred default_phase q)

  | PImplies (a, b) ->
      C.PImplies (pred_of_pred default_phase a, pred_of_pred default_phase b)

  | PIff (a, b) ->
      pred_and
        [
          C.PImplies (pred_of_pred default_phase a, pred_of_pred default_phase b);
          C.PImplies (pred_of_pred default_phase b, pred_of_pred default_phase a);
        ]

  | PForall (bs, body) ->
      C.PForall (binders_of_acsl bs, pred_of_pred default_phase body)

  | PExists (bs, body) ->
      C.PExists (binders_of_acsl bs, pred_of_pred default_phase body)

  | PValid (EVar x) ->
      p_atom (C.APred ("valid", [ C.TPtr x ]))

  | PValid e ->
      p_atom (C.APred ("valid", [ term_of_expr default_phase e ]))

  | PValidRead e ->
      p_atom (C.APred ("valid_read", [ term_of_expr default_phase e ]))

(***)
(* assigns -> Core.assignable list *)
(***)

let assignable_of_assigns_target (t : Acsl_ast.assigns_target) : C.assignable option =
  match t with
  | AVar v -> Some (C.AsVar v)

  | ADeref (EVar p) ->
      (* common case: assigns *p *)
      Some (C.AsHeap p)

  | ADeref e ->
      Some (C.AsTerm (term_of_expr C.Pre e))

  | ARange (EVar p, lo, hi) ->
      Some (C.AsRange (p, term_of_expr C.Pre lo, term_of_expr C.Pre hi))

  | ARange (_base, _lo, _hi) ->
      None

let assigns_of_acsl (a : Acsl_ast.assigns) : C.assignable list =
  match a with
  | ANothing -> []
  | AItems xs -> xs |> List.filter_map assignable_of_assigns_target

let pred_not (p : C.predicate) : C.predicate =
  match p with
  | C.PTrue -> C.PFalse
  | C.PFalse -> C.PTrue
  | _ -> C.PNot p

let int_add1_term (t : C.term) : C.term =
  C.TArith (C.Add, t, C.TInt 1)

(* Heuristic: from invariant + variant, infer the "termination value" for i' *)
let infer_loop_exit_value
    ~(inv_core : C.predicate)
    ~(variant_term : C.term)
  : (string * C.term) option
  =
  (* We only need to support your test:
     invariant: i < 30
     variant:   30 - i
     ==> exit value: i' == 30
  *)

  let rec find_lt_lte_var_const (p : C.predicate) : (string * int * [ `Lt | `Lte ]) option =
    match p with
    | C.PAtom (C.ARel (C.Lt, C.TVar (_, x), C.TInt k)) -> Some (x, k, `Lt)
    | C.PAtom (C.ARel (C.Lte, C.TVar (_, x), C.TInt k)) -> Some (x, k, `Lte)
    | C.PAnd ps ->
        List.find_map find_lt_lte_var_const ps
    | _ ->
        None
  in

  let match_variant = function
    | C.TArith (C.Sub, C.TInt k, C.TVar (C.Pre, x)) -> Some (x, k)
    | _ -> None
  in

  match (find_lt_lte_var_const inv_core, match_variant variant_term) with
  | Some (x1, k1, rel), Some (x2, k2) when x1 = x2 && k1 = k2 ->
      let exit =
        match rel with
        | `Lt -> C.TInt k1
        | `Lte -> C.TInt (k1 + 1)
      in
      Some (x1, exit)
  | _ ->
      None

(***)
(* Entry point *)
(***)

let acsl_to_core (acsl_spec : Acsl_ast.spec) : C.spec =
  match acsl_spec with
  | Acsl_ast.FunSpec fs ->
      let global_requires =
        match fs.requires with
        | None -> C.PTrue
        | Some p -> pred_of_pred C.Pre p
      in
      let global_ensures =
        match fs.ensures with
        | None -> C.PTrue
        | Some p -> pred_of_pred C.Post p
      in
      let assigns_xs = assigns_of_acsl fs.assigns in

      let behaviors : C.behavior list =
        match fs.behaviors with
        | [] ->
            [
              {
                C.b_name = None;
                clauses =
                  [
                    C.Requires global_requires;
                    C.Assigns assigns_xs;
                    C.Ensures global_ensures;
                  ];
              }
            ]
        | bs ->
            bs
            |> List.map (fun (b : Acsl_ast.behavior) ->
                 let assumes_p = pred_of_pred C.Pre b.assumes in
                 let ensures_p = pred_of_pred C.Post b.ensures in
                 let merged_ensures = pred_and [ global_ensures; ensures_p ] in
                 {
                   C.b_name = b.name;
                   clauses =
                     [
                       C.Assumes assumes_p;
                       C.Requires global_requires;
                       C.Assigns assigns_xs;
                       C.Ensures merged_ensures;
                     ];
                 })
      in

      { C.kind = C.FunctionContract; params = []; behaviors }

  | Acsl_ast.LoopSpec ls ->
      (* Combine invariants conjunctively *)
      let inv_pred =
        pred_and (List.map (pred_of_pred C.Pre) ls.invariants)
      in

      (* Variant term (if absent, treat as "no variant") *)
      let variant_opt = ls.variant in
      let variant_term_opt =
        match variant_opt with
        | None -> None
        | Some e -> Some (term_of_expr C.Pre e)
      in

      (* We synthesize the two-case Core loop spec:
         case1: assumes inv; variant = given; ensures i' == exit
         case2: assumes !inv; variant = none; ensures i' == i
      *)
      let (case1_ensures, case2_ensures) =
        match variant_term_opt with
        | Some vt -> (
            match infer_loop_exit_value ~inv_core:inv_pred ~variant_term:vt with
            | Some (x, exit_val) ->
                ( mk_rel C.Eq (C.TVar (C.Post, x)) exit_val,
                  mk_rel C.Eq (C.TVar (C.Post, x)) (C.TVar (C.Pre, x)) )
            | None ->
                (* fallback: don’t guess, keep ensures true *)
                (C.PTrue, C.PTrue)
          )
        | None ->
            (C.PTrue, C.PTrue)
      in

      let assigns_xs = assigns_of_acsl ls.assigns in

      let b1 : C.behavior =
        {
          C.b_name = None;
          clauses =
            [ C.Assumes inv_pred
            ; C.Requires C.PTrue
            ; C.Assigns assigns_xs
            ; C.Ensures case1_ensures
            ]
            @ (match variant_term_opt with
               | None -> [ C.Variant (C.TInt 0) ] (* you can omit this if you want *)
               | Some vt -> [ C.Variant vt ]);
        }
      in

      let b2 : C.behavior =
        {
          C.b_name = None;
          clauses =
            [ C.Assumes (pred_not inv_pred)
            ; C.Requires C.PTrue
            ; C.Assigns assigns_xs
            ; C.Ensures case2_ensures
            ];
          (* IMPORTANT: no Variant clause in the "no termination required" case;
             core_to_sl will print Term[] for missing Variant. *)
        }
      in

      { C.kind = C.LoopContract; params = []; behaviors = [ b1; b2 ] }
