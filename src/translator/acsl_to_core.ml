(* acsl_to_core.ml *)

open Acsl_ast
module C = Core

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

let sort_ty_of_sort_opt (s : Acsl_ast.sort option) : string option =
  match s with
  | None -> None
  | Some SInt -> Some "int"
  | Some SBool -> Some "bool"
  | Some SPtr -> Some "ptr"
  | Some (SUser u) -> Some u

let binders_of_acsl (bs : (ident * sort option) list) : C.binder list =
  List.map (fun (b_name, tyopt) -> { C.b_name; b_ty = sort_ty_of_sort_opt tyopt }) bs

let rec term_of_expr (default_phase : C.phase) (e : Acsl_ast.expr) : C.term =
  match e with
  | EConstInt n -> C.TInt n
  | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
  | EResult -> C.TResult
  | EVar x -> C.TVar (default_phase, x)
  | ENull -> C.TApp ("NULL", [])

  | EOld e1 -> term_of_expr C.Pre e1

  | EAt (e1, lbl) ->
      (* Best-effort phase handling:
         - LoopEntry corresponds to Pre
         - otherwise keep default_phase
      *)
      let ph =
        match lbl with
        | LoopEntry -> C.Pre
        | LoopCurrent -> default_phase
        | UserLabel _ -> default_phase
      in
      term_of_expr ph e1

  | EDeref (EVar p) ->
      C.THeap (default_phase, p)

  | EDeref addr ->
      C.TLoad (default_phase, term_of_expr default_phase addr)

  | EIndex (base, idx) ->
      C.TIndex (default_phase, term_of_expr default_phase base, term_of_expr default_phase idx)

  | EUnop (UNeg, e1) ->
      C.TArith (C.Sub, C.TInt 0, term_of_expr default_phase e1)

  | EUnop (UNot, e1) ->
      C.TApp ("not", [ term_of_expr default_phase e1 ])

  | EBinop (op, a, b) -> (
      match arith_of_binop op with
      | Some aop -> C.TArith (aop, term_of_expr default_phase a, term_of_expr default_phase b)
      | None ->
          C.TApp ("binop", [ term_of_expr default_phase a; term_of_expr default_phase b ]) )

  | EApp (f, args) ->
      C.TApp (f, List.map (term_of_expr default_phase) args)

  | ERange (lo, hi) ->
      C.TApp ("range", [ term_of_expr default_phase lo; term_of_expr default_phase hi ])

let p_atom (a : C.atom) : C.predicate = C.PAtom a

let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (r, t1, t2))

let rec pred_of_pred (default_phase : C.phase) (p : Acsl_ast.pred) : C.predicate =
  match p with
  | PTrue -> C.PTrue
  | PFalse -> C.PFalse

  | PCmp (op, a, b) -> (
      match rel_of_binop op with
      | Some r -> mk_rel r (term_of_expr default_phase a) (term_of_expr default_phase b)
      | None ->
          p_atom (C.APred ("bool", [ term_of_expr default_phase (EBinop (op, a, b)) ])) )

  | PApp (f, args) ->
      p_atom (C.APred (f, List.map (term_of_expr default_phase) args))

  | PAnd ps -> C.PAnd (List.map (pred_of_pred default_phase) ps)
  | POr ps -> C.POr (List.map (pred_of_pred default_phase) ps)
  | PNot q -> C.PNot (pred_of_pred default_phase q)
  | PImplies (a, b) -> C.PImplies (pred_of_pred default_phase a, pred_of_pred default_phase b)
  | PIff (a, b) ->
      C.PAnd
        [
          C.PImplies (pred_of_pred default_phase a, pred_of_pred default_phase b);
          C.PImplies (pred_of_pred default_phase b, pred_of_pred default_phase a);
        ]

  | PForall (bs, body) -> C.PForall (binders_of_acsl bs, pred_of_pred default_phase body)
  | PExists (bs, body) -> C.PExists (binders_of_acsl bs, pred_of_pred default_phase body)

  | PValid (EVar x) -> p_atom (C.APred ("valid", [ C.TPtr x ]))
  | PValid e -> p_atom (C.APred ("valid", [ term_of_expr default_phase e ]))

  | PValidRead e -> p_atom (C.APred ("valid_read", [ term_of_expr default_phase e ]))

let assignable_of_assigns_target (t : Acsl_ast.assigns_target) : C.assignable option =
  match t with
  | AVar v -> Some (C.AsVar v)
  | ADeref (EVar p) -> Some (C.AsHeap p)
  | ADeref e -> Some (C.AsTerm (term_of_expr C.Pre e))
  | ARange (EVar p, lo, hi) ->
      Some (C.AsRange (p, term_of_expr C.Pre lo, term_of_expr C.Pre hi))
  | ARange (_base, _lo, _hi) ->
      None

let assigns_of_acsl (a : Acsl_ast.assigns) : C.assignable list =
  match a with
  | ANothing -> []
  | AItems xs -> xs |> List.filter_map assignable_of_assigns_target

let acsl_to_core (acsl_spec : Acsl_ast.spec) : C.spec =
  match acsl_spec with
  | Acsl_ast.LoopSpec _ ->
      failwith "Not implemented yet: Acsl_to_core.acsl_to_core (LoopSpec)"

  | Acsl_ast.FunSpec fs ->
      let requires_p =
        match fs.requires with
        | None -> C.PTrue
        | Some p -> pred_of_pred C.Pre p
      in
      let ensures_p =
        match fs.ensures with
        | None -> C.PTrue
        | Some p -> pred_of_pred C.Post p
      in
      let assigns_xs = assigns_of_acsl fs.assigns in
      let b : C.behavior =
        {
          C.b_name = None;
          clauses =
            [
              C.Requires requires_p;
              C.Assigns assigns_xs;
              C.Ensures ensures_p;
            ];
        }
      in
      { C.kind = C.FunctionContract; params = []; behaviors = [ b ] }
