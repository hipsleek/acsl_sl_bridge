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

let p_atom (a : C.atom) : C.predicate = C.PAtom a
let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate = p_atom (C.ARel (r, t1, t2))

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

let rec term_of_expr (default_phase : C.phase) (e : Acsl_ast.expr) : C.term =
  match e with
  | EConstInt n -> C.TInt n
  | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
  | EResult -> C.TResult
  | EVar x -> C.TVar (default_phase, x)
  | ENull -> C.TApp ("NULL", [])

  | EOld e1 -> term_of_expr C.Pre e1

  | EAt (e1, lbl) ->
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

  | ERange (lo, hi) ->
      C.TApp ("range", [ term_of_expr default_phase lo; term_of_expr default_phase hi ])

  | EUnop (UNeg, e1) ->
      C.TArith (C.Sub, C.TInt 0, term_of_expr default_phase e1)

  | EUnop (UNot, e1) ->
      C.TApp ("not", [ term_of_expr default_phase e1 ])

  | EBinop (op, a, b) -> (
      match arith_of_binop op with
      | Some aop -> C.TArith (aop, term_of_expr default_phase a, term_of_expr default_phase b)
      | None ->
          (* keep structure, don’t overfit *)
          C.TApp ("binop", [ term_of_expr default_phase a; term_of_expr default_phase b ]) )

  | EApp (f, args) ->
      C.TApp (f, List.map (term_of_expr default_phase) args)

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

  | PAnd ps -> pred_and (List.map (pred_of_pred default_phase) ps)
  | POr ps -> C.POr (List.map (pred_of_pred default_phase) ps)
  | PNot q -> C.PNot (pred_of_pred default_phase q)
  | PImplies (a, b) -> C.PImplies (pred_of_pred default_phase a, pred_of_pred default_phase b)

  | PIff (a, b) ->
      pred_and
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
