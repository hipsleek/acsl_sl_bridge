(* core_to_acsl.ml *)

open Core
module A = Acsl_ast

type ctx =
  | CRequires
  | CEnsures
  | CLoop
  | CLoopRel

let binop_of_rel : Core.rel -> A.binop = function
  | Eq -> A.BEq
  | Neq -> A.BNeq
  | Lt -> A.BLt
  | Lte -> A.BLe
  | Gt -> A.BGt
  | Gte -> A.BGe

let binop_of_arith : Core.arith_op -> A.binop = function
  | Add -> A.BAdd
  | Sub -> A.BSub
  | Mul -> A.BMul
  | Div -> A.BDiv

let rec expr_of_core (c : ctx) (t : Core.term) : A.expr =
  match t with
  | TInt n -> A.EConstInt n
  | TResult -> A.EResult

  | TPtr p -> A.EVar p

  | TVar (ph, x) -> (
      match c with
      | CLoop -> A.EVar x
      | CLoopRel ->
          (match ph with
           | Pre -> A.EAt (A.EVar x, A.LoopEntry)
           | Post -> A.EVar x)
      | CRequires -> A.EVar x
      | CEnsures -> A.EVar x)

  | THeap (ph, p) -> (
      let deref = A.EDeref (A.EVar p) in
      match c with
      | CLoop -> deref
      | CLoopRel ->
          (match ph with
           | Pre -> A.EAt (deref, A.LoopEntry)
           | Post -> deref)
      | CRequires -> deref
      | CEnsures ->
          (match ph with
           | Post -> deref
           | Pre -> A.EOld deref))

  | TArith (Core.Sub, Core.TInt 0, t2) ->
    A.EUnop (A.UNeg, expr_of_core c t2)

  | TArith (op, t1, t2) ->
      A.EBinop (binop_of_arith op, expr_of_core c t1, expr_of_core c t2)

  | TApp (f, args) ->
      A.EApp (f, List.map (expr_of_core c) args)

  | TIndex (ph, a, idx) ->
      let e = A.EIndex (expr_of_core c a, expr_of_core c idx) in
      (match c with
       | CEnsures ->
           (match ph with
            | Pre -> A.EOld e
            | Post -> e)
       | CLoopRel ->
           (match ph with
            | Pre -> A.EAt (e, A.LoopEntry)
            | Post -> e)
       | CRequires
       | CLoop ->
           e)

  | TLoad (ph, addr) -> (
      let a = expr_of_core c addr in
      match c with
      | CEnsures ->
          (match ph with
           | Post -> A.EDeref a
           | Pre -> A.EOld (A.EDeref a))
      | CLoopRel ->
          (match ph with
           | Post -> A.EDeref a
           | Pre -> A.EAt (A.EDeref a, A.LoopEntry))
      | CLoop
      | CRequires ->
          A.EDeref a)

let sort_of_core_ty_opt (ty : string option) : A.sort option =
  match ty with
  | None -> None
  | Some "int" -> Some A.SInt
  | Some "integer" -> Some A.SInt
  | Some "bool" -> Some A.SBool
  | Some "boolean" -> Some A.SBool
  | Some "ptr" -> Some A.SPtr
  | Some s -> Some (A.SUser s)
  
let rec pred_of_core (c : ctx) (p : Core.predicate) : A.pred =
  match p with
  | PTrue -> A.PTrue
  | PFalse -> A.PFalse

  | PAtom (ARel (r, t1, t2)) ->
      A.PCmp (binop_of_rel r, expr_of_core c t1, expr_of_core c t2)

  | PAtom (APred (name, args)) ->
      if name = "valid" then
        (match args with
         | [ TPtr v ] -> A.PValid (A.EVar v)
         | [ t ] -> A.PValid (expr_of_core c t)
         | _ -> A.PApp ("\\valid", List.map (expr_of_core c) args))
      else if name = "valid_read_range" then
        (match args with
         | [ base; lo; hi ] ->
             let base' = expr_of_core c base in
             let lo' = expr_of_core c lo in
             let hi' = expr_of_core c hi in
             let ptr = A.EBinop (A.BAdd, base', A.ERange (lo', hi')) in
             A.PValidRead ptr
         | _ ->
             A.PApp ("\\valid_read", List.map (expr_of_core c) args))
      else if name = "valid_range" then
        (match args with
        | [ base; lo; hi ] ->
            let base' = expr_of_core c base in
            let lo' = expr_of_core c lo in
            let hi' = expr_of_core c hi in
            let ptr = A.EBinop (A.BAdd, base', A.ERange (lo', hi')) in
            A.PValid ptr
        | _ ->
            A.PApp ("\\valid", List.map (expr_of_core c) args))

      else
        A.PApp (name, List.map (expr_of_core c) args)

  | PNot p1 -> A.PNot (pred_of_core c p1)
  | PAnd ps -> A.PAnd (List.map (pred_of_core c) ps)
  | POr ps -> A.POr (List.map (pred_of_core c) ps)
  | PImplies (p1, p2) -> A.PImplies (pred_of_core c p1, pred_of_core c p2)
  | PForall (bs, body) ->
    let bs' =
      List.map
        (fun (b : Core.binder) -> (b.b_name, sort_of_core_ty_opt b.b_ty))
        bs
    in
    A.PForall (bs', pred_of_core c body)
  | PExists (bs, body) ->
      let bs' =
        List.map
          (fun (b : Core.binder) -> (b.b_name, sort_of_core_ty_opt b.b_ty))
          bs
      in
      A.PExists (bs', pred_of_core c body)

let find_first (f : 'a -> 'b option) (xs : 'a list) : 'b option =
  let rec go = function
    | [] -> None
    | x :: tl -> (match f x with Some y -> Some y | None -> go tl)
  in
  go xs

let all_of (f : 'a -> 'b option) (xs : 'a list) : 'b list =
  xs |> List.filter_map f

let clause_assumes = function Assumes p -> Some p | _ -> None
let clause_requires = function Requires p -> Some p | _ -> None
let clause_ensures = function Ensures p -> Some p | _ -> None
let clause_assigns = function Assigns xs -> Some xs | _ -> None

let rec split_top_and_core (p : Core.predicate) : Core.predicate list =
  match p with
  | Core.PAnd ps -> List.concat_map split_top_and_core ps
  | _ -> [ p ]

let uniq_core_preds (ps : Core.predicate list) : Core.predicate list =
  ps |> List.sort_uniq Stdlib.compare

let pred_and_core (ps : Core.predicate list) : Core.predicate =
  let atoms =
    ps
    |> List.concat_map split_top_and_core
    |> List.filter (fun p -> p <> Core.PTrue)
    |> uniq_core_preds
  in
  match atoms with
  | [] -> Core.PTrue
  | [ p ] -> p
  | _ -> Core.PAnd atoms

let uniq_preserve (xs : 'a list) : 'a list =
  let rec go seen acc = function
    | [] -> List.rev acc
    | x :: tl ->
        if List.mem x seen then go seen acc tl
        else go (x :: seen) (x :: acc) tl
  in
  go [] [] xs

let normalize_pred_list (ps : A.pred list) : A.pred list =
  ps
  |> List.filter (fun p -> p <> A.PTrue)
  |> uniq_preserve

let pred_and_acsl (ps : A.pred list) : A.pred =
  let atoms =
    ps
    |> List.concat_map (fun p -> match p with A.PAnd xs -> xs | _ -> [ p ])
    |> List.filter (fun p -> p <> A.PTrue)
    |> uniq_preserve
  in
  match atoms with
  | [] -> A.PTrue
  | [ p ] -> p
  | _ -> A.PAnd atoms


let uniq_assignables (xs : Core.assignable list) : Core.assignable list =
  let key_of = function
    | AsVar v -> "V:" ^ v
    | AsHeap p -> "H:" ^ p
    | AsRange (p, _lo, _hi) -> "R:" ^ p
    | AsTerm t -> "T:" ^ string_of_int (Stdlib.Hashtbl.hash t)
  in
  let module S = Set.Make (String) in
  let rec go seen acc = function
    | [] -> List.rev acc
    | x :: tl ->
        let k = key_of x in
        if S.mem k seen then go seen acc tl
        else go (S.add k seen) (x :: acc) tl
  in
  go S.empty [] xs

let assigns_target_of_core (a : Core.assignable) : A.assigns_target option =
  match a with
  | AsVar v -> Some (A.AVar v)
  | AsHeap p -> Some (A.ADeref (A.EVar p))
  | AsRange (p, lo, hi) ->
      let lo' = expr_of_core CLoop lo in
      let hi' = expr_of_core CLoop hi in
      Some (A.ARange (A.EVar p, lo', hi'))
  | AsTerm t ->
      (* best-effort: print as "*t" if caller used an address-like term; otherwise include the term directly *)
      let e = expr_of_core CEnsures t in
      Some (A.ADeref e)

let assigns_of_core (xs : Core.assignable list) : A.assigns =
  let ts = xs |> List.filter_map assigns_target_of_core in
  match ts with
  | [] -> A.ANothing
  | _ -> A.AItems ts

let is_global_req_only_behavior (b : Core.behavior) : bool =
  let assumes_ps = b.clauses |> all_of clause_assumes in
  let ensures_ps = b.clauses |> all_of clause_ensures in
  let requires_p =
    b.clauses |> find_first clause_requires |> Option.value ~default:Core.PTrue
  in
  let assigns_xs =
    b.clauses |> find_first clause_assigns |> Option.value ~default:[]
  in
  let assumes_is_true =
    match assumes_ps with
    | [] -> true
    | [ Core.PTrue ] -> true
    | _ -> false
  in
  let ensures_is_true =
    match ensures_ps with
    | [] -> true
    | [ Core.PTrue ] -> true
    | _ -> false
  in
  let requires_is_nontrivial = requires_p <> Core.PTrue in
  let assigns_is_empty = assigns_xs = [] in
  assumes_is_true && ensures_is_true && requires_is_nontrivial && assigns_is_empty

let fun_spec_of_core (s : Core.spec) : A.fun_spec =
  let all_clauses = s.behaviors |> List.concat_map (fun b -> b.clauses) in

  (* --- requires --- *)
  let reqs =
    all_clauses |> List.filter_map (function Requires p -> Some p | _ -> None)
  in
  let req_pred = pred_and_core reqs in
  let requires =
    let p = pred_of_core CRequires req_pred in
    if p = A.PTrue then None else Some p
  in

  (* --- assigns --- *)
  let assigns_list =
    all_clauses
    |> List.filter_map (function Assigns xs -> Some xs | _ -> None)
    |> List.concat
    |> uniq_assignables
  in
  let assigns = assigns_of_core assigns_list in

  (* Filter out the special “global requires only” behavior if it exists *)
  let candidate_behaviors =
    s.behaviors |> List.filter (fun b -> not (is_global_req_only_behavior b))
  in

  (* Policy for backwards-compatibility with tests:
     - If there is at least one NAMED behavior, emit behaviors.
     - Otherwise (all b_name=None), emit NO behaviors, and lift ensures to top-level ensures.
  *)
  let has_named_behavior =
    candidate_behaviors |> List.exists (fun b -> b.b_name <> None)
  in

  let behaviors =
    if has_named_behavior then
      candidate_behaviors
      |> List.map (fun b ->
           let assumes =
             b.clauses
             |> all_of clause_assumes
             |> List.map (pred_of_core CRequires)
             |> normalize_pred_list
             |> pred_and_acsl
           in
           let ensures =
             b.clauses
             |> all_of clause_ensures
             |> List.map (pred_of_core CEnsures)
             |> normalize_pred_list
             |> pred_and_acsl
           in
           { A.name = b.b_name; assumes; ensures })
    else
      []
  in

  (* Top-level ensures only when we did NOT emit behaviors *)
  let ensures =
    if behaviors = [] then
      let es =
        all_clauses |> List.filter_map (function Ensures p -> Some p | _ -> None)
      in
      let p = pred_of_core CEnsures (pred_and_core es) in
      if p = A.PTrue then None else Some p
    else
      None
  in

  (* Emit complete/disjoint only when we emitted multiple behaviors *)
  let complete_behaviors = has_named_behavior && List.length behaviors > 1 in
  let disjoint_behaviors = has_named_behavior && List.length behaviors > 1 in

  {
    A.requires;
    assigns;
    behaviors;
    ensures;
    complete_behaviors;
    disjoint_behaviors;
  }


let rec split_top_and (p : Core.predicate) : Core.predicate list =
  match p with
  | Core.PAnd ps -> List.concat_map split_top_and ps
  | _ -> [ p ]

let rec term_mentions_result (t : Core.term) : bool =
  match t with
  | Core.TResult -> true
  | Core.TInt _ -> false
  | Core.TPtr _ -> false
  | Core.TVar _ -> false
  | Core.THeap _ -> false
  | Core.TArith (_, a, b) -> term_mentions_result a || term_mentions_result b
  | Core.TApp (_, args) -> List.exists term_mentions_result args
  | Core.TIndex (_, a, idx) -> term_mentions_result a || term_mentions_result idx
  | Core.TLoad (_, addr) -> term_mentions_result addr

let rec pred_mentions_result (p : Core.predicate) : bool =
  match p with
  | Core.PTrue | Core.PFalse -> false
  | Core.PAtom (Core.ARel (_, t1, t2)) -> term_mentions_result t1 || term_mentions_result t2
  | Core.PAtom (Core.APred (_, args)) -> List.exists term_mentions_result args
  | Core.PNot q -> pred_mentions_result q
  | Core.PAnd qs | Core.POr qs -> List.exists pred_mentions_result qs
  | Core.PImplies (a, b) -> pred_mentions_result a || pred_mentions_result b
  | Core.PForall (_, body) | Core.PExists (_, body) -> pred_mentions_result body

let rec term_has_phase (want : Core.phase) (t : Core.term) : bool =
  match t with
  | Core.TInt _ -> false
  | Core.TResult -> false
  | Core.TPtr _ -> false
  | Core.TVar (ph, _) -> ph = want
  | Core.THeap (ph, _) -> ph = want
  | Core.TArith (_, t1, t2) -> term_has_phase want t1 || term_has_phase want t2
  | Core.TApp (_, args) -> List.exists (term_has_phase want) args
  | Core.TIndex (ph, a, idx) -> ph = want || term_has_phase want a || term_has_phase want idx
  | Core.TLoad (ph, addr) -> ph = want || term_has_phase want addr

let rec pred_has_phase (want : Core.phase) (p : Core.predicate) : bool =
  match p with
  | Core.PTrue | Core.PFalse -> false
  | Core.PAtom (Core.ARel (_, t1, t2)) -> term_has_phase want t1 || term_has_phase want t2
  | Core.PAtom (Core.APred (_, args)) -> List.exists (term_has_phase want) args
  | Core.PNot p1 -> pred_has_phase want p1
  | Core.PAnd ps | Core.POr ps -> List.exists (pred_has_phase want) ps
  | Core.PImplies (p1, p2) -> pred_has_phase want p1 || pred_has_phase want p2
  | Core.PForall (_, body) | Core.PExists (_, body) -> pred_has_phase want body

let pred_is_relational_pre_post (p : Core.predicate) : bool =
  pred_has_phase Core.Pre p && pred_has_phase Core.Post p

let is_liftable_relational (p : Core.predicate) : bool =
  match p with
  | Core.PAtom (Core.ARel (Core.Eq, _t1, _t2)) ->
      pred_is_relational_pre_post p && not (pred_mentions_result p)
  | _ ->
      false

let loop_spec_of_core (s : Core.spec) : A.loop_spec =
  let chosen =
    match
      s.behaviors
      |> List.find_opt (fun b -> List.exists (function Variant _ -> true | _ -> false) b.clauses)
    with
    | Some b -> b
    | None ->
        (match s.behaviors with
         | b :: _ -> b
         | [] -> failwith "empty loop spec")
  in

  let assumes_invs =
    chosen.clauses
    |> all_of clause_assumes
    |> List.concat_map split_top_and
    |> List.map (pred_of_core CLoop)
    |> normalize_pred_list
  in

  let relational_ensures_invs =
    chosen.clauses
    |> all_of clause_ensures
    |> List.concat_map (fun p -> match p with Core.PAnd ps -> ps | _ -> [])
    |> List.filter is_liftable_relational
    |> List.map (pred_of_core CLoopRel)
    |> normalize_pred_list
  in

  let invariants = assumes_invs @ relational_ensures_invs in

  let assigns_list =
    match find_first (function Assigns xs -> Some xs | _ -> None) chosen.clauses with
    | None -> []
    | Some xs -> xs
  in
  let assigns = assigns_of_core assigns_list in

  let variant =
    match find_first (function Variant t -> Some t | _ -> None) chosen.clauses with
    | None -> None
    | Some t -> Some (expr_of_core CLoop t)
  in

  { A.invariants; assigns; variant }

let spec_to_acsl (s : Core.spec) : string =
  let acsl_spec : A.spec =
    match s.kind with
    | FunctionContract -> A.FunSpec (fun_spec_of_core s)
    | LoopContract -> A.LoopSpec (loop_spec_of_core s)
  in Acsl_ast_printer.string_of_spec acsl_spec

