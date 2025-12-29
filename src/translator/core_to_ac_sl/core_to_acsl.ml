open Core
module A = Acsl_ast

type ctx =
  | CRequires
  | CEnsures
  | CLoop
  | CLoopRel

let binop_of_rel : Core.rel -> A.rel = function
  | Eq -> A.Eq
  | Neq -> A.Neq
  | Lt -> A.Lt
  | Lte -> A.Lte
  | Gt -> A.Gt
  | Gte -> A.Gte

let binop_of_arith : Core.arith_op -> A.binop = function
  | Add -> A.Add
  | Sub -> A.Sub
  | Mul -> A.Mul
  | Div -> A.Div

let rec aterm_of_core (c : ctx) (t : Core.term) : A.term =
  match t with
  | TInt n -> A.TInt n
  | TResult -> A.TResult

  | TPtr p -> A.TVar p

  | TVar (ph, x) -> (
      match c with
      | CLoop -> A.TVar x
      | CLoopRel ->
          (match ph with
           | Pre -> A.TAt (A.TVar x, A.LoopEntry)
           | Post -> A.TVar x)
      | CRequires -> A.TVar x
      | CEnsures ->
          A.TVar x)

  | THeap (ph, p) -> (
      let deref = A.TDeref (A.TVar p) in
      match c with
      | CLoop -> deref
      | CLoopRel ->
          (match ph with
           | Pre -> A.TAt (deref, A.LoopEntry)
           | Post -> deref)
      | CRequires -> deref
      | CEnsures ->
          (match ph with
           | Post -> deref
           | Pre -> A.TOld deref))

  | TArith (op, t1, t2) ->
      A.TBinOp (binop_of_arith op, aterm_of_core c t1, aterm_of_core c t2)

  | TApp (f, args) ->
      A.TApp (f, List.map (aterm_of_core c) args)

  | TIndex (ph, a, idx) ->
      let t = A.TIndex (aterm_of_core c a, aterm_of_core c idx) in
      (match c with
       | CEnsures ->
           (match ph with
            | Pre -> A.TOld t
            | Post -> t)
       | CLoopRel ->
           (match ph with
            | Pre -> A.TAt (t, A.LoopEntry)
            | Post -> t)
       | CRequires
       | CLoop ->
           t)

  | TLoad (ph, addr) -> (
      let at = aterm_of_core c addr in
      match c with
      | CEnsures ->
          (match ph with
           | Post -> A.TDeref at
           | Pre -> A.TOld (A.TDeref at))
      | CLoopRel ->
          (match ph with
           | Post -> A.TDeref at
           | Pre -> A.TAt (A.TDeref at, A.LoopEntry))
      | CLoop
      | CRequires ->
          A.TDeref at)


let rec apred_of_core (c : ctx) (p : Core.predicate) : A.predicate =
  match p with
  | PTrue -> A.PTrue
  | PFalse -> A.PFalse

  | PAtom (ARel (r, t1, t2)) ->
      A.PRel (binop_of_rel r, aterm_of_core c t1, aterm_of_core c t2)

  | PAtom (APred (name, args)) ->
      if name = "valid" then
        match args with
        | [ TPtr p ] -> A.PApp ("\\valid", [ A.TVar p ])
        | [ t ] -> A.PApp ("\\valid", [ aterm_of_core c t ])
        | _ -> A.PApp ("\\valid", List.map (aterm_of_core c) args)
      else if name = "valid_read_range" then
        match args with
        | [ base; lo; hi ] ->
            let base' = aterm_of_core c base in
            let lo' = aterm_of_core c lo in
            let hi' = aterm_of_core c hi in
            let ptr_expr = A.TBinOp (A.Add, base', A.TRange (lo', hi')) in
            A.PApp ("\\valid_read", [ ptr_expr ])
        | _ ->
            A.PApp ("\\valid_read", List.map (aterm_of_core c) args)
      else
        A.PApp (name, List.map (aterm_of_core c) args)

  | PNot p1 -> A.PNot (apred_of_core c p1)
  | PAnd ps -> A.PAnd (List.map (apred_of_core c) ps)
  | POr ps -> A.POr (List.map (apred_of_core c) ps)
  | PImplies (p1, p2) -> A.PImplies (apred_of_core c p1, apred_of_core c p2)

  | PForall (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, b.b_ty)) bs in
      A.PForall (bs', apred_of_core c body)

  | PExists (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, b.b_ty)) bs in
      A.PExists (bs', apred_of_core c body)


let aterm_of_assignable (a : Core.assignable) : A.term option =
  match a with
  | AsVar v -> Some (A.TVar v)
  | AsHeap p -> Some (A.TDeref (A.TVar p))
  | AsTerm t -> Some (aterm_of_core CEnsures t)
  | AsRange (p, lo, hi) ->
      let lo' = aterm_of_core CLoop lo in
      let hi' = aterm_of_core CLoop hi in
      Some (A.TIndex (A.TVar p, A.TRange (lo', hi')))

let assigns_of_core (xs : Core.assignable list) : A.assigns =
  let ts = xs |> List.filter_map aterm_of_assignable in
  match ts with
  | [] -> A.ANothing
  | _ -> A.AList ts

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

let normalize_pred_list (ps : A.predicate list) : A.predicate list =
  ps
  |> List.filter (fun p -> p <> A.PTrue)
  |> List.sort_uniq Stdlib.compare

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
  | [p] -> p
  | _ -> Core.PAnd atoms

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
  let requires_is_nontrivial = (requires_p <> Core.PTrue) in
  let assigns_is_empty = (assigns_xs = []) in
  assumes_is_true && ensures_is_true && requires_is_nontrivial && assigns_is_empty

let contract_of_core (s : Core.spec) : A.contract =
  let all_clauses = s.behaviors |> List.concat_map (fun b -> b.clauses) in

  let reqs =
    all_clauses |> List.filter_map (function Requires p -> Some p | _ -> None)
  in
  let req_pred = pred_and_core reqs in

  let assigns_list =
    all_clauses
    |> List.filter_map (function Assigns xs -> Some xs | _ -> None)
    |> List.concat
    |> uniq_assignables
  in

  let requires =
    [ apred_of_core CRequires req_pred ] |> normalize_pred_list
  in
  let assigns = assigns_of_core assigns_list in

  let behaviors =
    s.behaviors
    |> List.filter (fun b -> not (is_global_req_only_behavior b))
    |> List.map (fun b ->
         let assumes =
           b.clauses
           |> all_of clause_assumes
           |> List.map (apred_of_core CRequires)
           |> normalize_pred_list
         in
         let ensures =
           b.clauses
           |> all_of clause_ensures
           |> List.map (apred_of_core CEnsures)
           |> normalize_pred_list
         in
         { A.b_name = b.b_name; b_assumes = assumes; b_ensures = ensures })
  in

  { A.requires = requires; assigns; behaviors }


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

let loop_contract_of_core (s : Core.spec) : A.loop_contract =
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
    |> List.map (apred_of_core CLoop)
    |> normalize_pred_list
  in

  let relational_ensures_invs =
    chosen.clauses
    |> all_of clause_ensures
    |> List.concat_map (fun p ->
         match p with
         | Core.PAnd ps -> ps
         | _ -> [])
    |> List.filter is_liftable_relational
    |> List.map (apred_of_core CLoopRel)
    |> normalize_pred_list
  in

  let invs = assumes_invs @ relational_ensures_invs in

  let assigns_list =
    match find_first (function Assigns xs -> Some xs | _ -> None) chosen.clauses with
    | None -> []
    | Some xs -> xs
  in
  let l_assigns = assigns_of_core assigns_list in

  let l_variant =
    match find_first (function Variant t -> Some t | _ -> None) chosen.clauses with
    | None -> None
    | Some t -> Some (aterm_of_core CLoop t)
  in

  { A.l_invariants = invs; l_assigns; l_variant }

let spec_to_acsl (s : Core.spec) : string =
  match s.kind with
  | FunctionContract ->
      let c = contract_of_core s in
      Acsl_ast_printer.acsl_contract c
  | LoopContract ->
      let lc = loop_contract_of_core s in
      Acsl_ast_printer.acsl_loop_contract lc
