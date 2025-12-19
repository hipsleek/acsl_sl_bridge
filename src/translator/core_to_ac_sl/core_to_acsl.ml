open Core
module A = Acsl_ast



type ctx = CRequires | CEnsures | CLoop

let binop_of_rel : Core.rel -> A.rel = function
  | Eq -> A.Eq | Neq -> A.Neq | Lt -> A.Lt | Lte -> A.Lte | Gt -> A.Gt | Gte -> A.Gte

let binop_of_arith : Core.arith_op -> A.binop = function
  | Add -> A.Add | Sub -> A.Sub | Mul -> A.Mul | Div -> A.Div

let rec aterm_of_core (c : ctx) (t : Core.term) : A.term =
  match t with
  | TInt n -> A.TInt n
  | TResult -> A.TResult

  | TPtr p ->
      
      A.TVar p

  | TVar (ph, x) -> (
      match c, ph with
      | (CRequires | CLoop), Pre -> A.TVar x
      | (CRequires | CLoop), Post -> A.TVar x
      | CEnsures, Post -> A.TVar x
      | CEnsures, Pre -> A.TOld (A.TVar x)
    )

  | THeap (ph, p) -> (
      let deref = A.TDeref (A.TVar p) in
      match c, ph with
      | (CRequires | CLoop), Pre -> deref
      | (CRequires | CLoop), Post -> deref
      | CEnsures, Post -> deref
      | CEnsures, Pre -> A.TOld deref
    )

  | TArith (op, t1, t2) ->
      A.TBinOp (binop_of_arith op, aterm_of_core c t1, aterm_of_core c t2)

  | TApp (f, args) ->
      A.TApp (f, List.map (aterm_of_core c) args)



let rec apred_of_core (c : ctx) (p : Core.predicate) : A.predicate =
  match p with
  | PTrue -> A.PTrue
  | PFalse -> A.PFalse

  | PAtom (ARel (r, t1, t2)) ->
      A.PRel (binop_of_rel r, aterm_of_core c t1, aterm_of_core c t2)

  | PAtom (APred (name, args)) ->
      
      if name = "valid" then
        match args with
        | [TPtr p] -> A.PApp ("\\valid", [A.TVar p])
        | [t] -> A.PApp ("\\valid", [aterm_of_core c t])
        | _ -> A.PApp ("\\valid", List.map (aterm_of_core c) args)
      else
        A.PApp (name, List.map (aterm_of_core c) args)

  | PNot p1 -> A.PNot (apred_of_core c p1)
  | PAnd ps -> A.PAnd (List.map (apred_of_core c) ps)
  | POr ps -> A.POr (List.map (apred_of_core c) ps)
  | PImplies (p1, p2) -> A.PImplies (apred_of_core c p1, apred_of_core c p2)

  | PForall (bs, body) ->
      let bs' =
        List.map (fun (b : Core.binder) -> (b.b_name, b.b_ty)) bs
      in
      A.PForall (bs', apred_of_core c body)

  | PExists (bs, body) ->
      let bs' =
        List.map (fun (b : Core.binder) -> (b.b_name, b.b_ty)) bs
      in
      A.PExists (bs', apred_of_core c body)




let aterm_of_assignable (a : Core.assignable) : A.term option =
  match a with
  | AsVar v -> Some (A.TVar v)
  | AsHeap p -> Some (A.TDeref (A.TVar p))
  | AsTerm t -> Some (aterm_of_core CEnsures t)
  | AsRange (_p, _lo, _hi) ->
      
      None

let assigns_of_core (xs : Core.assignable list) : A.assigns =
  let ts =
    xs
    |> List.filter_map aterm_of_assignable
  in
  match ts with
  | [] -> A.ANothing
  | _ -> A.AList ts



let find_first f (xs : 'a list) : 'b option =
  let rec go = function
    | [] -> None
    | x :: tl -> (match f x with Some y -> Some y | None -> go tl)
  in
  go xs

let all_of f (xs : 'a list) : 'b list =
  xs |> List.filter_map f

let clause_assumes = function Assumes p -> Some p | _ -> None
let clause_requires = function Requires p -> Some p | _ -> None
let clause_ensures = function Ensures p -> Some p | _ -> None
let clause_assigns = function Assigns xs -> Some xs | _ -> None
let clause_variant = function Variant t -> Some t | _ -> None

let normalize_pred_list (ps : A.predicate list) : A.predicate list =
  
  ps |> List.filter (fun p -> p <> A.PTrue)



let contract_of_core (s : Core.spec) : A.contract =
  (* Global requires/assigns: in your Core pipeline these are repeated in each behavior.
     We take the first occurrence as the global ones. *)
  let all_clauses = s.behaviors |> List.concat_map (fun b -> b.clauses) in

  let req_pred =
    match find_first (fun c -> match c with Requires p -> Some p | _ -> None) all_clauses with
    | None -> Core.PTrue
    | Some p -> p
  in
  let assigns_list =
    match find_first (fun c -> match c with Assigns xs -> Some xs | _ -> None) all_clauses with
    | None -> []
    | Some xs -> xs
  in

  let requires = [ apred_of_core CRequires req_pred ] |> normalize_pred_list in
  let assigns = assigns_of_core assigns_list in

  let behaviors =
    s.behaviors
    |> List.map (fun b ->
         let assumes =
           b.clauses |> all_of clause_assumes |> List.map (apred_of_core CRequires) |> normalize_pred_list
         in
         let ensures =
           b.clauses |> all_of clause_ensures |> List.map (apred_of_core CEnsures) |> normalize_pred_list
         in
         { A.b_name = b.b_name; b_assumes = assumes; b_ensures = ensures })
  in

  { A.requires = requires; assigns; behaviors }



let loop_contract_of_core (s : Core.spec) : A.loop_contract =
  (* Heuristic that matches your SL->ACSL loop tests:
     pick the behavior that carries a Variant clause (i.e. the "continuing" case). *)
  let chosen =
    match
      s.behaviors
      |> List.find_opt (fun b -> List.exists (function Variant _ -> true | _ -> false) b.clauses)
    with
    | Some b -> b
    | None -> (match s.behaviors with b :: _ -> b | [] -> failwith "empty loop spec")
  in

  let invs =
    chosen.clauses
    |> all_of clause_assumes
    |> List.map (apred_of_core CLoop)
    |> normalize_pred_list
  in

  let assigns_list =
    match find_first (fun c -> match c with Assigns xs -> Some xs | _ -> None) chosen.clauses with
    | None -> []
    | Some xs -> xs
  in
  let l_assigns = assigns_of_core assigns_list in

  let l_variant =
    match find_first (fun c -> match c with Variant t -> Some t | _ -> None) chosen.clauses with
    | None -> None
    | Some t -> Some (aterm_of_core CLoop t)
  in

  { A.l_invariants = invs; l_assigns; l_variant }



type out =
  | Contract of A.contract
  | LoopContract of A.loop_contract


let spec_to_acsl (s : Core.spec) : string =
  match s.kind with
  | FunctionContract ->
      let c = contract_of_core s in
      Acsl_ast_printer.acsl_contract c
  | LoopContract ->
      let lc = loop_contract_of_core s in
      Acsl_ast_printer.acsl_loop_contract lc
