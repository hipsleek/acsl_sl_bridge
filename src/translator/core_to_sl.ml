(* core_to_sl.ml *)

open Core
module S = Sl_ast

(***)
(* Utilities *)
(***) 

let rec sl_flatten_and (xs : S.sl list) : S.sl list =
  match xs with
  | [] -> []
  | S.STrue :: tl -> sl_flatten_and tl
  | S.SAnd ys :: tl -> sl_flatten_and (ys @ tl)
  | x :: tl -> x :: sl_flatten_and tl

let sl_and (xs : S.sl list) : S.sl =
  let xs = sl_flatten_and xs in
  match xs with
  | [] -> S.STrue
  | [ x ] -> x
  | _ -> S.SAnd xs

let rec sl_flatten_or (xs : S.sl list) : S.sl list =
  match xs with
  | [] -> []
  | S.SFalse :: tl -> sl_flatten_or tl
  | S.SOr ys :: tl -> sl_flatten_or (ys @ tl)
  | x :: tl -> x :: sl_flatten_or tl

let sl_or (xs : S.sl list) : S.sl =
  let xs = sl_flatten_or xs in
  match xs with
  | [] -> S.SFalse
  | [ x ] -> x
  | _ -> S.SOr xs

(***)
(* Core -> SL expr *)
(***) 

type expr_ctx = CReq | CEns

let sl_binop_of_rel : Core.rel -> S.binop = function
  | Eq -> S.BEq
  | Neq -> S.BNeq
  | Lt -> S.BLt
  | Lte -> S.BLe
  | Gt -> S.BGt
  | Gte -> S.BGe

let sl_binop_of_arith : Core.arith_op -> S.binop = function
  | Add -> S.BAdd
  | Sub -> S.BSub
  | Mul -> S.BMul
  | Div -> S.BDiv

let rec expr_of_term ?(ctx = CReq) (t : Core.term) : S.expr =
  match t with
  | TInt n -> S.EConstInt n
  | TResult -> S.EResult
  | TPtr p -> S.EVar p

  | TVar (ph, x) -> (
      match ctx with
      | CReq -> S.EVar x
      | CEns -> if ph = Pre then S.EOld (S.EVar x) else S.EVar x)

  | THeap (ph, p) ->
      let d = S.EDeref (S.EVar p) in
      (match ctx with
       | CReq -> d
       | CEns -> if ph = Pre then S.EOld d else d)

  | TLoad (ph, addr) ->
      let d = S.EDeref (expr_of_term ~ctx:CReq addr) in
      (match ctx with
       | CReq -> d
       | CEns -> if ph = Pre then S.EOld d else d)

  | TIndex (ph, base, idx) ->
      let base_e = expr_of_term ~ctx:CReq base in
      let idx_e = expr_of_term ~ctx:CReq idx in
      let d = S.EDeref (S.EBinop (S.BAdd, base_e, idx_e)) in
      (match ctx with
       | CReq -> d
       | CEns -> if ph = Pre then S.EOld d else d)

  | TArith (Core.Sub, Core.TInt 0, t2) ->
      (* Preserve unary negation in SL *)
      S.EUnop (S.UNeg, expr_of_term ~ctx t2)

  | TArith (op, t1, t2) ->
      S.EBinop (sl_binop_of_arith op, expr_of_term ~ctx t1, expr_of_term ~ctx t2)

  | TApp (f, args) ->
      S.EApp (f, List.map (expr_of_term ~ctx) args)

(***)
(* Core predicate -> SL sl *)
(***) 

let is_acsl_only_pred_name (nm : string) : bool =
  nm = "valid"
  || nm = "valid_read"
  || nm = "valid_read_range"
  || nm = "\\valid"
  || nm = "\\valid_read"

let rec sl_of_core_pred ?(ctx = CReq) (p : Core.predicate) : S.sl =
  match p with
  | PTrue -> S.STrue
  | PFalse -> S.SFalse

  | PAtom (ARel (r, t1, t2)) ->
      S.SPure (S.EBinop (sl_binop_of_rel r, expr_of_term ~ctx t1, expr_of_term ~ctx t2))

  | PAtom (APred (name, args)) ->
      if is_acsl_only_pred_name name then
        (* Drop ACSL-specific validity predicates in SL output *)
        S.STrue
      else if name = "bool" then
        (* Important: do NOT fail on “bool(term)” wrappers produced by acsl_to_core.
           Re-emit the term as a pure SL expression. *)
        match args with
        | [ t ] -> S.SPure (expr_of_term ~ctx t)
        | _ -> S.SPure (S.EApp (name, List.map (expr_of_term ~ctx) args))
      else
        S.SPure (S.EApp (name, List.map (expr_of_term ~ctx) args))

  | PNot q -> S.SNot (sl_of_core_pred ~ctx q)
  | PAnd ps -> sl_and (List.map (sl_of_core_pred ~ctx) ps)
  | POr ps -> sl_or (List.map (sl_of_core_pred ~ctx) ps)
  | PImplies (a, b) -> S.SImplies (sl_of_core_pred ~ctx a, sl_of_core_pred ~ctx b)

  | PForall (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, None)) bs in
      S.SForall (bs', sl_of_core_pred ~ctx body)

  | PExists (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, None)) bs in
      S.SExists (bs', sl_of_core_pred ~ctx body)

(***)
(* Clause pickers *)
(***) 

let find_first (f : 'a -> 'b option) (xs : 'a list) : 'b option =
  let rec go = function
    | [] -> None
    | x :: tl -> (match f x with Some y -> Some y | None -> go tl)
  in
  go xs

let clause_assumes = function Assumes p -> Some p | _ -> None
let clause_requires = function Requires p -> Some p | _ -> None
let clause_ensures = function Ensures p -> Some p | _ -> None
let clause_variant = function Variant t -> Some t | _ -> None


(***)
(* Spec -> SL *)
(***) 

let core_to_sl (s : Core.spec) : string =
  let behaviors : S.behavior list =
    s.behaviors
    |> List.map (fun (b : Core.behavior) ->
         let assumes_p =
           b.clauses |> find_first clause_assumes |> Option.value ~default:Core.PTrue
         in
         let requires_p =
           b.clauses |> find_first clause_requires |> Option.value ~default:Core.PTrue
         in
         let ensures_p =
           b.clauses |> find_first clause_ensures |> Option.value ~default:Core.PTrue
         in

         let assumes_sl = sl_of_core_pred ~ctx:CReq assumes_p in
         let req_sl = sl_of_core_pred ~ctx:CReq requires_p in
         let ens_sl = sl_of_core_pred ~ctx:CEns ensures_p in
         let variant_t_opt = b.clauses |> find_first clause_variant in
         let var_clause =
            match variant_t_opt with
            | None -> [ S.CVar None ]
            | Some t -> [ S.CVar (Some (expr_of_term ~ctx:CReq t)) ]
         in

         let body =
          (match req_sl with
          | S.STrue -> []
          | _ -> [ S.CReq req_sl ])
          @
          (match s.kind with
          | Core.LoopContract -> var_clause
          | Core.FunctionContract -> [])
          @
          (match ens_sl with
          | S.STrue -> []
          | _ -> [ S.CEns ens_sl ])
        in


         { S.name = b.b_name; assumes = assumes_sl; body })
  in

  let spec : S.spec = { S.ret = None; behaviors } in
  Sl_ast_printer.string_of_spec spec
