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

let rec sl_flatten_or (xs : S.sl list) : S.sl list =
  match xs with
  | [] -> []
  | S.SFalse :: tl -> sl_flatten_or tl
  | S.SOr ys :: tl -> sl_flatten_or (ys @ tl)
  | x :: tl -> x :: sl_flatten_or tl

let sl_and (xs : S.sl list) : S.sl =
  let xs = sl_flatten_and xs in
  match xs with
  | [] -> S.STrue
  | [ x ] -> x
  | _ -> S.SAnd xs

let sl_or (xs : S.sl list) : S.sl =
  let xs = sl_flatten_or xs in
  match xs with
  | [] -> S.SFalse
  | [ x ] -> x
  | _ -> S.SOr xs

(***)
(* Core.rel / Core.arith_op -> SL binop *)
(***)

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

(***)
(* Term -> SL expr *)
(***)

type expr_ctx =
  | CReq
  | CEns

let rec expr_of_term ?(ctx=CReq) (t : Core.term) : S.expr =
  match t with
  | TInt n -> S.EConstInt n
  | TResult -> S.EResult

  | TPtr p ->
      S.EVar p

  | TVar (ph, x) ->
      begin match ctx with
      | CReq -> S.EVar x
      | CEns -> if ph = Pre then S.EOld (S.EVar x) else S.EVar x
      end

  | THeap (ph, p) ->
      let d = S.EDeref (S.EVar p) in
      begin match ctx with
      | CReq -> d
      | CEns -> if ph = Pre then S.EOld d else d
      end

  | TLoad (ph, addr) ->
      let d = S.EDeref (expr_of_term ~ctx:CReq addr) in
      begin match ctx with
      | CReq -> d
      | CEns -> if ph = Pre then S.EOld d else d
      end

  | TIndex (ph, base, idx) ->
      let base_e = expr_of_term ~ctx:CReq base in
      let idx_e = expr_of_term ~ctx:CReq idx in
      let d = S.EDeref (S.EBinop (S.BAdd, base_e, idx_e)) in
      begin match ctx with
      | CReq -> d
      | CEns -> if ph = Pre then S.EOld d else d
      end

  | TArith (Core.Sub, Core.TInt 0, t2) ->
      S.EUnop (S.UNeg, expr_of_term ~ctx t2)

  | TArith (op, t1, t2) ->
      S.EBinop (sl_binop_of_arith op, expr_of_term ~ctx t1, expr_of_term ~ctx t2)

  | TApp (f, args) ->
      S.EApp (f, List.map (expr_of_term ~ctx) args)

(***)
(* Predicate -> SL *)
(***)

let is_acsl_only_pred_name (nm : string) : bool =
  nm = "valid"
  || nm = "valid_read"
  || nm = "valid_read_range"
  || nm = "\\valid"
  || nm = "\\valid_read"

let rec sl_of_core_pred ?(ctx=CReq) (p : Core.predicate) : S.sl =
  match p with
  | PTrue -> S.STrue
  | PFalse -> S.SFalse

  | PAtom (ARel (r, t1, t2)) ->
      S.SPure (S.EBinop (sl_binop_of_rel r, expr_of_term ~ctx t1, expr_of_term ~ctx t2))

  | PAtom (APred (name, args)) ->
      if is_acsl_only_pred_name name then
        S.STrue
      else
        (* best-effort: treat as boolean term application *)
        S.SPure (S.EApp (name, List.map (expr_of_term ~ctx) args))

  | PNot q ->
      S.SNot (sl_of_core_pred ~ctx q)

  | PAnd ps ->
      ps |> List.map (sl_of_core_pred ~ctx) |> sl_and

  | POr ps ->
      ps |> List.map (sl_of_core_pred ~ctx) |> sl_or

  | PImplies (a, b) ->
      S.SImplies (sl_of_core_pred ~ctx a, sl_of_core_pred ~ctx b)

  | PForall (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, None)) bs in
      S.SForall (bs', sl_of_core_pred ~ctx body)

  | PExists (bs, body) ->
      let bs' = List.map (fun (b : Core.binder) -> (b.b_name, None)) bs in
      S.SExists (bs', sl_of_core_pred ~ctx body)

(***)
(* Spec -> SL string *)
(***)

let core_to_sl (s : Core.spec) : string =
  let all_clauses = s.behaviors |> List.concat_map (fun b -> b.clauses) in

  let req_ps =
    all_clauses |> List.filter_map (function Requires p -> Some p | _ -> None)
  in
  let ens_ps =
    all_clauses |> List.filter_map (function Ensures p -> Some p | _ -> None)
  in

  let req_p =
    match req_ps with
    | [] -> Core.PTrue
    | [p] -> p
    | ps -> Core.PAnd ps
  in

  let ens_p =
    match ens_ps with
    | [] -> Core.PTrue
    | [p] -> p
    | ps -> Core.PAnd ps
  in

  let req_sl = sl_of_core_pred ~ctx:CReq req_p in
  let ens_sl = sl_of_core_pred ~ctx:CEns ens_p in

  let body =
    (match req_sl with
     | S.STrue -> []
     | _ -> [ S.CReq req_sl ])
    @
    (match ens_sl with
     | S.STrue -> []
     | _ -> [ S.CEns ens_sl ])
  in

  let spec : S.spec =
    { S.ret = None; behaviors = [ { S.name = None; assumes = S.STrue; body } ] }
  in
  Sl_ast_printer.string_of_spec spec
