(* core_to_sl.ml *)

open Core
module S = Sl_ast

let extract_core_ensures (b : Core.behavior) : Core.predicate =
  let rec go = function
    | [] -> Core.PTrue
    | Ensures p :: _ -> p
    | _ :: tl -> go tl
  in
  go b.clauses

let extract_swap_eqs (p : Core.predicate) : (string * string) list =
  let rec atoms acc = function
    | Core.PAnd ps -> List.fold_left atoms acc ps
    | Core.PAtom (Core.ARel (Core.Eq, Core.THeap (Core.Post, a), Core.THeap (Core.Pre, b))) ->
        (a, b) :: acc
    | Core.PAtom (Core.ARel (Core.Eq, Core.THeap (Core.Pre, b), Core.THeap (Core.Post, a))) ->
        (a, b) :: acc
    | _ -> acc
  in
  atoms [] p |> List.rev

let rec sl_expr_of_core_term (t : Core.term) : Sl_ast.expr =
  match t with
  | Core.TInt n -> Sl_ast.EConstInt n
  | Core.TVar (_, x) -> Sl_ast.EVar x
  | Core.TResult -> Sl_ast.EResult

  | Core.TArith (Core.Sub, Core.TInt 0, t2) ->
      Sl_ast.EUnop (Sl_ast.UNeg, sl_expr_of_core_term t2)

  | Core.TArith (Core.Add, a, b) ->
      Sl_ast.EBinop (Sl_ast.BAdd, sl_expr_of_core_term a, sl_expr_of_core_term b)

  | Core.TArith (Core.Sub, a, b) ->
      Sl_ast.EBinop (Sl_ast.BSub, sl_expr_of_core_term a, sl_expr_of_core_term b)

  | Core.TArith (Core.Mul, a, b) ->
      Sl_ast.EBinop (Sl_ast.BMul, sl_expr_of_core_term a, sl_expr_of_core_term b)

  | Core.TArith (Core.Div, a, b) ->
      Sl_ast.EBinop (Sl_ast.BDiv, sl_expr_of_core_term a, sl_expr_of_core_term b)

  | Core.TApp ("not", [ x ]) ->
      Sl_ast.EUnop (Sl_ast.UNot, sl_expr_of_core_term x)

  | _ ->
      failwith "core_to_sl: unsupported pure term"


let rec sl_of_core_pred (p : Core.predicate) : Sl_ast.sl =
  match p with
  | Core.PTrue -> Sl_ast.STrue
  | Core.PFalse -> Sl_ast.SFalse

  | Core.PAtom (Core.ARel (rel, a, b)) ->
      let bop =
        match rel with
        | Core.Eq  -> Sl_ast.BEq
        | Core.Neq -> Sl_ast.BNeq
        | Core.Lt  -> Sl_ast.BLt
        | Core.Lte -> Sl_ast.BLe
        | Core.Gt  -> Sl_ast.BGt
        | Core.Gte -> Sl_ast.BGe
      in
      Sl_ast.SPure
        (Sl_ast.EBinop (bop, sl_expr_of_core_term a, sl_expr_of_core_term b))

  | Core.PNot q ->
      Sl_ast.SNot (sl_of_core_pred q)

  | Core.PAnd qs ->
      Sl_ast.SAnd (List.map sl_of_core_pred qs)

  | Core.POr qs ->
      Sl_ast.SOr (List.map sl_of_core_pred qs)

  | Core.PImplies (a, b) ->
      Sl_ast.SImplies (sl_of_core_pred a, sl_of_core_pred b)

  | _ ->
      failwith "core_to_sl: unsupported predicate form"
    
let core_to_sl (core_spec : Core.spec) : string =
  match core_spec.kind with
  | Core.LoopContract ->
      failwith "Core_to_sl: LoopContract not supported yet"

  | Core.FunctionContract -> (
      match core_spec.behaviors with
      | [] -> failwith "Core_to_sl: empty behaviors"
      | b0 :: _ ->
          let ensures_p = extract_core_ensures b0 in
          let swap_pairs = extract_swap_eqs ensures_p in

          (* Case 1: heap swap / old sugar *)
          if swap_pairs <> [] then
            let eqs =
              swap_pairs
              |> List.map (fun (a, b) -> "(*" ^ a ^ ")==\\old(*" ^ b ^ ")")
              |> String.concat " && "
            in
            "ens " ^ eqs ^ ";"

          (* Case 2: pure ensures *)
          else
            let sl = sl_of_core_pred ensures_p in
            "ens " ^ Sl_ast_printer.string_of_sl sl ^ ";"
    )

