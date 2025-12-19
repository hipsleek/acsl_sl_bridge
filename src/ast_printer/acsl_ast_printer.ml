(* acsl_ast_printer.ml
   Printer for final ACSL AST.
   Goal: precedence-correct printing for terms/predicates + contract rendering.
*)

open Acsl_ast

let join sep xs = String.concat sep xs
let parens s = "(" ^ s ^ ")"
let comma_list xs = join ", " xs

(* ---------- Precedence ---------- *)

type prec =
  | PTop
  | PImpl
  | POr
  | PAnd
  | PRel
  | PAdd
  | PMul
  | PUnary
  | PAtom

let prec_to_int = function
  | PTop -> 0
  | PImpl -> 1
  | POr -> 2
  | PAnd -> 3
  | PRel -> 4
  | PAdd -> 5
  | PMul -> 6
  | PUnary -> 7
  | PAtom -> 8

let need_parens ctx here = prec_to_int here < prec_to_int ctx
let with_parens_if ctx here s = if need_parens ctx here then parens s else s

(* ---------- Operators ---------- *)

let string_of_binop : binop -> string = function
  | Eq -> "=="
  | Neq -> "!="
  | Lt -> "<"
  | Lte -> "<="
  | Gt -> ">"
  | Gte -> ">="
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

let string_of_rel : rel -> string = function
  | Eq -> "=="
  | Neq -> "!="
  | Lt -> "<"
  | Lte -> "<="
  | Gt -> ">"
  | Gte -> ">="

let prec_of_binop = function
  | Add | Sub -> PAdd
  | Mul | Div -> PMul
  | Eq | Neq | Lt | Lte | Gt | Gte -> PRel

(* ---------- Terms ---------- *)

let rec acsl_term ?(ctx=PTop) (t : term) : string =
  let (here, s) =
    match t with
    | TVar x -> (PAtom, x)
    | TInt n -> (PAtom, string_of_int n)
    | TResult -> (PAtom, "\\result")
    | TDeref t1 ->
        (PUnary, "*" ^ acsl_term ~ctx:PUnary t1)
    | TOld t1 ->
        (PAtom, "\\old(" ^ acsl_term ~ctx:PTop t1 ^ ")")
    | TApp (f, args) ->
        (PAtom, f ^ parens (args |> List.map (acsl_term ~ctx:PTop) |> comma_list))
    | TBinOp (op, t1, t2) ->
        let p = prec_of_binop op in
        let lhs = acsl_term ~ctx:p t1 in
        let rhs = acsl_term ~ctx:p t2 in
        (p, lhs ^ " " ^ string_of_binop op ^ " " ^ rhs)
  in
  with_parens_if ctx here s

(* ---------- Predicates ---------- *)

let prec_of_pred = function
  | PTrue | PFalse | PRel _ | PApp _ -> PAtom
  | PNot _ -> PUnary
  | PAnd _ -> PAnd
  | POr _ -> POr
  | PImplies _ -> PImpl
  | PForall _ | PExists _ -> PAtom

let conj xs =
  match xs with
  | [] -> "\\true"
  | [x] -> x
  | _ -> join " && " xs

let rec acsl_pred ?(ctx=PTop) (p : predicate) : string =
  let here = prec_of_pred p in
  let s =
    match p with
    | PTrue -> "\\true"
    | PFalse -> "\\false"
    | PRel (r, t1, t2) ->
        acsl_term ~ctx:PRel t1 ^ " " ^ string_of_rel r ^ " " ^ acsl_term ~ctx:PRel t2
    | PApp (name, args) ->
        name ^ parens (args |> List.map (acsl_term ~ctx:PTop) |> comma_list)
    | PNot p1 ->
        "!" ^ parens (acsl_pred ~ctx:PTop p1)
    | PAnd ps ->
        begin match ps with
        | [] -> "\\true"
        | [x] -> acsl_pred ~ctx:ctx x
        | _ -> ps |> List.map (acsl_pred ~ctx:PAnd) |> conj
        end
    | POr ps ->
        begin match ps with
        | [] -> "\\false"
        | [x] -> acsl_pred ~ctx:ctx x
        | _ -> ps |> List.map (acsl_pred ~ctx:POr) |> join " || "
        end
    | PImplies (p1, p2) ->
        parens (acsl_pred ~ctx:PImpl p1) ^ " ==> " ^ parens (acsl_pred ~ctx:PImpl p2)
    | PForall (bs, body) ->
        let bs_str =
          bs
          |> List.map (fun (x, ty) -> match ty with None -> x | Some t -> t ^ " " ^ x)
          |> comma_list
        in
        "\\forall " ^ bs_str ^ "; " ^ acsl_pred ~ctx:PTop body
    | PExists (bs, body) ->
        let bs_str =
          bs
          |> List.map (fun (x, ty) -> match ty with None -> x | Some t -> t ^ " " ^ x)
          |> comma_list
        in
        "\\exists " ^ bs_str ^ "; " ^ acsl_pred ~ctx:PTop body
  in
  with_parens_if ctx here s

(* ---------- Assigns ---------- *)

let acsl_assigns = function
  | ANothing -> "\\nothing"
  | AList ts ->
      begin match ts with
      | [] -> "\\nothing"
      | _ -> ts |> List.map (acsl_term ~ctx:PTop) |> comma_list
      end

(* ---------- Renderers (contracts) ---------- *)

let acsl_behavior (b : behavior) : string list =
  match b.b_name with
  | None ->
      let ensures = b.b_ensures |> List.map acsl_pred |> conj in
      [ "  ensures " ^ ensures ^ ";" ]
  | Some name ->
      let assumes = b.b_assumes |> List.map acsl_pred |> conj in
      let ensures = b.b_ensures |> List.map acsl_pred |> conj in
      [ "  behavior " ^ name ^ ":"
      ; "    assumes " ^ assumes ^ ";"
      ; "    ensures " ^ ensures ^ ";"
      ]

let acsl_contract (c : contract) : string =
  let requires = c.requires |> List.map acsl_pred |> conj in
  let assigns = acsl_assigns c.assigns in
  let body = c.behaviors |> List.concat_map acsl_behavior in
  join "\n" (["/*@"; "  requires " ^ requires ^ ";"; "  assigns " ^ assigns ^ ";"]
             @ body @ ["*/"])

let acsl_loop_contract (lc : loop_contract) : string =
  let invs =
    match lc.l_invariants with
    | [] -> [ "  loop invariant \\true;" ]
    | ps -> ps |> List.map (fun p -> "  loop invariant " ^ acsl_pred p ^ ";")
  in
  let assigns = "  loop assigns " ^ acsl_assigns lc.l_assigns ^ ";" in
  let variant =
    match lc.l_variant with
    | None -> []
    | Some t -> [ "  loop variant " ^ acsl_term t ^ ";" ]
  in
  join "\n" (["/*@"] @ invs @ [assigns] @ variant @ ["*/"])
