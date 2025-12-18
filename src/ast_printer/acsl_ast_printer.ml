open Acsl_ast

let join sep xs = String.concat sep xs
let parens s = "(" ^ s ^ ")"
let comma_list xs = join ", " xs

let conj xs =
  match xs with
  | [] -> "\\true"
  | [x] -> x
  | _ -> join " && " xs

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

let rec acsl_term = function
  | TVar x -> x
  | TInt n -> string_of_int n
  | TDeref t -> "*" ^ acsl_term t
  | TOld t -> "\\old(" ^ acsl_term t ^ ")"
  | TResult -> "\\result"
  | TApp (f,args) -> f ^ parens (args |> List.map acsl_term |> comma_list)
  | TBinOp (op,t1,t2) -> acsl_term t1 ^ " " ^ string_of_binop op ^ " " ^ acsl_term t2

let rec acsl_pred = function
  | PTrue -> "\\true"
  | PFalse -> "\\false"
  | PRel (r,t1,t2) -> acsl_term t1 ^ " " ^ string_of_rel r ^ " " ^ acsl_term t2
  | PApp (name,args) -> name ^ parens (args |> List.map acsl_term |> comma_list)
  | PNot p -> "!" ^ parens (acsl_pred p)
  | PAnd ps -> ps |> List.map acsl_pred |> conj
  | POr ps ->
      begin match ps with
      | [] -> "\\false"
      | [p] -> acsl_pred p
      | _ -> ps |> List.map acsl_pred |> join " || "
      end
  | PImplies (p1,p2) -> parens (acsl_pred p1) ^ " ==> " ^ parens (acsl_pred p2)
  | PForall (bs,body) ->
      let bs_str =
        bs
        |> List.map (fun (x,ty) -> match ty with None -> x | Some t -> t ^ " " ^ x)
        |> comma_list
      in
      "\\forall " ^ bs_str ^ "; " ^ acsl_pred body
  | PExists (bs,body) ->
      let bs_str =
        bs
        |> List.map (fun (x,ty) -> match ty with None -> x | Some t -> t ^ " " ^ x)
        |> comma_list
      in
      "\\exists " ^ bs_str ^ "; " ^ acsl_pred body

let acsl_assigns = function
  | ANothing -> "\\nothing"
  | AList ts ->
      begin match ts with
      | [] -> "\\nothing"
      | _ -> ts |> List.map acsl_term |> comma_list
      end

let acsl_behavior (b:behavior) =
  match b.b_name with
  | None ->
      let ensures = b.b_ensures |> List.map acsl_pred |> conj in
      ["  ensures " ^ ensures ^ ";"]
  | Some name ->
      let assumes = b.b_assumes |> List.map acsl_pred |> conj in
      let ensures = b.b_ensures |> List.map acsl_pred |> conj in
      ["  behavior " ^ name ^ ":";"    assumes " ^ assumes ^ ";";"    ensures " ^ ensures ^ ";"]

let acsl_contract (c:contract) =
  let requires = c.requires |> List.map acsl_pred |> conj in
  let assigns = acsl_assigns c.assigns in
  let body = c.behaviors |> List.concat_map acsl_behavior in
  join "\n" (["/*@";"  requires " ^ requires ^ ";";"  assigns " ^ assigns ^ ";"] @ body @ ["*/"])

let acsl_loop_contract (lc:loop_contract) =
  let invs =
    match lc.l_invariants with
    | [] -> ["  loop invariant \\true;"]
    | ps -> ps |> List.map (fun p -> "  loop invariant " ^ acsl_pred p ^ ";")
  in
  let assigns = "  loop assigns " ^ acsl_assigns lc.l_assigns ^ ";" in
  let variant =
    match lc.l_variant with
    | None -> []
    | Some t -> ["  loop variant " ^ acsl_term t ^ ";"]
  in
  join "\n" (["/*@"] @ invs @ [assigns] @ variant @ ["*/"])
