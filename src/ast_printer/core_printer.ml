open Core

let join sep xs = String.concat sep xs
let parens s = "(" ^ s ^ ")"



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

let need_parens (ctx : prec) (here : prec) =
  prec_to_int here < prec_to_int ctx

let with_parens_if ctx here s =
  if need_parens ctx here then parens s else s



let string_of_mode = function
  | In -> "in"
  | Out -> "out"
  | InOut -> "inout"

let string_of_phase = function
  | Pre -> "pre"
  | Post -> "post"

let string_of_arith_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

let string_of_rel = function
  | Eq -> "=="
  | Neq -> "!="
  | Lt -> "<"
  | Lte -> "<="
  | Gt -> ">"
  | Gte -> ">="

let string_of_binder (b : binder) : string =
  match b.b_ty with
  | None -> b.b_name
  | Some ty_s -> ty_s ^ " " ^ b.b_name



let prec_of_term = function
  | TInt _ | TVar _ | TPtr _ | TResult -> PAtom
  | THeap _ -> PAtom
  | TApp _ -> PAtom
  | TIndex _ -> PAtom
  | TLoad _ -> PAtom
  | TArith (Mul, _, _) | TArith (Div, _, _) -> PMul
  | TArith (Add, _, _) | TArith (Sub, _, _) -> PAdd

let rec string_of_term ?(ctx=PTop) (t : term) : string =
  let here = prec_of_term t in
  let s =
    match t with
    | TVar (Pre, x)-> x
    | TVar (Post, x) -> x ^ "'"              
    | TInt n -> string_of_int n
    | TPtr p -> p
    | THeap (Pre, p)-> "H(" ^ p ^ ")"
    | THeap (Post, p) -> "H'(" ^ p ^ ")"
    | TResult -> "\\result"
    | TArith (op, t1, t2) ->
        let (p_here, op_s) =
          match op with
          | Add | Sub -> (PAdd, " " ^ string_of_arith_op op ^ " ")
          | Mul | Div -> (PMul, string_of_arith_op op)
        in
        let lhs = string_of_term ~ctx:p_here t1 in
        let rhs = string_of_term ~ctx:p_here t2 in
        lhs ^ op_s ^ rhs
    | TApp (f, args) ->
        f ^ parens (args |> List.map (string_of_term ~ctx:PTop) |> join ", ")
    | TLoad (Pre, t1) ->
        "load(" ^ string_of_term ~ctx:PTop t1 ^ ")"
    | TLoad (Post, t1) ->
        "load'(" ^ string_of_term ~ctx:PTop t1 ^ ")"
    | TIndex (_ph, a, idx) ->
        string_of_term ~ctx:PAtom a ^ "[" ^ string_of_term ~ctx:PTop idx ^ "]"



  in
  with_parens_if ctx here s



let prec_of_pred = function
  | PTrue | PFalse | PAtom _ -> PAtom
  | PNot _ -> PUnary
  | PAnd _ -> PAnd
  | POr _ -> POr
  | PImplies _ -> PImpl
  | PForall _ | PExists _ -> PAtom

let string_of_atom (a : atom) : string =
  match a with
  | ARel (r, t1, t2) ->
      string_of_term ~ctx:PRel t1 ^ " " ^ string_of_rel r ^ " " ^ string_of_term ~ctx:PRel t2
  | APred (name, args) ->
      name ^ parens (args |> List.map (string_of_term ~ctx:PTop) |> join ", ")

let rec string_of_predicate ?(ctx=PTop) (p : predicate) : string =
  let here = prec_of_pred p in
  let s =
    match p with
    | PTrue -> "true"
    | PFalse -> "false"
    | PAtom a -> string_of_atom a
    | PNot p1 ->
        "not " ^ (string_of_predicate ~ctx:PUnary p1 |> parens)
    | PAnd ps ->
        begin match ps with
        | [] -> "true"
        | [x] -> string_of_predicate ~ctx:ctx x
        | _ ->
            ps |> List.map (string_of_predicate ~ctx:PAnd) |> join " && "
        end
    | POr ps ->
        begin match ps with
        | [] -> "false"
        | [x] -> string_of_predicate ~ctx:ctx x
        | _ ->
            ps |> List.map (string_of_predicate ~ctx:POr) |> join " || "
        end
    | PImplies (p1, p2) ->
        (string_of_predicate ~ctx:PImpl p1 |> parens)
        ^ " ==> "
        ^ (string_of_predicate ~ctx:PImpl p2 |> parens)
    | PForall (bs, body) ->
        "forall "
        ^ (bs |> List.map string_of_binder |> join ", ")
        ^ ". "
        ^ string_of_predicate ~ctx:PTop body
    | PExists (bs, body) ->
        "exists "
        ^ (bs |> List.map string_of_binder |> join ", ")
        ^ ". "
        ^ string_of_predicate ~ctx:PTop body
  in
  with_parens_if ctx here s



let string_of_assignable (a : assignable) : string =
  match a with
  | AsVar x -> x
  | AsHeap p -> "*" ^ p
  | AsRange (p, lo, hi) ->
      p ^ "+(" ^ string_of_term lo ^ ".." ^ string_of_term hi ^ ")"
  | AsTerm t ->
      "assign(" ^ string_of_term t ^ ")"

let string_of_assignables (xs : assignable list) : string =
  match xs with
  | [] -> "{}"
  | _ -> "{ " ^ (xs |> List.map string_of_assignable |> join ", ") ^ " }"



let string_of_param (p : param) : string =
  p.name ^ ":" ^ string_of_mode p.mode

let string_of_clause (c : clause) : string =
  match c with
  | Assumes p-> "assumes "^ string_of_predicate p
  | Requires p -> "requires " ^ string_of_predicate p
  | Ensures p-> "ensures "^ string_of_predicate p
  | Assigns xs -> "assigns "^ string_of_assignables xs
  | Variant t-> "variant "^ string_of_term t

let string_of_behavior (b : behavior) : string =
  let header =
    match b.b_name with
    | None -> "behavior <anon>:"
    | Some n -> "behavior " ^ n ^ ":"
  in
  let body = b.clauses |> List.map (fun c -> "  " ^ string_of_clause c) in
  join "\n" (header :: body)

let string_of_spec_kind = function
  | FunctionContract -> "function"
  | LoopContract -> "loop"

let string_of_spec (s : spec) : string =
  let params_s =
    "params(" ^ (s.params |> List.map string_of_param |> join ", ") ^ ")"
  in
  let kind_s = "kind(" ^ string_of_spec_kind s.kind ^ ")" in
  let beh_s = s.behaviors |> List.map string_of_behavior |> join "\n\n" in
  join "\n" [kind_s; params_s; beh_s]
