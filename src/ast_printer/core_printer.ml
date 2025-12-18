
open Core



let join sep xs = String.concat sep xs

let parens s = "(" ^ s ^ ")"



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


let rec string_of_term (t : term) : string =
  match t with
  | TVar (_ph, x) -> x
  | TInt n -> string_of_int n
  | TPtr p -> p
  | THeap (Pre, p) -> "H(" ^ p ^ ")"
  | THeap (Post, p) -> "H'(" ^ p ^ ")"
  | TResult -> "\\result"
  | TArith (op, t1, t2) ->
      let lhs = string_of_term t1 in
      let rhs = string_of_term t2 in
      begin match op with
      | Add | Sub -> lhs ^ " " ^ string_of_arith_op op ^ " " ^ rhs
      | Mul | Div -> lhs ^ string_of_arith_op op ^ rhs
      end
  | TApp (f, args) ->
      f ^ parens (args |> List.map string_of_term |> join ", ")



let string_of_atom (a : atom) : string =
  match a with
  | ARel (r, t1, t2) ->
      string_of_term t1 ^ " " ^ string_of_rel r ^ " " ^ string_of_term t2
  | APred (name, args) ->
      name ^ parens (args |> List.map string_of_term |> join ", ")

let rec string_of_predicate (p : predicate) : string =
  match p with
  | PTrue -> "true"
  | PFalse -> "false"
  | PAtom a -> string_of_atom a
  | PNot p1 ->
      "not " ^ parens (string_of_predicate p1)
  | PAnd ps ->
      begin match ps with
      | [] -> "true"
      | [x] -> string_of_predicate x
      | _ -> ps |> List.map string_of_predicate |> join " && "
      end
  | POr ps ->
      begin match ps with
      | [] -> "false"
      | [x] -> string_of_predicate x
      | _ -> ps |> List.map string_of_predicate |> join " || "
      end
  | PImplies (p1, p2) ->
      parens (string_of_predicate p1) ^ " ==> " ^ parens (string_of_predicate p2)
  | PForall (bs, body) ->
      "forall " ^ (bs |> List.map string_of_binder |> join ", ")
      ^ ". " ^ string_of_predicate body
  | PExists (bs, body) ->
      "exists " ^ (bs |> List.map string_of_binder |> join ", ")
      ^ ". " ^ string_of_predicate body



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



type clause_bucket = {
  assumes : predicate list;
  requires : predicate list;
  ensures : predicate list;
  assigns : assignable list option;   
  variant : term option;              
}

let empty_bucket =
  { assumes = []; requires = []; ensures = []; assigns = None; variant = None }

let bucket_add (b : clause_bucket) (c : clause) : clause_bucket =
  match c with
  | Assumes p -> { b with assumes = b.assumes @ [p] }
  | Requires p -> { b with requires = b.requires @ [p] }
  | Ensures p -> { b with ensures = b.ensures @ [p] }
  | Assigns xs ->
      
      let merged =
        match b.assigns with
        | None -> xs
        | Some ys -> ys @ xs
      in
      { b with assigns = Some merged }
  | Variant t ->
      
      { b with variant = Some t }

let bucket_of_clauses (cs : clause list) : clause_bucket =
  List.fold_left bucket_add empty_bucket cs

let conjunct (ps : predicate list) : predicate =
  match ps with
  | [] -> PTrue
  | [p] -> p
  | _ -> PAnd ps



let string_of_param (p : param) : string =
  p.name ^ ":" ^ string_of_mode p.mode

let string_of_behavior (bhv : behavior) : string =
  let b = bucket_of_clauses bhv.clauses in
  let header =
    match bhv.b_name with
    | None -> ""
    | Some n -> "behavior " ^ n ^ "\n"
  in
  let assumes_s = "assumes " ^ string_of_predicate (conjunct b.assumes) in
  let requires_s = "requires " ^ string_of_predicate (conjunct b.requires) in
  let ensures_s = "ensures " ^ string_of_predicate (conjunct b.ensures) in
  let assigns_s =
    match b.assigns with
    | None -> "assigns {}"
    | Some xs -> "assigns " ^ string_of_assignables xs
  in
  let variant_s =
    match b.variant with
    | None -> None
    | Some t -> Some ("variant " ^ string_of_term t)
  in
  let lines =
    [ Some header
    ; Some (assumes_s ^ "\n")
    ; Some (requires_s ^ "\n")
    ; Some (ensures_s ^ "\n")
    ; Some (assigns_s)
    ; (match variant_s with None -> None | Some v -> Some ("\n" ^ v))
    ]
    |> List.filter_map (fun x -> x)
  in
  join "" lines

let string_of_spec_kind = function
  | FunctionContract -> "function"
  | LoopContract -> "loop"

let string_of_spec (s : spec) : string =
  let params_s =
    "params (" ^ (s.params |> List.map string_of_param |> join ", ") ^ ")\n"
  in
  let kind_s =
    "kind " ^ string_of_spec_kind s.kind ^ "\n"
  in
  let behaviors_s =
    s.behaviors |> List.map string_of_behavior |> join "\n"
  in
  kind_s ^ params_s ^ behaviors_s
