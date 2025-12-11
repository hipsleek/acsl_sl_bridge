type ptr = string
type car_type = string
type car = string

type heap_atom = 
  | PointTo of ptr * car_type * car 

type heap = 
  | Atom of heap_atom
  | Sep of heap * heap

type arith_expr =
  | A_var of string
  | A_post_var of string
  | A_old of arith_expr
  | A_int of int
  | A_add of arith_expr * arith_expr
  | A_sub of arith_expr * arith_expr
  | A_mul of arith_expr * arith_expr
  | A_div of arith_expr * arith_expr

type conditional_expr =
  | E_eq of arith_expr * arith_expr
  | E_neq of arith_expr * arith_expr
  | E_lte of arith_expr * arith_expr
  | E_lt of arith_expr * arith_expr
  | E_gte of arith_expr * arith_expr
  | E_gt of arith_expr * arith_expr

type terminate_expr =
  | Term_none
  | Term of arith_expr

type post_kind =
  | Post_heap of heap
  | Post_expr of conditional_expr

type base_spec = {
  pre : heap;
  post : heap;
}

type case_spec = {
  test : conditional_expr;
  term : terminate_expr option;
  pre : heap;
  post : post_kind;
}

type spec =
  | Simple of base_spec
  | Sugar_prime of (ptr * ptr) list
  | Sugar_old of (ptr * ptr) list
  | Case of case_spec list


(*Prints*)
let rec string_of_heap = function
  | Atom (PointTo (p, t, v)) ->
      Printf.sprintf "%s->%s*(%s)" p t v
  | Sep (h1, h2) ->
      Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)    

let rec string_of_arith = function
  | A_var x -> x
  | A_post_var x  -> x ^ "'"
  | A_old e -> "\\old(" ^ string_of_arith e ^ ")"
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)

let string_of_expr = function
  | E_eq (e1, e2) -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | E_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | E_lt (e1, e2) -> Printf.sprintf "%s<%s" (string_of_arith e1) (string_of_arith e2)
  | E_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | E_gt (e1, e2) -> Printf.sprintf "%s>%s" (string_of_arith e1) (string_of_arith e2)
  | E_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)


let string_of_post_kind = function
  | Post_heap h -> string_of_heap h
  | Post_expr e -> string_of_expr e

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)

let string_of_sl_case (c : case_spec) : string =
  let guard = string_of_expr c.test in
  match c.term, c.post with
  | None, Post_heap h_post ->
      let bs = { pre = c.pre; post = h_post } in
      Printf.sprintf "%s => %s" guard (string_of_base_spec bs)

  | None, Post_expr ce ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        (string_of_heap c.pre)
        (string_of_expr ce)

  | Some (Term e), Post_heap h_post ->
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        guard
        (string_of_arith e)
        (string_of_heap h_post)

  | Some (Term e), Post_expr ce ->
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        guard
        (string_of_arith e)
        (string_of_expr ce)

  | Some Term_none, Post_heap h_post ->
      Printf.sprintf "%s => req Term[]; ens %s;"
        guard
        (string_of_heap h_post)

  | Some Term_none, Post_expr ce ->
      Printf.sprintf "%s => req Term[]; ens %s;"
        guard
        (string_of_expr ce)


let string_of_sugar_prime (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) =
    Printf.sprintf "(*%s)'==(*%s)" p q
  in
  pairs
  |> List.map string_of_pair
  |> String.concat " && "

let string_of_sugar_old (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) =
    Printf.sprintf "(*%s)==\\old(*%s)" p q
  in
  pairs
  |> List.map string_of_pair
  |> String.concat " && "

let string_of_spec = function
  | Simple bs ->
      string_of_base_spec bs
  | Case cases ->
      let body =
        cases
        |> List.map string_of_sl_case
        |> String.concat " "
      in
      Printf.sprintf "case {%s};" body
  | Sugar_prime pairs ->
      Printf.sprintf "ens %s;" (string_of_sugar_prime pairs)
  | Sugar_old pairs ->
      Printf.sprintf "ens %s;" (string_of_sugar_old pairs)
