open Sl_ast

let rec string_of_heap = function
  | Atom (PointTo (p, t, v)) ->
      Printf.sprintf "%s->%s*(%s)" p t v
  | Sep (h1, h2) ->
      Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)

let rec string_of_arith = function
  | A_var x -> x
  | A_post_var x -> x ^ "'"
  | A_old e -> "\\old(" ^ string_of_arith e ^ ")"
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)

let string_of_expr = function
  | E_eq  (e1, e2) -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | E_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | E_lt  (e1, e2) -> Printf.sprintf "%s<%s"  (string_of_arith e1) (string_of_arith e2)
  | E_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | E_gt  (e1, e2) -> Printf.sprintf "%s>%s"  (string_of_arith e1) (string_of_arith e2)
  | E_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)

let rec string_of_pred = function
  | Pred ce -> string_of_expr ce
  | Pred_and (p1, p2) ->
      Printf.sprintf "%s && %s" (string_of_pred p1) (string_of_pred p2)

let string_of_post_kind = function
  | Post_heap h -> string_of_heap h
  | Post_expr p -> string_of_pred p

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)

let string_of_terminate = function
  | Term_none -> "Term[]"
  | Term e    -> Printf.sprintf "Term[%s]" (string_of_arith e)

let string_of_sl_case (c : case_spec) : string =
  let guard = string_of_expr c.test in
  match c.term, c.post with
  | None, Post_heap h_post ->
      let bs = { pre = c.pre; post = h_post } in
      Printf.sprintf "%s => %s" guard (string_of_base_spec bs)

  | None, Post_expr p ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        (string_of_heap c.pre)
        (string_of_pred p)

  | Some t, Post_heap h_post ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        (string_of_terminate t)
        (string_of_heap h_post)

  | Some t, Post_expr p ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        (string_of_terminate t)
        (string_of_pred p)

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

let string_of_loop_simple (ls : loop_simple) : string =
  let req_str  = string_of_pred ls.req in
  let term_str =
    match ls.term with
    | None   -> ""
    | Some t -> " && " ^ string_of_terminate t
  in
  let ens_str  = string_of_pred ls.ens in
  Printf.sprintf "req %s%s; ens %s;" req_str term_str ens_str

let string_of_loop_spec = function
  | Loop_case cases ->
      let body =
        cases
        |> List.map string_of_sl_case
        |> String.concat " "
      in
      Printf.sprintf "case {%s};" body
  | Loop_simple ls ->
      string_of_loop_simple ls

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
  | Loop ls ->
      string_of_loop_spec ls
