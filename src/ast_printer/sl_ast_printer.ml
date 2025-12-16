open Sl_ast

let rec string_of_heap = function
  | Atom (PointTo (p, t, v)) -> Printf.sprintf "%s->%s*(%s)" p t v
  | Sep (h1, h2) -> Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)

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
  | E_eq (e1, e2)  -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | E_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | E_lt (e1, e2)  -> Printf.sprintf "%s<%s"  (string_of_arith e1) (string_of_arith e2)
  | E_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | E_gt (e1, e2)  -> Printf.sprintf "%s>%s"  (string_of_arith e1) (string_of_arith e2)
  | E_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)

let string_of_post_kind = function
  | Post_heap h -> string_of_heap h
  | Post_expr es -> es |> List.map string_of_expr |> String.concat " && "

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;" (string_of_heap s.pre) (string_of_heap s.post)

let string_of_sl_case (c : case_spec) : string =
  let guard = string_of_expr c.test in
  match c.term, c.post with
  | None, Post_heap h_post ->
      let bs = { pre = c.pre; post = h_post } in
      Printf.sprintf "%s => %s" guard (string_of_base_spec bs)
  | None, Post_expr es ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard (string_of_heap c.pre) (es |> List.map string_of_expr |> String.concat " && ")
  | Some (Term e), Post_heap h_post ->
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        guard (string_of_arith e) (string_of_heap h_post)

  | Some (Term e), Post_expr es ->
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        guard (string_of_arith e) (es |> List.map string_of_expr |> String.concat " && ")

  | Some Term_none, Post_heap h_post ->
      Printf.sprintf "%s => req Term[]; ens %s;" guard (string_of_heap h_post)

  | Some Term_none, Post_expr es ->
      Printf.sprintf "%s => req Term[]; ens %s;" guard (es |> List.map string_of_expr |> String.concat " && ")

let string_of_sugar_prime (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) = Printf.sprintf "(*%s)'==(*%s)" p q in
  pairs |> List.map string_of_pair |> String.concat " && "

let string_of_sugar_old (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) = Printf.sprintf "(*%s)==\\old(*%s)" p q
  in pairs |> List.map string_of_pair |> String.concat " && "

let string_of_spec = function
  | Simple bs -> string_of_base_spec bs
  | Case cases -> let body = cases |> List.map string_of_sl_case |> String.concat " " in
      Printf.sprintf "case {%s};" body
  | Sugar_prime pairs -> Printf.sprintf "ens %s;" (string_of_sugar_prime pairs)
  | Sugar_old pairs -> Printf.sprintf "ens %s;" (string_of_sugar_old pairs)
