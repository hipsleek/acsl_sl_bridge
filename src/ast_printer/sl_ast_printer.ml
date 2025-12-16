open Sl_ast

let rec string_of_arith = function
  | A_var x -> x
  | A_post_var x -> x ^ "'"
  | A_old e -> "\\old(" ^ string_of_arith e ^ ")"
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)

let string_of_pure_atom = function
  | P_eq (e1, e2) -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | P_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | P_lt (e1, e2) -> Printf.sprintf "%s<%s"  (string_of_arith e1) (string_of_arith e2)
  | P_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | P_gt (e1, e2) -> Printf.sprintf "%s>%s"  (string_of_arith e1) (string_of_arith e2)
  | P_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)

let string_of_heap_atom = function
  | PointTo (p, t, v) -> Printf.sprintf "%s->%s*(%s)" p t v

let string_of_sugar_prime (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) = Printf.sprintf "(*%s)'==(*%s)" p q in
  pairs |> List.map string_of_pair |> String.concat " && "

let string_of_sugar_old (pairs : (ptr * ptr) list) : string =
  let string_of_pair (p, q) = Printf.sprintf "(*%s)==\\old(*%s)" p q in
  pairs |> List.map string_of_pair |> String.concat " && "

type prec =
  | Prec_or
  | Prec_and
  | Prec_implies
  | Prec_not
  | Prec_sep
  | Prec_atom

let prec_of_assertion = function
  | A_implies _ -> Prec_implies
  | A_or _ -> Prec_or
  | A_and _ -> Prec_and
  | A_not _ -> Prec_not
  | A_sep _ -> Prec_sep
  | A_emp
  | A_heap_atom _
  | A_pure _
  | A_sugar_prime _
  | A_sugar_old _ -> Prec_atom

let parenthesize (need : bool) (s : string) : string =
  if need then "(" ^ s ^ ")" else s

let rec string_of_assertion ?(ctx = Prec_or) (a : assertion) : string =
  let my_prec = prec_of_assertion a in
  let need_parens =
    match (ctx, my_prec) with
    | Prec_atom, _ -> false
    | Prec_sep, (Prec_or | Prec_and | Prec_implies) -> true
    | Prec_not, (Prec_or | Prec_and | Prec_implies | Prec_sep) -> true
    | Prec_and, (Prec_or | Prec_implies) -> true
    | Prec_or, Prec_implies -> true
    | Prec_implies, _ -> false
    | _, _ -> false
  in
  let rendered =
    match a with
    | A_emp -> "emp"

    | A_heap_atom ha -> string_of_heap_atom ha
    | A_pure p -> string_of_pure_atom p

    | A_sep (a1, a2) ->
        Printf.sprintf "%s ** %s"
          (string_of_assertion ~ctx:Prec_sep a1)
          (string_of_assertion ~ctx:Prec_sep a2)

    | A_not a1 ->
        Printf.sprintf "!(%s)" (string_of_assertion ~ctx:Prec_or a1)

    | A_and (a1, a2) ->
        Printf.sprintf "%s && %s"
          (string_of_assertion ~ctx:Prec_and a1)
          (string_of_assertion ~ctx:Prec_and a2)

    | A_or (a1, a2) ->
        Printf.sprintf "%s || %s"
          (string_of_assertion ~ctx:Prec_or a1)
          (string_of_assertion ~ctx:Prec_or a2)

    | A_implies (a1, a2) ->
        Printf.sprintf "%s => %s"
          (string_of_assertion ~ctx:Prec_implies a1)
          (string_of_assertion ~ctx:Prec_implies a2)

    | A_sugar_prime pairs ->
        string_of_sugar_prime pairs

    | A_sugar_old pairs ->
        string_of_sugar_old pairs
  in
  parenthesize need_parens rendered

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_assertion s.pre)
    (string_of_assertion s.post)

let string_of_term_opt = function
  | None -> None
  | Some Term_none -> Some "Term[]"
  | Some (Term e)  -> Some (Printf.sprintf "Term[%s]" (string_of_arith e))

let string_of_sl_case (c : case_spec) : string =
  let guard = string_of_assertion c.test in
  match string_of_term_opt c.term with
  | None ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        (string_of_assertion c.pre)
        (string_of_assertion c.post)
  | Some t ->
      Printf.sprintf "%s => req %s; ens %s;"
        guard
        t
        (string_of_assertion c.post)

let string_of_spec = function
  | Simple bs -> string_of_base_spec bs
  | Ens a -> Printf.sprintf "ens %s;" (string_of_assertion a)
  | Case cases ->
      let body = cases |> List.map string_of_sl_case |> String.concat " " in
      Printf.sprintf "case {%s};" body
