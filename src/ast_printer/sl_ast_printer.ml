open Sl_ast

(* -------------------------------------------------------------------------- *)
(* Arithmetic expressions                                                     *)
(* -------------------------------------------------------------------------- *)

(* Default printer: A_result must NOT appear here *)
let rec string_of_arith (e : arith_expr) : string =
  match e with
  | A_var x -> x
  | A_post_var x -> x ^ "'"
  | A_old e -> "\\old(" ^ string_of_arith e ^ ")"
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)
  | A_result ->
      failwith "A_result cannot be printed outside ens[...]"

(* Binder-aware arithmetic printer *)
let rec string_of_arith_with_ret (r : var) (e : arith_expr) : string =
  match e with
  | A_result -> r
  | A_var x -> x
  | A_post_var x -> x ^ "'"
  | A_old e -> "\\old(" ^ string_of_arith_with_ret r e ^ ")"
  | A_int n -> string_of_int n
  | A_add (e1, e2) ->
      Printf.sprintf "%s+%s"
        (string_of_arith_with_ret r e1)
        (string_of_arith_with_ret r e2)
  | A_sub (e1, e2) ->
      Printf.sprintf "%s-%s"
        (string_of_arith_with_ret r e1)
        (string_of_arith_with_ret r e2)
  | A_mul (e1, e2) ->
      Printf.sprintf "%s*%s"
        (string_of_arith_with_ret r e1)
        (string_of_arith_with_ret r e2)
  | A_div (e1, e2) ->
      Printf.sprintf "%s/%s"
        (string_of_arith_with_ret r e1)
        (string_of_arith_with_ret r e2)

(* -------------------------------------------------------------------------- *)
(* Pure atoms                                                                 *)
(* -------------------------------------------------------------------------- *)

let string_of_pure_atom (p : pure_atom) : string =
  match p with
  | P_eq (e1, e2) -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | P_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | P_lt (e1, e2) -> Printf.sprintf "%s<%s"  (string_of_arith e1) (string_of_arith e2)
  | P_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | P_gt (e1, e2) -> Printf.sprintf "%s>%s"  (string_of_arith e1) (string_of_arith e2)
  | P_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)

let string_of_pure_atom_with_ret (r : var) (p : pure_atom) : string =
  match p with
  | P_eq (e1, e2) -> Printf.sprintf "%s==%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)
  | P_neq (e1, e2) -> Printf.sprintf "%s!=%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)
  | P_lt (e1, e2) -> Printf.sprintf "%s<%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)
  | P_lte (e1, e2) -> Printf.sprintf "%s<=%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)
  | P_gt (e1, e2) -> Printf.sprintf "%s>%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)
  | P_gte (e1, e2) -> Printf.sprintf "%s>=%s"
      (string_of_arith_with_ret r e1)
      (string_of_arith_with_ret r e2)

(* -------------------------------------------------------------------------- *)
(* Heap atoms and sugar                                                       *)
(* -------------------------------------------------------------------------- *)

let string_of_heap_atom = function
  | PointTo (p, t, v) -> Printf.sprintf "%s->%s*(%s)" p t v

let string_of_sugar_prime pairs =
  pairs
  |> List.map (fun (p,q) -> Printf.sprintf "(*%s)'==(*%s)" p q)
  |> String.concat " && "

let string_of_sugar_old pairs =
  pairs
  |> List.map (fun (p,q) -> Printf.sprintf "(*%s)==\\old(*%s)" p q)
  |> String.concat " && "

(* -------------------------------------------------------------------------- *)
(* Assertions                                                                 *)
(* -------------------------------------------------------------------------- *)

let rec string_of_assertion (a : assertion) : string =
  match a with
  | A_emp -> "emp"
  | A_heap_atom ha -> string_of_heap_atom ha
  | A_pure p -> string_of_pure_atom p
  | A_sep (a,b) -> string_of_assertion a ^ " ** " ^ string_of_assertion b
  | A_and (a,b) -> string_of_assertion a ^ " && " ^ string_of_assertion b
  | A_or (a,b)  -> string_of_assertion a ^ " || " ^ string_of_assertion b
  | A_not a -> "!(" ^ string_of_assertion a ^ ")"
  | A_implies (a,b) -> string_of_assertion a ^ " => " ^ string_of_assertion b
  | A_sugar_prime ps -> string_of_sugar_prime ps
  | A_sugar_old ps -> string_of_sugar_old ps

let rec string_of_assertion_with_ret (r : var) (a : assertion) : string =
  match a with
  | A_emp -> "emp"
  | A_heap_atom ha -> string_of_heap_atom ha
  | A_pure p -> string_of_pure_atom_with_ret r p
  | A_sep (a,b) -> string_of_assertion_with_ret r a ^ " ** " ^ string_of_assertion_with_ret r b
  | A_and (a,b) -> string_of_assertion_with_ret r a ^ " && " ^ string_of_assertion_with_ret r b
  | A_or (a,b)  -> string_of_assertion_with_ret r a ^ " || " ^ string_of_assertion_with_ret r b
  | A_not a -> "!(" ^ string_of_assertion_with_ret r a ^ ")"
  | A_implies (a,b) -> string_of_assertion_with_ret r a ^ " => " ^ string_of_assertion_with_ret r b
  | A_sugar_prime ps -> string_of_sugar_prime ps
  | A_sugar_old ps -> string_of_sugar_old ps

(* -------------------------------------------------------------------------- *)
(* Specs                                                                      *)
(* -------------------------------------------------------------------------- *)

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_assertion s.pre)
    (string_of_assertion s.post)

let string_of_sl_case (c : case_spec) : string =
  match c.term with
  | None ->
      Printf.sprintf "%s => req %s; ens %s;"
        (string_of_assertion c.test)
        (string_of_assertion c.pre)
        (string_of_assertion c.post)
  | Some t ->
      let term_str =
        match t with
        | Term e -> string_of_arith e
        | Term_none -> ""
      in
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        (string_of_assertion c.test)
        term_str
        (string_of_assertion c.post)

let string_of_ens_spec (e : ens_spec) : string =
  match e.ret with
  | None ->
      Printf.sprintf "ens %s;" (string_of_assertion e.post)
  | Some r ->
      Printf.sprintf "ens[%s] %s;"
        r
        (string_of_assertion_with_ret r e.post)

let string_of_spec (s : spec) : string =
  match s with
  | Simple bs -> string_of_base_spec bs
  | Ens e -> string_of_ens_spec e
  | Case cases ->
      "case {" ^ String.concat " " (List.map string_of_sl_case cases) ^ "};"
