(* sl_ast_printer.ml *)

open Sl_ast

let rec string_of_arith ?(result_name : string option = None) (e : arith) : string =
  match e with
  | AVar x -> x
  | APostVar x -> x ^ "'"
  | AOld a -> "\\old(" ^ string_of_arith ~result_name a ^ ")"
  | AInt n -> string_of_int n
  | AAdd (a,b) -> string_of_arith ~result_name a ^ "+" ^ string_of_arith ~result_name b
  | ASub (a,b) -> string_of_arith ~result_name a ^ "-" ^ string_of_arith ~result_name b
  | AMul (a,b) -> string_of_arith ~result_name a ^ "*" ^ string_of_arith ~result_name b
  | ADiv (a,b) -> string_of_arith ~result_name a ^ "/" ^ string_of_arith ~result_name b
  | AResult ->
      (match result_name with
       | Some r -> r
       | None -> "\\result")

let string_of_pure_atom ?(result_name : string option = None) (p : pure_atom) : string =
  let a = string_of_arith ~result_name in
  match p with
  | PEq (x,y)  -> a x ^ "==" ^ a y
  | PNeq (x,y) -> a x ^ "!=" ^ a y
  | PLt (x,y)  -> a x ^ "<"  ^ a y
  | PLte (x,y) -> a x ^ "<=" ^ a y
  | PGt (x,y)  -> a x ^ ">"  ^ a y
  | PGte (x,y) -> a x ^ ">=" ^ a y

let rec string_of_assertion ?(result_name : string option = None) (a : assertion) : string =
  match a with
  | AEmp -> "emp"
  | AHeapAtom (PointTo (p,t,v)) -> p ^ "->" ^ t ^ "*(" ^ v ^ ")"
  | ASep (x,y) -> string_of_assertion ~result_name x ^ " ** " ^ string_of_assertion ~result_name y
  | APure p -> string_of_pure_atom ~result_name p
  | AAnd (x,y) -> string_of_assertion ~result_name x ^ " && " ^ string_of_assertion ~result_name y
  | AOr (x,y) -> string_of_assertion ~result_name x ^ " || " ^ string_of_assertion ~result_name y
  | ANot x -> "!(" ^ string_of_assertion ~result_name x ^ ")"
  | AImplies (x,y) -> string_of_assertion ~result_name x ^ " => " ^ string_of_assertion ~result_name y
  | ASugarPrime pairs ->
      pairs
      |> List.map (fun (a,b) -> "(*" ^ a ^ ")'==(*" ^ b ^ ")")
      |> String.concat " && "
  | ASugarOld pairs ->
      pairs
      |> List.map (fun (a,b) -> "(*" ^ a ^ ")==\\old(*" ^ b ^ ")")
      |> String.concat " && "

let string_of_base_spec (b : base_spec) : string =
  "req " ^ string_of_assertion b.pre ^ "; ens " ^ string_of_assertion b.post ^ ";"

let string_of_term (t : terminate_expr option) : string option =
  match t with
  | None -> None
  | Some TermNone -> Some "Term[]"
  | Some (Term e) -> Some ("Term[" ^ string_of_arith e ^ "]")

let string_of_case (c : case_spec) : string =
  let guard = string_of_assertion c.test in
  match c.term with
  | None ->
      (* normal case: req <pre>; ens <post>; *)
      guard ^ " => req " ^ string_of_assertion c.pre ^ "; ens " ^ string_of_assertion c.post ^ ";"
  | Some TermNone ->
      (* loop-ish case: req Term[]; ens <post>; *)
      guard ^ " => req Term[]; ens " ^ string_of_assertion c.post ^ ";"
  | Some (Term e) ->
      guard ^ " => req Term[" ^ string_of_arith e ^ "]; ens " ^ string_of_assertion c.post ^ ";"

let string_of_spec (s : spec) : string =
  match s with
  | Simple b ->
      string_of_base_spec b

  | Ens { ret; post } ->
      let post_s = string_of_assertion ~result_name:ret post in
      (match ret with
       | None -> "ens " ^ post_s ^ ";"
       | Some r -> "ens[" ^ r ^ "] " ^ post_s ^ ";")

  | Case cases ->
      let body =
        cases
        |> List.map string_of_case
        |> String.concat " "
      in
      "case {" ^ body ^ "};"
