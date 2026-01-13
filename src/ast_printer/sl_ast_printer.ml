open Sl_ast

type prec =
  | PTop
  | PImpl
  | POr
  | PAnd
  | PCmp
  | PAdd
  | PMul
  | PUnary
  | PAtom

let paren_if need s =
  if need then "(" ^ s ^ ")" else s

let string_of_binop = function
  | BAdd -> "+" | BSub -> "-" | BMul -> "*" | BDiv -> "/" | BMod -> "%"
  | BEq -> "==" | BNeq -> "!=" | BLt -> "<" | BLe -> "<="
  | BGt -> ">" | BGe -> ">="
  | BAnd -> "&&" | BOr -> "||"

let string_of_unop = function
  | UNeg -> "-" | UNot -> "!"

let prec_of_binop = function
  | BOr -> POr
  | BAnd -> PAnd
  | BEq | BNeq | BLt | BLe | BGt | BGe -> PCmp
  | BAdd | BSub -> PAdd
  | BMul | BDiv | BMod -> PMul

let rec string_of_expr ?(ctx=PTop) = function
  | EVar x -> x
  | EConstInt n -> string_of_int n
  | EConstBool true -> "\\true"
  | EConstBool false -> "\\false"
  | EResult -> "\\result"

  | EDeref e ->
      let inner = string_of_expr ~ctx:PUnary e in
      let s = "*" ^ inner in
      paren_if (ctx <> PTop && ctx <> PUnary && ctx <> PAtom) s

  | EOld e ->
      "\\old(" ^ string_of_expr e ^ ")"

  | EPost e ->
      let inner =
        match e with
        | EVar _ -> string_of_expr ~ctx:PAtom e
        | _ -> "(" ^ string_of_expr e ^ ")"
      in
      inner ^ "'"

  | EUnop (op, e) ->
      string_of_unop op ^ string_of_expr ~ctx:PUnary e

  | EBinop (op, a, b) ->
      let p = prec_of_binop op in
      let sa = string_of_expr ~ctx:p a in
      let sb = string_of_expr ~ctx:p b in
      let s = sa ^ " " ^ string_of_binop op ^ " " ^ sb in
      paren_if (ctx <> PTop && p < ctx) s

  | EApp (f, args) ->
      f ^ "(" ^ (args |> List.map string_of_expr |> String.concat ", ") ^ ")"

let string_of_sort = function
  | SInt -> "int"
  | SBool -> "bool"
  | SPtr -> "ptr"
  | SUser s -> s

let string_of_binder (x, so) =
  match so with
  | None -> x
  | Some s -> x ^ ":" ^ string_of_sort s

let rec string_of_sl ?(ctx=PTop) = function
  | STrue -> "\\true"
  | SFalse -> "\\false"
  | SEmp -> "emp"
  | SPure e -> string_of_expr ~ctx e
  | SHeap h -> string_of_heaplet h

  | SSep xs ->
      xs
      |> List.map (string_of_sl ~ctx:PAnd)
      |> String.concat " ** "
      |> paren_if (ctx <> PTop)

  | SAnd xs ->
      xs
      |> List.map (string_of_sl ~ctx:PAnd)
      |> String.concat " && "
      |> paren_if (ctx = POr || ctx = PImpl)

  | SOr xs ->
      xs
      |> List.map (string_of_sl ~ctx:POr)
      |> String.concat " || "
      |> paren_if (ctx = PImpl)

  | SNot p ->
      "!(" ^ string_of_sl p ^ ")"

  | SImplies (a, b) ->
      let s =
        string_of_sl ~ctx:PImpl a ^ " ==> " ^
        string_of_sl ~ctx:PImpl b
      in
      paren_if (ctx <> PTop) s

  | SExists (bs, p) ->
      "\\exists " ^
      (bs |> List.map string_of_binder |> String.concat ", ") ^
      ". " ^ string_of_sl p

  | SForall (bs, p) ->
      "\\forall " ^
      (bs |> List.map string_of_binder |> String.concat ", ") ^
      ". " ^ string_of_sl p

and string_of_heaplet = function
  | HPt { loc; ty; value; _ } ->
      string_of_expr loc ^ "->" ^ ty ^ "*(" ^ string_of_expr value ^ ")"

  | HRange { loc; ty; lo; hi; _ } ->
      string_of_expr loc ^ "->" ^ ty ^ "*(" ^
      string_of_expr lo ^ "," ^ string_of_expr hi ^ ")"

  | HPred (name, args) ->
      name ^ "(" ^
      (args |> List.map string_of_expr |> String.concat ", ") ^
      ")"

let string_of_clause ~ret = function
  | CReq p ->
      "req " ^ string_of_sl p ^ ";"

  | CEns p ->
      begin match ret with
      | None -> "ens " ^ string_of_sl p ^ ";"
      | Some r -> "ens[" ^ r ^ "] " ^ string_of_sl p ^ ";"
      end

  | CVar None ->
      "req Term[];"

  | CVar (Some e) ->
      "req Term[" ^ string_of_expr e ^ "];"

let string_of_block ~ret b =
  b |> List.map (string_of_clause ~ret)
    |> String.concat " "

let string_of_behavior ~ret b =
  let body_s = string_of_block ~ret b.body in
  if b.assumes = STrue then body_s
  else string_of_sl b.assumes ^ " ==> " ^ body_s

let string_of_spec (s : spec) : string =
  match s.behaviors with
  | { assumes = STrue; body = [CReq p]; _ } :: cases ->
      let req_s = "req " ^ string_of_sl p ^ ";" in
      let cases_s =
        cases
        |> List.map (string_of_behavior ~ret:s.ret)
        |> String.concat " "
      in
      req_s ^ "case {" ^ cases_s ^ "};"

  | bs ->
      let needs_case =
        match bs with
        | [] -> false
        | [b] -> b.assumes <> STrue || b.name <> None
        | _ -> true
      in
      if needs_case then
        let body =
          bs
          |> List.map (fun b -> "  " ^ string_of_behavior ~ret:s.ret b)
          |> String.concat "\n"
        in
        "case {\n" ^ body ^ "\n};"
      else
        match bs with
        | [] -> ";"
        | [b] -> string_of_block ~ret:s.ret b.body
        | _ -> assert false
