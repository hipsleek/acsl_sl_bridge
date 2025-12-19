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

let paren_if (need : bool) (s : string) : string =
  if need then "(" ^ s ^ ")" else s
 let string_of_binop = function
  | BAdd -> "+" | BSub -> "-" | BMul -> "*" | BDiv -> "/" | BMod -> "%"
  | BEq -> "=="| BNeq -> "!="| BLt -> "<" | BLe -> "<="| BGt -> ">" | BGe -> ">="
  | BAnd -> "&&"| BOr -> "||"

let string_of_unop = function
  | UNeg -> "-" | UNot -> "!"

let prec_of_binop = function
  | BOr -> POr
  | BAnd -> PAnd
  | BEq | BNeq | BLt | BLe | BGt | BGe -> PCmp
  | BAdd | BSub -> PAdd
  | BMul | BDiv | BMod -> PMul

let rec string_of_expr ?(ctx : prec = PTop) (e : expr) : string =
  match e with
  | EVar x -> x
  | EConstInt n -> string_of_int n
  | EConstBool true -> "true"
  | EConstBool false -> "false"
  | EResult -> "\\result"

  | EDeref e1 ->
      
      let inner = string_of_expr ~ctx:PUnary e1 in
      paren_if (ctx <> PTop && ctx <> PUnary && ctx <> PAtom) ("*" ^ inner)

  | EOld e1 ->
      "\\old(" ^ string_of_expr ~ctx:PTop e1 ^ ")"

  | EPost e1 ->
      
      let inner =
        match e1 with
        | EVar _ -> string_of_expr ~ctx:PAtom e1
        | _ -> "(" ^ string_of_expr ~ctx:PTop e1 ^ ")"
      in
      inner ^ "'"

  | EUnop (op, e1) ->
      let s = string_of_unop op ^ string_of_expr ~ctx:PUnary e1 in
      paren_if (ctx <> PTop && ctx <> PUnary && ctx <> PAtom) s

  | EBinop (op, a, b) ->
      let myp = prec_of_binop op in
      let sa = string_of_expr ~ctx:myp a in
      let sb = string_of_expr ~ctx:myp b in
      let s = sa ^ " " ^ string_of_binop op ^ " " ^ sb in
      
      let need =
        match ctx, myp with
        | PTop, _ -> false
        | PImpl, (POr | PAnd | PCmp | PAdd | PMul | PUnary | PAtom) -> false
        | POr, (PAnd | PCmp | PAdd | PMul | PUnary | PAtom) -> false
        | PAnd, (PCmp | PAdd | PMul | PUnary | PAtom) -> false
        | PCmp, (PAdd | PMul | PUnary | PAtom) -> false
        | PAdd, (PMul | PUnary | PAtom) -> false
        | PMul, (PUnary | PAtom) -> false
        | PUnary, PAtom -> false
        | _ -> true
      in
      paren_if need s

  | EApp (f, args) ->
      let args_s =
        args |> List.map (string_of_expr ~ctx:PTop) |> String.concat ", "
      in
      f ^ "(" ^ args_s ^ ")"
 let string_of_sort = function
  | SInt -> "int"
  | SBool -> "bool"
  | SPtr -> "ptr"
  | SUser s -> s

let string_of_binder (x, so : ident * sort option) : string =
  match so with
  | None -> x
  | Some s -> x ^ ":" ^ string_of_sort s

let rec string_of_sl ?(ctx : prec = PTop) (p : sl) : string =
  match p with
  | STrue -> "\\true"
  | SFalse -> "\\false"
  | SEmp -> "emp"

  | SPure e ->
      
      string_of_expr ~ctx:ctx e

  | SHeap h ->
      string_of_heaplet h

  | SSep xs ->
      let xs' = List.filter (fun x -> x <> SEmp) xs in
      begin match xs' with
      | [] -> "emp"
      | [x] -> string_of_sl ~ctx:ctx x
      | _ ->
          let s =
            xs' |> List.map (string_of_sl ~ctx:PAnd) |> String.concat " ** "
          in
          paren_if (ctx <> PTop && ctx <> PAnd && ctx <> PAtom) s
      end

  | SAnd xs ->
      let xs' = xs in
      begin match xs' with
      | [] -> "\\true"
      | [x] -> string_of_sl ~ctx:ctx x
      | _ ->
          let s = xs' |> List.map (string_of_sl ~ctx:PAnd) |> String.concat " && " in
          paren_if (ctx = POr || ctx = PImpl) s
      end

  | SOr xs ->
      begin match xs with
      | [] -> "\\false"
      | [x] -> string_of_sl ~ctx:ctx x
      | _ ->
          let s = xs |> List.map (string_of_sl ~ctx:POr) |> String.concat " || " in
          paren_if (ctx = PImpl) s
      end

  | SNot q ->
      let s = "!(" ^ string_of_sl ~ctx:PTop q ^ ")" in
      paren_if (ctx <> PTop && ctx <> PUnary && ctx <> PAtom) s

  | SImplies (a, b) ->
      let sa = string_of_sl ~ctx:PImpl a in
      let sb = string_of_sl ~ctx:PImpl b in
      let s = sa ^ " => " ^ sb in
      paren_if (ctx <> PTop) s

  | SExists (bs, q) ->
      "exists " ^
      (bs |> List.map string_of_binder |> String.concat ", ") ^
      ". " ^ string_of_sl ~ctx:PTop q

  | SForall (bs, q) ->
      "forall " ^
      (bs |> List.map string_of_binder |> String.concat ", ") ^
      ". " ^ string_of_sl ~ctx:PTop q

and string_of_heaplet = function
  | HPt { loc; ty; value } ->
      
      let l = string_of_expr ~ctx:PAtom loc in
      let v = string_of_expr ~ctx:PTop value in
      l ^ "->" ^ ty ^ "*(" ^ v ^ ")"
  | HPred (name, args) ->
      let args_s =
        args |> List.map (string_of_expr ~ctx:PTop) |> String.concat ", "
      in
      name ^ "(" ^ args_s ^ ")"
 let string_of_clause ~(ret : ident option) (c : clause) : string =
  match c with
  | CReq p -> "req " ^ string_of_sl p ^ ";"
  | CEns p ->
      (match ret with
       | None -> "ens " ^ string_of_sl p ^ ";"
       | Some r -> "ens[" ^ r ^ "] " ^ string_of_sl p ^ ";")
  | CVar None -> "req Term[];"
  | CVar (Some e) -> "req Term[" ^ string_of_expr e ^ "];"

let string_of_block ~(ret : ident option) (b : block) : string =
  b |> List.map (string_of_clause ~ret) |> String.concat " "

let string_of_behavior ~(ret : ident option) (b : behavior) : string =
  let body_s = string_of_block ~ret b.body in
  let guard_is_true = (b.assumes = STrue) in
  match b.name, guard_is_true with
  | None, true -> body_s
  | _ ->
      let name_prefix =
        match b.name with
        | None -> ""
        | Some n -> n ^ ": "
      in
      name_prefix ^ string_of_sl b.assumes ^ " => " ^ body_s

let string_of_spec (s : spec) : string =
  let bs = s.behaviors in
  let needs_case =
    match bs with
    | [] -> false
    | [b] -> b.assumes <> STrue || b.name <> None
    | _ -> true
  in
  if needs_case then
    let body =
      bs |> List.map (string_of_behavior ~ret:s.ret) |> String.concat " "
    in
    "case {" ^ body ^ "};"
  else
    match bs with
    | [] -> ";"
    | [b] -> string_of_block ~ret:s.ret b.body
    | _ -> assert false

