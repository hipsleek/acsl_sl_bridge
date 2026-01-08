(* src/ast_printer/acsl_ast_printer.ml *)

open Acsl_ast

type prec =
  | PTop
  | PIff
  | PImpl
  | POr
  | PAnd
  | PCmp
  | PAdd
  | PMul
  | PUnary
  | PAtom

let prec_to_int = function
  | PTop -> 0
  | PIff -> 1
  | PImpl -> 2
  | POr -> 3
  | PAnd -> 4
  | PCmp -> 5
  | PAdd -> 6
  | PMul -> 7
  | PUnary -> 8
  | PAtom -> 9

let need_parens ~(parent : prec) ~(child : prec) : bool =
  prec_to_int child < prec_to_int parent

let paren_if b s = if b then "(" ^ s ^ ")" else s

let string_of_binop = function
  | BAdd -> "+" | BSub -> "-" | BMul -> "*" | BDiv -> "/" | BMod -> "%"
  | BEq -> "==" | BNeq -> "!=" | BLt -> "<" | BLe -> "<="
  | BGt -> ">" | BGe -> ">="
  | BAnd -> "&&" | BOr -> "||"

let string_of_unop = function
  | UNeg -> "-"
  | UNot -> "!"

let prec_of_binop = function
  | BOr -> POr
  | BAnd -> PAnd
  | BEq | BNeq | BLt | BLe | BGt | BGe -> PCmp
  | BAdd | BSub -> PAdd
  | BMul | BDiv | BMod -> PMul

let string_of_loop_label = function
  | LoopEntry -> "LoopEntry"
  | LoopCurrent -> "LoopCurrent"
  | UserLabel s -> s

(* ---------- Expr precedence helpers ---------- *)

let prec_of_expr = function
  | EVar _ | EConstInt _ | EConstBool _ | EResult | ENull -> PAtom
  | EApp _ | EIndex _ -> PAtom
  | EOld _ | EAt _ -> PAtom
  | ERange _ -> PAtom
  | EDeref _ | EUnop _ -> PUnary
  | EBinop (op, _, _) -> prec_of_binop op

let binop_of_expr = function
  | EBinop (op, _, _) -> Some op
  | _ -> None

(* Extra parentheses rules to preserve AST meaning for non-associative / right-nesting:
   - a + (b - c) needs parens on right child if it's subtraction
   - a - (b + c) needs parens on right child if it's add/sub
   - similarly for *, /, % on the right child
*)
let need_parens_right_child (parent_op : binop) (right : expr) : bool =
  match parent_op, binop_of_expr right with
  | BAdd, Some BSub -> true
  | BSub, Some (BAdd | BSub) -> true
  | BMul, Some (BDiv | BMod) -> true
  | BDiv, Some (BMul | BDiv | BMod) -> true
  | BMod, Some (BMul | BDiv | BMod) -> true
  | _ -> false

(* ---------- Expr printer ---------- *)

let rec string_of_expr ?(ctx = PTop) (e : expr) : string =
  match e with
  | EVar x -> x
  | EConstInt n -> string_of_int n
  | EConstBool true -> "\\true"
  | EConstBool false -> "\\false"
  | EResult -> "\\result"
  | ENull -> "NULL"

  | EOld e1 ->
      "\\old(" ^ string_of_expr e1 ^ ")"

  | EAt (e1, lab) ->
      "\\at(" ^ string_of_expr e1 ^ ", " ^ string_of_loop_label lab ^ ")"

  | ERange (lo, hi) ->
      "(" ^ string_of_expr lo ^ " .. " ^ string_of_expr hi ^ ")"

  | EApp (f, args) ->
      f ^ "(" ^ (args |> List.map string_of_expr |> String.concat ", ") ^ ")"

  | EIndex (a, i) ->
      string_of_expr ~ctx:PAtom a ^ "[" ^ string_of_expr i ^ "]"

  | EDeref e1 ->
      (* IMPORTANT: do NOT re-parenthesize; child call already knows it's under unary context *)
      let inner = string_of_expr ~ctx:PUnary e1 in
      let s = "*" ^ inner in
      paren_if (need_parens ~parent:ctx ~child:PUnary) s

  | EUnop (op, e1) ->
      (* IMPORTANT: do NOT re-parenthesize; child call already knows it's under unary context *)
      let inner = string_of_expr ~ctx:PUnary e1 in
      let s = string_of_unop op ^ inner in
      paren_if (need_parens ~parent:ctx ~child:PUnary) s

  | EBinop (op, a, b) ->
      (* Pretty-print unary neg when encoded as (0 - e) *)
      begin match op, a with
      | BSub, EConstInt 0 ->
          let inner = string_of_expr ~ctx:PUnary b in
          let s = "-" ^ inner in
          paren_if (need_parens ~parent:ctx ~child:PUnary) s
      | _ ->
          let p = prec_of_binop op in
          let sa = string_of_expr ~ctx:p a in
          let sb = string_of_expr ~ctx:p b in
          let sb = paren_if (need_parens_right_child op b) sb in
          let s = sa ^ " " ^ string_of_binop op ^ " " ^ sb in
          paren_if (need_parens ~parent:ctx ~child:p) s
      end

(* ---------- Pred precedence helpers ---------- *)

let prec_of_pred = function
  | PTrue | PFalse -> PAtom
  | PValid _ | PValidRead _ | PApp _ -> PAtom
  | PForall _ | PExists _ -> PAtom
  | PNot _ -> PUnary
  | PCmp _ -> PCmp
  | PAnd _ -> PAnd
  | POr _ -> POr
  | PImplies _ -> PImpl
  | PIff _ -> PIff

let string_of_sort = function
  | SInt -> "integer"
  | SBool -> "boolean"
  | SPtr -> "ptr"
  | SUser s -> s

let string_of_binder (x, so) =
  match so with
  | None -> x
  | Some s -> string_of_sort s ^ " " ^ x

let string_of_assigns_target = function
  | AVar x -> x
  | ADeref e -> "*" ^ string_of_expr ~ctx:PUnary e
  | ARange (base, lo, hi) ->
      string_of_expr base ^ "[" ^ string_of_expr lo ^ " .. " ^ string_of_expr hi ^ "]"

let string_of_assigns = function
  | ANothing -> "\\nothing"
  | AItems xs -> xs |> List.map string_of_assigns_target |> String.concat ", "

(* ---------- Pred printer ---------- *)

let rec string_of_pred ?(ctx = PTop) (p : pred) : string =
  match p with
  | PTrue -> "\\true"
  | PFalse -> "\\false"

  | PValid e ->
      "\\valid(" ^ string_of_expr e ^ ")"

  | PValidRead e ->
      "\\valid_read(" ^ string_of_expr e ^ ")"

  | PApp (f, args) ->
      f ^ "(" ^ (args |> List.map string_of_expr |> String.concat ", ") ^ ")"

  | PCmp (op, a, b) ->
      let sa = string_of_expr ~ctx:PCmp a in
      let sb = string_of_expr ~ctx:PCmp b in
      let s = sa ^ " " ^ string_of_binop op ^ " " ^ sb in
      paren_if (need_parens ~parent:ctx ~child:PCmp) s

  | PNot p1 ->
      (* exactly one set of parens, always *)
      "!(" ^ string_of_pred ~ctx:PTop p1 ^ ")"

  | PAnd xs ->
      let s = xs |> List.map (string_of_pred ~ctx:PAnd) |> String.concat " && " in
      paren_if (need_parens ~parent:ctx ~child:PAnd) s

  | POr xs ->
      let s = xs |> List.map (string_of_pred ~ctx:POr) |> String.concat " || " in
      paren_if (need_parens ~parent:ctx ~child:POr) s

  | PImplies (a, b) ->
      (* Tests expect parentheses around both sides *)
      let sa = "(" ^ string_of_pred ~ctx:PTop a ^ ")" in
      let sb = "(" ^ string_of_pred ~ctx:PTop b ^ ")" in
      let s = sa ^ " ==> " ^ sb in
      paren_if (need_parens ~parent:ctx ~child:PImpl) s

  | PIff (a, b) ->
      (* Tests expect parentheses around both sides *)
      let sa = "(" ^ string_of_pred ~ctx:PTop a ^ ")" in
      let sb = "(" ^ string_of_pred ~ctx:PTop b ^ ")" in
      let s = sa ^ " <==> " ^ sb in
      paren_if (need_parens ~parent:ctx ~child:PIff) s

  | PForall (bs, body) ->
      "\\forall "
      ^ (bs |> List.map string_of_binder |> String.concat ", ")
      ^ "; " ^ string_of_pred ~ctx:PTop body

  | PExists (bs, body) ->
      "\\exists "
      ^ (bs |> List.map string_of_binder |> String.concat ", ")
      ^ "; " ^ string_of_pred ~ctx:PTop body

(* ---------- Spec pretty-print ---------- *)

let pp_line buf s =
  Buffer.add_string buf "  ";
  Buffer.add_string buf s;
  Buffer.add_string buf "\n"

let pp_behavior buf (b : behavior) =
  match b.name with
  | None -> ()
  | Some n ->
      pp_line buf ("behavior " ^ n ^ ":");
      pp_line buf ("  assumes " ^ string_of_pred b.assumes ^ ";");
      pp_line buf ("  ensures " ^ string_of_pred b.ensures ^ ";")

let string_of_fun_spec (fs : fun_spec) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "/*@\n";

  (* Your tests expect requires even when absent *)
  begin match fs.requires with
  | None -> pp_line buf "requires \\true;"
  | Some p -> pp_line buf ("requires " ^ string_of_pred p ^ ";")
  end;

  pp_line buf ("assigns " ^ string_of_assigns fs.assigns ^ ";");

  begin match fs.behaviors with
  | [] ->
      begin match fs.ensures with
      | None -> ()
      | Some p -> pp_line buf ("ensures " ^ string_of_pred p ^ ";")
      end
  | bs ->
      List.iter (pp_behavior buf) bs;
      if fs.complete_behaviors then pp_line buf "complete behaviors;";
      if fs.disjoint_behaviors then pp_line buf "disjoint behaviors;"
  end;

  Buffer.add_string buf "*/";
  Buffer.contents buf

let string_of_loop_spec (ls : loop_spec) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "/*@\n";
  ls.invariants
  |> List.iter (fun p -> pp_line buf ("loop invariant " ^ string_of_pred p ^ ";"));
  pp_line buf ("loop assigns " ^ string_of_assigns ls.assigns ^ ";");
  begin match ls.variant with
  | None -> ()
  | Some e -> pp_line buf ("loop variant " ^ string_of_expr e ^ ";")
  end;
  Buffer.add_string buf "*/";
  Buffer.contents buf

let string_of_spec (s : spec) : string =
  match s with
  | FunSpec fs -> string_of_fun_spec fs
  | LoopSpec ls -> string_of_loop_spec ls
