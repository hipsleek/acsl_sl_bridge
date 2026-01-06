(* acsl_ast.ml *)

type ident = string

type c_type = string

type sort =
  | SInt
  | SBool
  | SPtr
  | SUser of string

type binop =
  | BAdd | BSub | BMul | BDiv | BMod
  | BEq | BNeq | BLt | BLe | BGt | BGe
  | BAnd | BOr

type unop =
  | UNeg
  | UNot

type loop_label =
  | LoopEntry
  | LoopCurrent
  | UserLabel of ident

type expr =
  | EVar of ident
  | EConstInt of int
  | EConstBool of bool
  | EResult
  | ENull
  | EUnop of unop * expr
  | EBinop of binop * expr * expr
  | EApp of ident * expr list
  | EDeref of expr
  | EOld of expr
  | EAt of expr * loop_label
  | EIndex of expr * expr
  | ERange of expr * expr

type assigns_target =
  | AVar of ident
  | ADeref of expr
  | ARange of expr * expr * expr

type assigns =
  | ANothing
  | AItems of assigns_target list

type pred =
  | PTrue
  | PFalse
  | PCmp of binop * expr * expr
  | PApp of ident * expr list
  | PAnd of pred list
  | POr of pred list
  | PNot of pred
  | PImplies of pred * pred
  | PIff of pred * pred
  | PForall of (ident * sort option) list * pred
  | PExists of (ident * sort option) list * pred
  | PValid of expr
  | PValidRead of expr

type behavior = {
  name : ident option;
  assumes : pred;
  ensures : pred;
}

type fun_spec = {
  requires : pred option;
  assigns : assigns;
  behaviors : behavior list;
  ensures : pred option;
  complete_behaviors : bool;
  disjoint_behaviors : bool;
}

type loop_spec = {
  invariants : pred list;
  assigns : assigns;
  variant : expr option;
}

type spec =
  | FunSpec of fun_spec
  | LoopSpec of loop_spec
