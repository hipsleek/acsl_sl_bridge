type ident = string

type binop =
  | Eq | Neq | Lt | Lte | Gt | Gte
  | Add | Sub | Mul | Div

type label =
  | LoopEntry
  | Here
  | Old
  | Label of string

type term =
  | TVar of ident
  | TInt of int
  | TDeref of term
  | TOld of term
  | TResult
  | TApp of string * term list
  | TBinOp of binop * term * term
  | TAt of term * label
  | TIndex of term * term
  | TRange of term * term

type rel = Eq | Neq | Lt | Lte | Gt | Gte

type predicate =
  | PTrue
  | PFalse
  | PRel of rel * term * term
  | PApp of string * term list
  | PNot of predicate
  | PAnd of predicate list
  | POr of predicate list
  | PImplies of predicate * predicate
  | PForall of (ident * string option) list * predicate
  | PExists of (ident * string option) list * predicate

type assigns =
  | ANothing
  | AList of term list

type behavior = {
  b_name : string option;
  b_assumes : predicate list;
  b_ensures : predicate list;
}

type contract = {
  requires : predicate list;
  assigns : assigns;
  behaviors : behavior list;
}

type loop_contract = {
  l_invariants : predicate list;
  l_assigns : assigns;
  l_variant : term option;
}
