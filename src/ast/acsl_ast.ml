type ident = string

type binop = | Eq | Neq | Lt | Lte | Gt | Gte | Add | Sub | Mul | Div

type term =
  | TVar of ident
  | TInt of int
  | TDeref of term
  | TOld of term
  | TApp of string * term list
  | TBinOp of binop * term * term

type predicate = term

type behavior = {
  b_name: string option;
  b_assumes: predicate list;
  b_requires: predicate list;
  b_ensures: predicate list;
}

type contract = {
  assigns : term list;
  behaviors : behavior list;
}

type loop_contract = {
  l_invariants : predicate list;
  l_assigns    : term list;
  l_variant    : term option;
}


