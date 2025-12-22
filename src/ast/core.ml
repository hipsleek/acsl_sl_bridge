type ptr = string
type var = string
type ty = string

type mode = In | Out | InOut

type param = {
  name : var;
  mode : mode;
}

type phase = Pre | Post

type arith_op = Add | Sub | Mul | Div

type term =
  | TVar of phase * var          
  | TInt of int
  | TPtr of ptr                  
  | THeap of phase * ptr          
  | TResult                         
  | TArith of arith_op * term * term
  | TApp of string * term list
  | TIndex of phase * term * term
  | TLoad of phase * term

type rel =
  | Eq | Neq | Lt | Lte | Gt | Gte

type binder = {
  b_name : var;
  b_ty : ty option;               
}

type atom =
  | ARel of rel * term * term
  | APred of string * term list     

type predicate =
  | PTrue
  | PFalse
  | PAtom of atom
  | PNot of predicate
  | PAnd of predicate list
  | POr of predicate list
  | PImplies of predicate * predicate
  | PForall of binder list * predicate
  | PExists of binder list * predicate


type assignable =
  | AsVar of var                 
  | AsHeap of ptr                 
  | AsRange of ptr * term * term   
  | AsTerm of term                


type clause =
  | Assumes of predicate
  | Requires of predicate
  | Ensures of predicate
  | Assigns of assignable list
  | Variant of term

type behavior = {
  b_name : string option;         
  clauses : clause list;
}

type spec_kind =
  | FunctionContract
  | LoopContract

type spec = {
  kind : spec_kind;
  params : param list;
  behaviors : behavior list;
}
