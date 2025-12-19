 type ident = string

type sort =
  | SInt
  | SBool
  | SPtr
  | SUser of string

type c_type = string  
 type binop =
  | BAdd | BSub | BMul | BDiv | BMod
  | BEq | BNeq | BLt | BLe | BGt | BGe
  | BAnd | BOr
type unop = UNeg | UNot

type expr =
  | EVar of ident
  | EConstInt of int
  | EConstBool of bool
  | EResult                       
  | EUnop of unop * expr
  | EBinop of binop * expr * expr
  | EApp of ident * expr list   
  | EDeref of expr                
  | EOld of expr                
  | EPost of expr                
  
 type heaplet =
  | HPt of { loc : expr; ty : c_type; value : expr }   
  | HPred of ident * expr list                         

type sl =
  | STrue
  | SFalse
  | SPure of expr                     
  | SHeap of heaplet
  | SEmp
  | SSep of sl list                  
  | SAnd of sl list
  | SOr of sl list
  | SNot of sl
  | SImplies of sl * sl
  | SExists of (ident * sort option) list * sl
  | SForall of (ident * sort option) list * sl
 type clause =
  | CReq of sl
  | CEns of sl
  | CVar of expr option

type block = clause list

type behavior = {
  name : string option;
  assumes : sl;     
  body : block;  
}

type spec = {
  ret : ident option;     
  behaviors: behavior list;    
}
