type ptr = string
type car_type = string
type car = string

type heap_atom = 
  | PointTo of ptr * car_type * car 

type heap = 
  | Atom of heap_atom
  | Sep of heap * heap

type arith_expr =
  | A_var of string
  | A_post_var of string
  | A_old of arith_expr
  | A_int of int
  | A_add of arith_expr * arith_expr
  | A_sub of arith_expr * arith_expr
  | A_mul of arith_expr * arith_expr
  | A_div of arith_expr * arith_expr

type conditional_expr =
  | E_eq of arith_expr * arith_expr
  | E_neq of arith_expr * arith_expr
  | E_lte of arith_expr * arith_expr
  | E_lt of arith_expr * arith_expr
  | E_gte of arith_expr * arith_expr
  | E_gt of arith_expr * arith_expr

type terminate_expr =
  | Term_none
  | Term of arith_expr

type post_kind =
  | Post_heap of heap
  | Post_expr of conditional_expr list

type base_spec = {
  pre : heap;
  post : heap;
}

type case_spec = {
  test : conditional_expr;
  term : terminate_expr option;
  pre : heap;
  post : post_kind;
}

type spec =
  | Simple of base_spec
  | Sugar_prime of (ptr * ptr) list
  | Sugar_old of (ptr * ptr) list
  | Case of case_spec list

