type ptr = string
type var = string
type car_type = string
type car = string

type arith_expr =
  | A_var of var
  | A_post_var of var
  | A_old of arith_expr
  | A_int of int
  | A_add of arith_expr * arith_expr
  | A_sub of arith_expr * arith_expr
  | A_mul of arith_expr * arith_expr
  | A_div of arith_expr * arith_expr

type pure_atom =
  | P_eq of arith_expr * arith_expr
  | P_neq of arith_expr * arith_expr
  | P_lte of arith_expr * arith_expr
  | P_lt of arith_expr * arith_expr
  | P_gte of arith_expr * arith_expr
  | P_gt of arith_expr * arith_expr

type terminate_expr =
  | Term_none
  | Term of arith_expr

type heap_atom =
  | PointTo of ptr * car_type * car

type assertion =
  | A_emp
  | A_heap_atom of heap_atom
  | A_sep of assertion * assertion
  | A_pure of pure_atom
  | A_and of assertion * assertion
  | A_or of assertion * assertion
  | A_not of assertion
  | A_implies of assertion * assertion
  | A_sugar_prime of (ptr * ptr) list
  | A_sugar_old of (ptr * ptr) list

type base_spec = {
  pre : assertion;
  post : assertion;
}

type case_spec = {
  test : assertion;
  term : terminate_expr option;
  pre : assertion;
  post : assertion;
}

type spec =
  | Simple of base_spec
  | Ens of assertion
  | Case of case_spec list
