type ptr = string
type var = string
type car_type = string
type car = string

type arith =
  | AVar of var
  | APostVar of var
  | AOld of arith
  | AInt of int
  | AAdd of arith * arith
  | ASub of arith * arith
  | AMul of arith * arith
  | ADiv of arith * arith
  | AResult

type pure_atom =
  | PEq  of arith * arith
  | PNeq of arith * arith
  | PLte of arith * arith
  | PLt  of arith * arith
  | PGte of arith * arith
  | PGt  of arith * arith

type terminate_expr =
  | TermNone
  | Term of arith

type heap_atom =
  | PointTo of ptr * car_type * car

type assertion =
  | AEmp
  | AHeapAtom of heap_atom
  | ASep of assertion * assertion
  | APure of pure_atom
  | AAnd of assertion * assertion
  | AOr of assertion * assertion
  | ANot of assertion
  | AImplies of assertion * assertion
  (* Keep sugar (denormalised) *)
  | ASugarPrime of (ptr * ptr) list
  | ASugarOld of (ptr * ptr) list

type base_spec = {
  pre : assertion;
  post : assertion;
}

type case_spec = {
  test : assertion;
  term : terminate_expr option;
  pre  : assertion;
  post : assertion;
}

type ens_spec = {
  ret  : var option;
  post : assertion;
}

type spec =
  | Simple of base_spec
  | Ens of ens_spec
  | Case of case_spec list
