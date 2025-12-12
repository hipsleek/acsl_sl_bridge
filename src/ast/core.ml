(* the idea of this interface is generalise and distill the key information.
so, it writes about the io variables, memory loc to be chanhged, the pre-state, the relation bw
pre state and post state*)

type ptr = string
type ty = string
type var = string

type mode = 
  | In
  | Out
  | InOut

type phase =
  | Pre
  | Post

type term =
  | T_var of phase * var
  | T_int of int
  | T_heap of phase * ptr
  | T_ptr of ptr  

type predicate =
  | P_eq of term * term
  | P_neq of term * term
  | P_lte of term * term
  | P_lt of term * term
  | P_gte of term * term
  | P_gt of term * term
  | P_valid of ptr

type param = {
  name : var;
  (* ty : ty; *)
  mode : mode;
}

type behavior = {
  assumes : predicate list; 
  requires : predicate list;
  ensures : predicate list;
  frame : ptr list;
  variant : term option;
}

type spec = {
  params : param list;
  behaviors : behavior list;
}




(* Preety prints*)
