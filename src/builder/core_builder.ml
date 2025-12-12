open Core

let mk_param mode name : param = { name; mode; }

let var_pre x = T_var (Pre, x)
let var_post x = T_var (Post, x)

let heap_pre (p : ptr) : term = T_heap (Pre, p)
let heap_post (p : ptr) : term = T_heap (Post, p)

let eq (t1 : term) (t2 : term) : predicate = P_eq (t1, t2)
let neq (t1 : term) (t2 : term) : predicate = P_neq (t1, t2)
let lte (t1 : term) (t2 : term) : predicate = P_lte (t1, t2)
let lt (t1 : term) (t2 : term) : predicate = P_lt (t1, t2)
let gte (t1 : term) (t2 : term) : predicate = P_gte (t1, t2)
let gt (t1 : term) (t2 : term) : predicate = P_gt (t1, t2)
let valid (p : ptr) : predicate = P_valid p

let mk_behavior
    ?(assumes = [])
    ?(requires = [])
    ?(ensures = [])
    ?(frame = [])
    ?variant
    ()
  : behavior =
  { assumes; requires; ensures; frame; variant }