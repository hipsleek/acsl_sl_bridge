module C = Core
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(*Relation makers*)
let rec atoms_of_heap (h : Sl_ast.heap) : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list =
  match h with
  | Atom (PointTo (p, t, v)) -> [ (p, t, v) ]
  | Sep (h1, h2) -> atoms_of_heap h1 @ atoms_of_heap h2

let ptrs_of_atoms (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) : StringSet.t =
  List.fold_left (fun acc (p, _, _) -> StringSet.add p acc) StringSet.empty atoms

let map_of_atoms (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) : string StringMap.t =
  List.fold_left (fun acc (p, _t, v) -> StringMap.add p v acc) StringMap.empty atoms

let make_ensures
    (pre_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
    (post_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  : C.predicate list =
  let buf = ref [] in
  let post_map = map_of_atoms post_atoms in
  StringMap.iter
    (fun p v_post ->
       let src_opt =
         try
           let q =
             pre_atoms
             |> List.find (fun (_q, _t, v_pre) -> v_pre = v_post)
             |> fun (q, _t, _v) -> q
           in
           Some q
         with Not_found -> None
       in
       match src_opt with
       | Some q ->
           let lhs = Core_builder.heap_post p in
           let rhs = Core_builder.heap_pre q in
           buf := Core_builder.eq lhs rhs :: !buf
       | None -> ())
    post_map;
  List.rev !buf

(*1:1 translation*)
let rec term_of_arith (e : Sl_ast.arith_expr) : C.term =
  match e with
  | A_var x -> C.T_var (C.Post, x)
  | A_post_var x -> C.T_var (C.Post, x)
  | A_old inner -> begin match inner with
      | A_var x -> C.T_var (C.Pre, x)
      | A_post_var x -> C.T_var (C.Pre, x)
      | _ -> failwith "nested \\old over arithmetic not supported yet"
      end
  | A_int n -> C.T_int n
  | A_add (e1, e2) -> C.T_arith (C.Add, term_of_arith e1, term_of_arith e2)
  | A_sub (e1, e2) -> C.T_arith (C.Sub, term_of_arith e1, term_of_arith e2)
  | A_mul (e1, e2) -> C.T_arith (C.Mul, term_of_arith e1, term_of_arith e2)
  | A_div (e1, e2) -> C.T_arith (C.Div, term_of_arith e1, term_of_arith e2)


let get_predicate (e : Sl_ast.conditional_expr) : C.predicate =
  match e with
  | E_eq  (e1, e2) -> C.P_eq  (term_of_arith e1, term_of_arith e2)
  | E_neq (e1, e2) -> C.P_neq (term_of_arith e1, term_of_arith e2)
  | E_lte (e1, e2) -> C.P_lte (term_of_arith e1, term_of_arith e2)
  | E_lt  (e1, e2) -> C.P_lt  (term_of_arith e1, term_of_arith e2)
  | E_gte (e1, e2) -> C.P_gte (term_of_arith e1, term_of_arith e2)
  | E_gt  (e1, e2) -> C.P_gt  (term_of_arith e1, term_of_arith e2)