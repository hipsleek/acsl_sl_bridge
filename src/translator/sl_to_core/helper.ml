module C = Core
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let rec atoms_of_assertion (a : Sl_ast.assertion)
  : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list =
  match a with
  | Sl_ast.A_heap_atom (Sl_ast.PointTo (p, t, v)) -> [ (p, t, v) ]
  | Sl_ast.A_sep (a1, a2) -> atoms_of_assertion a1 @ atoms_of_assertion a2
  | Sl_ast.A_and (a1, a2) -> atoms_of_assertion a1 @ atoms_of_assertion a2
  | Sl_ast.A_emp
  | Sl_ast.A_pure _
  | Sl_ast.A_or _
  | Sl_ast.A_not _
  | Sl_ast.A_implies _
  | Sl_ast.A_sugar_prime _
  | Sl_ast.A_sugar_old _ -> []

let ptrs_of_atoms
    (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  : StringSet.t =
  List.fold_left
    (fun acc (p, _, _) -> StringSet.add p acc)
    StringSet.empty
    atoms

let map_of_atoms
    (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  : string StringMap.t =
  List.fold_left
    (fun acc (p, _t, v) -> StringMap.add p v acc)
    StringMap.empty
    atoms

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
           let rhs = Core_builder.heap_pre  q in
           buf := Core_builder.eq lhs rhs :: !buf
       | None -> ())
    post_map;
  List.rev !buf

let rec term_of_arith (e : Sl_ast.arith_expr) : C.term =
  match e with
  | Sl_ast.A_var x -> C.T_var (C.Post, x)
  | Sl_ast.A_post_var x -> C.T_var (C.Post, x)
  | Sl_ast.A_old inner ->
      begin match inner with
      | Sl_ast.A_var x -> C.T_var (C.Pre, x)
      | Sl_ast.A_post_var x -> C.T_var (C.Pre, x)
      | _ -> failwith "nested \\old over arithmetic not supported yet"
      end
  | Sl_ast.A_int n -> C.T_int n
  | Sl_ast.A_add (e1, e2) -> C.T_arith (C.Add, term_of_arith e1, term_of_arith e2)
  | Sl_ast.A_sub (e1, e2) -> C.T_arith (C.Sub, term_of_arith e1, term_of_arith e2)
  | Sl_ast.A_mul (e1, e2) -> C.T_arith (C.Mul, term_of_arith e1, term_of_arith e2)
  | Sl_ast.A_div (e1, e2) -> C.T_arith (C.Div, term_of_arith e1, term_of_arith e2)
  | Sl_ast.A_result -> C.T_result

let get_predicate (p : Sl_ast.pure_atom) : C.predicate =
  match p with
  | Sl_ast.P_eq  (e1, e2) -> C.P_eq  (term_of_arith e1, term_of_arith e2)
  | Sl_ast.P_neq (e1, e2) -> C.P_neq (term_of_arith e1, term_of_arith e2)
  | Sl_ast.P_lte (e1, e2) -> C.P_lte (term_of_arith e1, term_of_arith e2)
  | Sl_ast.P_lt  (e1, e2) -> C.P_lt  (term_of_arith e1, term_of_arith e2)
  | Sl_ast.P_gte (e1, e2) -> C.P_gte (term_of_arith e1, term_of_arith e2)
  | Sl_ast.P_gt  (e1, e2) -> C.P_gt  (term_of_arith e1, term_of_arith e2)

let rec subst_result_arith (r : string) (e : Sl_ast.arith_expr) : Sl_ast.arith_expr =
  match e with
  | Sl_ast.A_var x when x = r -> Sl_ast.A_result
  | Sl_ast.A_var _ -> e
  | Sl_ast.A_post_var _ -> e
  | Sl_ast.A_old e1 -> Sl_ast.A_old (subst_result_arith r e1)
  | Sl_ast.A_int _ -> e
  | Sl_ast.A_add (e1, e2) -> Sl_ast.A_add (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.A_sub (e1, e2) -> Sl_ast.A_sub (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.A_mul (e1, e2) -> Sl_ast.A_mul (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.A_div (e1, e2) -> Sl_ast.A_div (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.A_result -> Sl_ast.A_result

let subst_result_pure (r : string) (p : Sl_ast.pure_atom) : Sl_ast.pure_atom =
  match p with
  | Sl_ast.P_eq  (e1, e2) -> Sl_ast.P_eq  (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.P_neq (e1, e2) -> Sl_ast.P_neq (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.P_lte (e1, e2) -> Sl_ast.P_lte (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.P_lt  (e1, e2) -> Sl_ast.P_lt  (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.P_gte (e1, e2) -> Sl_ast.P_gte (subst_result_arith r e1, subst_result_arith r e2)
  | Sl_ast.P_gt  (e1, e2) -> Sl_ast.P_gt  (subst_result_arith r e1, subst_result_arith r e2)

let rec subst_result_assertion (r : string) (a : Sl_ast.assertion) : Sl_ast.assertion =
  match a with
  | Sl_ast.A_emp -> Sl_ast.A_emp
  | Sl_ast.A_heap_atom _ -> a
  | Sl_ast.A_sugar_prime _ -> a
  | Sl_ast.A_sugar_old _ -> a
  | Sl_ast.A_pure p -> Sl_ast.A_pure (subst_result_pure r p)
  | Sl_ast.A_sep (a1, a2) -> Sl_ast.A_sep (subst_result_assertion r a1, subst_result_assertion r a2)
  | Sl_ast.A_and (a1, a2) -> Sl_ast.A_and (subst_result_assertion r a1, subst_result_assertion r a2)
  | Sl_ast.A_or (a1, a2) -> Sl_ast.A_or (subst_result_assertion r a1, subst_result_assertion r a2)
  | Sl_ast.A_not a1 -> Sl_ast.A_not (subst_result_assertion r a1)
  | Sl_ast.A_implies (a1, a2) -> Sl_ast.A_implies (subst_result_assertion r a1, subst_result_assertion r a2)


let rec preds_of_assertion (a : Sl_ast.assertion) : C.predicate list =
  match a with
  | Sl_ast.A_pure p -> [ get_predicate p ]
  | Sl_ast.A_and (a1, a2) -> preds_of_assertion a1 @ preds_of_assertion a2
  | Sl_ast.A_emp -> []
  | _ -> failwith "preds_of_assertion: non-pure assertion where pure expected"
