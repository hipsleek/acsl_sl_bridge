open Sl_ast

module C = Core

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(*Helper functions*)
let rec atoms_of_heap (h : Sl_ast.heap) : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list =
  match h with
  | Atom (PointTo (p, t, v)) -> [ (p, t, v) ]
  | Sep (h1, h2) -> atoms_of_heap h1 @ atoms_of_heap h2

let ptrs_of_atoms (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) : StringSet.t =
  List.fold_left
    (fun acc (p, _, _) -> StringSet.add p acc)
    StringSet.empty atoms

let map_of_atoms (atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) : string StringMap.t =
  List.fold_left
    (fun acc (p, _t, v) -> StringMap.add p v acc)
    StringMap.empty atoms

let make_ensures 
  (pre_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  (post_atoms: (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) :C.predicate list =

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
            let lhs = C.heap_post p in
            let rhs = C.heap_pre q in
            buf := C.eq lhs rhs :: !buf
        | None -> ()
    )
    post_map;
  List.rev !buf

let rec string_of_arith = function
  | A_var x -> x
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)

let term_of_arith (e : Sl_ast.arith_expr) : C.term =
  match e with
  | A_var x -> C.T_var x
  | A_int n -> C.T_int n
  | A_add _
  | A_sub _
  | A_mul _
  | A_div _ -> C.T_var (string_of_arith e)

let get_predicate (e : Sl_ast.conditional_expr) : C.predicate =
  match e with
  | E_eq (e1, e2) -> C.P_eq  (term_of_arith e1, term_of_arith e2)
  | E_neq (e1, e2) -> C.P_neq (term_of_arith e1, term_of_arith e2)
  | E_lte (e1, e2) -> C.P_lte (term_of_arith e1, term_of_arith e2)
  | E_lt (e1, e2) -> C.P_lt  (term_of_arith e1, term_of_arith e2)
  | E_gte (e1, e2) -> C.P_gte (term_of_arith e1, term_of_arith e2)
  | E_gt (e1, e2) -> C.P_gt  (term_of_arith e1, term_of_arith e2)


(*branch functions*)
let make_simple_core
  (pre_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  (post_atoms: (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list) :C.spec =

  let ptrs = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
  let ptr_list = StringSet.elements ptrs in

  (* Default INOUT*)
  let params = List.map (fun p -> C.mk_param C.InOut p) ptr_list in
  let frame = ptr_list in
  let requires = List.map (fun p -> C.valid p) ptr_list in
  let ensures = make_ensures pre_atoms post_atoms in

  let behaviors : C.behavior = {
    assumes  = []; 
    requires;
    ensures;
    frame;
    variant = None
  } in

  {
    C.params;
    behaviors = [behaviors];
  }

let make_case_core sl_cases = 
  let global_ptrs_set =
    List.fold_left
      (fun acc c ->
          let add_heap acc h =
            let atoms = atoms_of_heap h in
            StringSet.union acc (ptrs_of_atoms atoms)
          in
          let acc = add_heap acc c.pre in
          add_heap acc c.post)
      StringSet.empty
      sl_cases
  in
  let global_ptrs = StringSet.elements global_ptrs_set in
  let params = List.map (fun p -> C.mk_param C.InOut p) global_ptrs in
  let behaviors =
    sl_cases
    |> List.map (fun c ->
            let pre_atoms = atoms_of_heap c.pre in
            let post_atoms = atoms_of_heap c.post in
            let frame_set = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
            let frame = StringSet.elements frame_set in
            let assumes  = [ get_predicate c.test ] in
            let requires = List.map (fun p -> C.valid p) global_ptrs in
            let ensures  = make_ensures pre_atoms post_atoms in
            let variant =
              match c.term with
              | None
              | Some Term_none -> None
              | Some (Term e)  -> Some (term_of_arith e)
            in
            {
              C.assumes;
              requires;
              ensures;
              frame;
              variant;
            })
  in

  {
    C.params;
    behaviors;
  }


let spec_to_core (s : Sl_ast.spec) : C.spec =
  match s with
  | Simple { pre; post } -> 
    let pre_atoms = atoms_of_heap pre in
    let post_atoms = atoms_of_heap post in
    make_simple_core pre_atoms post_atoms

  | Case sl_cases -> make_case_core sl_cases
  