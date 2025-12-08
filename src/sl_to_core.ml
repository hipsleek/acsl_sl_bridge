open Ast

module C = Core

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let rec atoms_of_heap (h : Ast.heap) : (Ast.ptr * Ast.car_type * Ast.car) list =
  match h with
  | Atom (PointTo (p, t, v)) -> [ (p, t, v) ]
  | Sep (h1, h2) -> atoms_of_heap h1 @ atoms_of_heap h2

let ptrs_of_atoms (atoms : (Ast.ptr * Ast.car_type * Ast.car) list) : StringSet.t =
  List.fold_left
    (fun acc (p, _, _) -> StringSet.add p acc)
    StringSet.empty atoms

let map_of_atoms (atoms : (Ast.ptr * Ast.car_type * Ast.car) list) : string StringMap.t =
  List.fold_left
    (fun acc (p, _t, v) -> StringMap.add p v acc)
    StringMap.empty atoms

let spec_to_core (s : Ast.spec) : C.spec =
  let pre_atoms = atoms_of_heap s.pre in
  let post_atoms = atoms_of_heap s.post in

  let post_map = map_of_atoms post_atoms in

  let ptrs = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
  let ptr_list = StringSet.elements ptrs in

  (* Default INOUT*)
  let params = List.map (fun p -> C.mk_param C.InOut p) ptr_list in

  let frame = ptr_list in

  let requires = List.map (fun p -> C.valid p) ptr_list in

  let ensures =
    let buf = ref [] in
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
  in

  {
    C.params;
    frame;
    requires;
    ensures;
  }