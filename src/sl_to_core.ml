open Ast

module C = Core

let rec atoms_of_heap (h : Ast.heap) : (Ast.ptr * Ast.car_type * Ast.car) list =
  match h with
  | Atom (PointTo (p, t, v)) -> [ (p, t, v) ]
  | Sep (h1, h2) -> atoms_of_heap h1 @ atoms_of_heap h2

let heap_atoms_to_core (atoms : (Ast.ptr * Ast.car_type * Ast.car) list)
  : C.heap =
  List.map
    (fun (p, t, v) -> { C.loc = p; ty = t; value = v })
    atoms

let spec_to_core (s : Ast.spec) : C.spec =
  let pre_atoms  = atoms_of_heap s.pre in
  let post_atoms = atoms_of_heap s.post in
  {
    C.pre  = heap_atoms_to_core pre_atoms;
    C.post = heap_atoms_to_core post_atoms;
  }
