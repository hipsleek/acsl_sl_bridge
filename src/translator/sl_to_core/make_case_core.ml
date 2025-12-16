open Helper
open Sl_ast

module C = Core

let has_heap (a : Sl_ast.assertion) : bool =
  atoms_of_assertion a <> []

let make_case_term_expression (sl_cases : Sl_ast.case_spec list) : C.spec =
  let behaviors =
    sl_cases
    |> List.map (fun c ->
         let variant =
           match c.term with
           | None
           | Some Term_none -> None
           | Some (Term e)  -> Some (term_of_arith e)
         in
         let assumes = preds_of_assertion c.test in
         let ensures = preds_of_assertion c.post in
         {
           C.assumes;
           C.requires = [];
           C.ensures  = ensures;
           C.frame    = [];
           C.variant  = variant;
         })
  in
  { C.params = []; behaviors }

let make_case_heap_expression (sl_cases : Sl_ast.case_spec list) : C.spec =
  let global_ptrs_set =
    List.fold_left
      (fun acc c ->
         let add_assertion acc a =
           let atoms = atoms_of_assertion a in
           StringSet.union acc (ptrs_of_atoms atoms)
         in
         let acc = add_assertion acc c.pre in
         let acc = add_assertion acc c.post in
         acc)
      StringSet.empty
      sl_cases
  in
  let global_ptrs = StringSet.elements global_ptrs_set in
  let params = List.map (fun p -> Core_builder.mk_param C.InOut p) global_ptrs in

  let behaviors =
    sl_cases
    |> List.map (fun c ->
         let pre_atoms  = atoms_of_assertion c.pre in
         let post_atoms = atoms_of_assertion c.post in

         let frame_set =
           StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms)
         in
         let frame = StringSet.elements frame_set in

         let assumes  = preds_of_assertion c.test in
         let requires = List.map Core_builder.valid global_ptrs in
         let ensures  = make_ensures pre_atoms post_atoms in

         let variant =
           match c.term with
           | None
           | Some Term_none -> None
           | Some (Term e)  -> Some (term_of_arith e)
         in

         {
           C.assumes;
           C.requires;
           C.ensures;
           C.frame;
           C.variant;
         })
  in
  { C.params = params; behaviors }

let make_case_core (sl_cases : Sl_ast.case_spec list) : C.spec =
  let has_any_pure_post =
    List.exists (fun c -> not (has_heap c.post)) sl_cases
  in
  if has_any_pure_post then make_case_term_expression sl_cases
  else make_case_heap_expression sl_cases
