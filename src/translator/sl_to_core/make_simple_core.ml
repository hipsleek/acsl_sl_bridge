open Helper

let make_simple_core
    (pre  : Sl_ast.assertion)
    (post : Sl_ast.assertion)
  : Core.spec =
  let pre_atoms  = atoms_of_assertion pre in
  let post_atoms = atoms_of_assertion post in

  let ptrs = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
  let ptr_list = StringSet.elements ptrs in

  let params   = List.map (fun p -> Core_builder.mk_param Core.InOut p) ptr_list in
  let frame    = ptr_list in
  let requires = List.map Core_builder.valid ptr_list in
  let ensures  = make_ensures pre_atoms post_atoms in

  let behavior : Core.behavior =
    { Core.assumes = []; requires; ensures; frame; variant = None }
  in
  { Core.params = params; behaviors = [ behavior ] }
