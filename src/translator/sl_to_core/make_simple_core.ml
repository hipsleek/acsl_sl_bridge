open Helper

let make_simple_core
    (pre_atoms  : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
    (post_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  : Core.spec =
  (*Get all pointers*)
  let ptrs = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
  let ptr_list = StringSet.elements ptrs in

  (*Make all variables inout*)
  let params = List.map (fun p -> Core_builder.mk_param Core.InOut p) ptr_list in
  let frame = ptr_list in
  let requires = List.map Core_builder.valid ptr_list in (*get valid pointers*)
  let ensures = make_ensures pre_atoms post_atoms in

  let behavior : Core.behavior =
    {
      Core.assumes  = [];
      requires;
      ensures;
      frame;
      variant = None;
    }
  in
  { Core.params = params; behaviors = [ behavior ] }