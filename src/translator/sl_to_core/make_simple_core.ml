open Helper

let make_simple_core
    (pre_atoms  : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
    (post_atoms : (Sl_ast.ptr * Sl_ast.car_type * Sl_ast.car) list)
  : Core.spec =
  (* Gather all pointers mentioned in pre/post heaps *)
  let ptrs_set =
    StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms)
  in
  let ptrs = StringSet.elements ptrs_set in

  (* All pointers are treated as inout parameters *)
  let params =
    List.map (fun p -> Core_builder.mk_param Core.InOut p) ptrs
  in

  let frame    = ptrs in
  let requires = List.map Core_builder.valid ptrs in
  let ensures  = make_ensures pre_atoms post_atoms in

  let behavior : Core.behavior =
    {
      Core.assumes  = [];
      Core.requires = requires;
      Core.ensures  = ensures;
      Core.frame    = frame;
      Core.variant  = None;
    }
  in
  { Core.params = params; behaviors = [ behavior ] }
