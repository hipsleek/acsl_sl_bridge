open Helper

let make_sugar_core (pairs : (Sl_ast.ptr * Sl_ast.ptr) list) : Core.spec =
  let ptrs_set = List.fold_left 
    (fun acc (p, q) -> StringSet.add p (StringSet.add q acc)) StringSet.empty pairs in
  let ptrs = StringSet.elements ptrs_set in
  let params = List.map (fun p -> Core_builder.mk_param C.InOut p) ptrs in
  let frame = ptrs in
  let requires = List.map Core_builder.valid ptrs in
  let ensures =
    List.map
      (fun (p, q) ->
         let lhs = Core_builder.heap_post p in
         let rhs = Core_builder.heap_pre  q in
         Core_builder.eq lhs rhs)
      pairs
  in
  let behavior : C.behavior =
    {
      C.assumes = [];
      requires;
      ensures;
      frame;
      variant = None;
    }
  in
  { C.params = params; behaviors = [ behavior ] }