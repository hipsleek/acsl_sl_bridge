open Helper

let make_case_core (sl_cases : Sl_ast.case_spec list) : C.spec =
  let has_post_expr =
    List.exists
      (fun c ->
         match c.Sl_ast.post with
         | Post_expr _ -> true
         | Post_heap _ -> false)
      sl_cases
  in
  if has_post_expr then
    let behaviors =
      (*Pattern match the behaviours to extract the test/condtional and their corresponding terminating consequent*)
      sl_cases
      |> List.map (fun c ->
           let assumes = [ get_predicate c.Sl_ast.test ] in
           let variant =
             match c.term with
             | None
             | Some Term_none -> None
             | Some (Term e)  -> Some (term_of_arith e)
           in
           {
             C.assumes;
             C.requires = [];
             C.ensures = [];
             C.frame = [];
             C.variant = variant;
           })
    in { C.params = []; behaviors }
  else
    let global_ptrs_set =
      List.fold_left
        (fun acc c ->
           let add_heap acc h =
             let atoms = atoms_of_heap h in
             StringSet.union acc (ptrs_of_atoms atoms)
           in
           let acc = add_heap acc c.Sl_ast.pre in
           match c.post with
           | Post_heap h_post -> add_heap acc h_post
           | Post_expr _ -> acc ) (*ignore*)
        StringSet.empty
        sl_cases
    in
    let global_ptrs = StringSet.elements global_ptrs_set in
    let params      = List.map (fun p -> Core_builder.mk_param C.InOut p) global_ptrs in

    let behaviors =
      sl_cases
      |> List.map (fun c ->
           let pre_atoms = atoms_of_heap c.Sl_ast.pre in
           let post_atoms =
             match c.post with
             | Post_heap h_post -> atoms_of_heap h_post
             | Post_expr _ -> [] (*ignore*)
           in
           let frame_set = StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms) in
           let frame  = StringSet.elements frame_set in
           let assumes  = [ get_predicate c.test ] in
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
             C.requires = requires;
             C.ensures = ensures;
             C.frame = frame;
             C.variant = variant;
           })
    in
    { C.params = params; behaviors }