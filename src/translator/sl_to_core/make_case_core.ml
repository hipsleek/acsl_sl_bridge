open Helper

module C = Core

let make_case_heap_expression (sl_cases : Sl_ast.case_spec list) : C.spec =
  (* Reject Post_expr inside Case: loops must go through Sl_ast.Loop now. *)
  let () =
    if List.exists (fun c ->
         match c.Sl_ast.post with
         | Sl_ast.Post_expr _ -> true
         | Sl_ast.Post_heap _ -> false)
       sl_cases
    then
      failwith
        "make_case_core: Case contains Post_expr; represent loops using `Loop (...)` instead."
  in

  (* Compute the global set of pointers appearing in any pre/post heap *)
  let global_ptrs_set =
    List.fold_left
      (fun acc c ->
         let add_heap acc h =
           let atoms = atoms_of_heap h in
           StringSet.union acc (ptrs_of_atoms atoms)
         in
         let acc = add_heap acc c.Sl_ast.pre in
         match c.Sl_ast.post with
         | Sl_ast.Post_heap h_post -> add_heap acc h_post
         | Sl_ast.Post_expr _ -> acc (* impossible due to check above *))
      StringSet.empty
      sl_cases
  in
  let global_ptrs = StringSet.elements global_ptrs_set in

  let params =
    List.map (fun p -> Core_builder.mk_param C.InOut p) global_ptrs
  in

  let behaviors =
    sl_cases
    |> List.map (fun c ->
         let pre_atoms = atoms_of_heap c.Sl_ast.pre in
         let post_atoms =
           match c.Sl_ast.post with
           | Sl_ast.Post_heap h_post -> atoms_of_heap h_post
           | Sl_ast.Post_expr _ -> [] (* impossible due to check above *)
         in

         (* Frame for this case: pointers mentioned in this case's pre or post heap *)
         let frame_set =
           StringSet.union (ptrs_of_atoms pre_atoms) (ptrs_of_atoms post_atoms)
         in
         let frame = StringSet.elements frame_set in

         let assumes  = [ get_predicate c.Sl_ast.test ] in
         let requires = List.map Core_builder.valid global_ptrs in
         let ensures  = make_ensures pre_atoms post_atoms in

         (* Keep variant if present (harmless for non-loop cases; ignored by contract printer) *)
         let variant =
           match c.Sl_ast.term with
           | None
           | Some Sl_ast.Term_none -> None
           | Some (Sl_ast.Term e)  -> Some (term_of_arith e)
         in

         {
           C.assumes;
           C.requires;
           C.ensures;
           C.frame;
           C.variant = variant;
         })
  in
  { C.params = params; behaviors }

let make_case_core (sl_cases : Sl_ast.case_spec list) : C.spec =
  make_case_heap_expression sl_cases
