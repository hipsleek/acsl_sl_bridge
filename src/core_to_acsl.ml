open Core

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let map_of_atoms (atoms : heap) : string StringMap.t =
  List.fold_left
    (fun acc atom -> StringMap.add atom.loc atom.value acc)
    StringMap.empty atoms

let ptrs_of_atoms (atoms : heap) : StringSet.t =
  List.fold_left
    (fun acc atom -> StringSet.add atom.loc acc)
    StringSet.empty atoms

let spec_to_acsl (s : spec) : string =
  let pre_atoms  = s.pre in
  let post_atoms = s.post in

  (* let pre_map = map_of_atoms pre_atoms in *)
  let post_map = map_of_atoms post_atoms in

  let ptrs =
    StringSet.union
      (ptrs_of_atoms pre_atoms)
      (ptrs_of_atoms post_atoms)
  in
  let ptr_list = StringSet.elements ptrs in

  let requires_clause =
    match ptr_list with
    (* | [] -> "\\true" *)
    | _  ->
        ptr_list
        |> List.map (fun p -> Printf.sprintf "\\valid(%s)" p)
        |> String.concat " && "
  in

  let assigns_clause =
    match ptr_list with
    (* | [] -> "\\nothing" *)
    | _  ->
        ptr_list
        |> List.map (fun p -> Printf.sprintf "*%s" p)
        |> String.concat ", "
  in

  let ensures_clauses =
    let buf = ref [] in
    (*Idea is that given the post-condition mappings, we wnt to find the pointer's pre-condition mapping*)
    (*So a naiive loop, iter function below, is used to find the inital pointer in the pre-condtion mappings*)
    StringMap.iter
      (fun p v_post ->
         let src_opt =
           try
             let src =
               List.find
                 (fun pre_atom -> pre_atom.value = v_post)
                 pre_atoms
             in
             Some src.loc
           with Not_found -> None
         in
         match src_opt with
         | Some q ->
             buf :=
               Printf.sprintf "*%s == \\old(*%s)" p q
               :: !buf (*After cons with buf, we move the pointer of buf back to the head*)
         | None -> () (*No match found, so do nothing*)
      )
      post_map;
    List.rev !buf
  in

  match ensures_clauses with
  | [] ->
      Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
*/"
        requires_clause assigns_clause
  | _ ->
      let ensures_clause = String.concat " && " ensures_clauses in
      Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
  ensures  %s;
*/"
        requires_clause assigns_clause ensures_clause
