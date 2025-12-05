open Ast

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let rec atoms_of_heap (h : heap) : (ptr * car) list =
  match h with
  | Atom (PointTo (p, v)) -> [ (p, v) ]
  | Sep (h1, h2) -> atoms_of_heap h1 @ atoms_of_heap h2


(*Eg: a -> int*(u)   =>   [("a", "u")]*)
let map_of_atoms (atoms : (ptr * car) list) : car StringMap.t =
  List.fold_left
    (fun acc (p, v) -> StringMap.add p v acc)
    StringMap.empty atoms

(*Eg: a -> int*(u)   =>   {"a"}*)
let ptrs_of_atoms (atoms : (ptr * car) list) : StringSet.t =
  List.fold_left
    (fun acc (p, _) -> StringSet.add p acc)
    StringSet.empty atoms


let sl_spec_to_acsl (s : spec) : string =
  let pre_atoms = atoms_of_heap s.pre in
  let post_atoms = atoms_of_heap s.post in

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
    | _ ->
        ptr_list
        |> List.map (fun p -> Printf.sprintf "\\valid(%s)" p)
        |> String.concat " && "
  in

  let assigns_clause =
    match ptr_list with
    (* | [] -> "\\nothing" *)
    | _ ->
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
            Some (
              fst
                (List.find
                   (fun (_q, v_pre) -> v_pre = v_post)
                   pre_atoms)
            )
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

  let acsl =
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
  in
  acsl
