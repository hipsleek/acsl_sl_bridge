open Core

let get_behaviors (s : spec) : behavior =
  match s.behaviors with
  | b :: _ -> b (*Match head to see if type behaviour*)
  | [] -> failwith "core_to_acsl: spec has no behaviors"

let string_of_term_in_ensures (t : term) : string =
  match t with
  | T_heap (Pre, p) -> Printf.sprintf "\\old(*%s)" p
  | T_heap (Post, p) -> Printf.sprintf "*%s" p
  | T_var x -> x
  | T_int n -> string_of_int n
  | T_ptr p -> p


let requires_clause (b : behavior) : string =
  match b.requires with
  | [] -> "\\true"
  | preds ->
      preds
      |> List.map (function
             | P_valid p -> Printf.sprintf "\\valid(%s)" p
             | P_eq _ 
             | P_neq _
             | P_lte _
             | P_lt _
             | P_gte _
             | P_gt _ ->
                 failwith "Core_to_acsl.requires_clause: unsupported predicate")
      |> String.concat " && "

let assigns_clause (b : behavior) : string =
  match b.frame with
  (* | [] -> "\\nothing" *)
  | ptrs ->
      ptrs
      |> List.map (fun p -> Printf.sprintf "*%s" p)
      |> String.concat ", "

let ensures_clause (b : behavior) : string option =
  match b.ensures with
  (* | [] -> None *)
  | preds ->
      let parts =
        preds
        |> List.map (function
               | P_eq (t1, t2) ->
                   Printf.sprintf "%s == %s"
                     (string_of_term_in_ensures t1)
                     (string_of_term_in_ensures t2)
               | P_valid _
               | P_neq _
               | P_lte _
               | P_lt _
               | P_gte _
               | P_gt _ ->
                   failwith "Core_to_acsl.ensures_clause: unsupported predicate")
      in
      Some (String.concat " && " parts)


let spec_to_acsl (s : spec) : string =
  let b = get_behaviors s in
  let req  = requires_clause b in
  let asgn = assigns_clause  b in
  match ensures_clause b with
  | None -> Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
*/"
        req asgn
  | Some ens -> Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
  ensures  %s;
*/"
        req asgn ens
