open Core

let string_of_term_in_ensures (t : term) : string =
  match t with
  | T_heap (Pre, p) -> Printf.sprintf "\\old(*%s)" p
  | T_heap (Post, p) -> Printf.sprintf "*%s" p
  | T_var x -> x
  | T_int n -> string_of_int n



let requires_clause (s : spec) : string =
  match s.requires with
  (* | [] -> "\\true" *)
  | preds ->
      preds
      |> List.map (function
             | P_valid p -> Printf.sprintf "\\valid(%s)" p
             | P_eq _ -> failwith "Unexpected equality in requires_clause")
      |> String.concat " && "

let assigns_clause (s : spec) : string =
  match s.frame with
  (* | [] -> "\\nothing" *)
  | ptrs ->
      ptrs
      |> List.map (fun p -> Printf.sprintf "*%s" p)
      |> String.concat ", "

let ensures_clause (s : spec) : string option =
  match s.ensures with
  (* | [] -> None *)
  | preds ->
      let parts =
        preds
        |> List.map (function
               | P_eq (t1, t2) ->
                   Printf.sprintf "%s == %s"
                     (string_of_term_in_ensures t1)
                     (string_of_term_in_ensures t2)
               | P_valid _ ->
                   failwith "Unexpected validity in ensures_clause")
      in
      Some (String.concat " && " parts)



let spec_to_acsl (s : spec) : string =
  let req  = requires_clause s in
  let asgn = assigns_clause s in
  match ensures_clause s with
  | None ->
      Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
*/"
        req asgn
  | Some ens ->
      Printf.sprintf
"/*@
  requires %s;
  assigns  %s;
  ensures  %s;
*/"
        req asgn ens
