open Core

module StringSet = Set.Make (String)

type term_style =
  | Plain
  | Heap   

let acsl_of_term (style : term_style) (t : term) : string =
  match style, t with
  | Plain, T_ptr p -> p
  | Plain, T_var x -> x
  | Plain, T_int n -> string_of_int n
  | Plain, T_heap _ -> failwith "acsl_of_term: unexpected heap term in Plain style"

  | Heap, T_heap (Pre, p) -> Printf.sprintf "\\old(*%s)" p
  | Heap, T_heap (Post, p) -> Printf.sprintf "*%s" p
  | Heap, T_var x -> x
  | Heap, T_int n -> string_of_int n
  | Heap, T_ptr p -> p

let op_string_of_pred (p : predicate) : string =
  match p with
  | P_eq  _ -> "=="
  | P_neq _ -> "!="
  | P_lte _ -> "<="
  | P_lt  _ -> "<"
  | P_gte _ -> ">="
  | P_gt  _ -> ">"
  | P_valid _ ->
      failwith "op_string_of_pred: P_valid has no binary operator"

let acsl_of_predicate (style : term_style) (p : predicate) : string =
  match p with
  | P_valid q -> Printf.sprintf "\\valid(%s)" q
  | P_eq (t1, t2)
  | P_neq (t1, t2)
  | P_lte (t1, t2)
  | P_lt  (t1, t2)
  | P_gte (t1, t2)
  | P_gt  (t1, t2) ->
      let op = op_string_of_pred p in
      Printf.sprintf "%s %s %s"
        (acsl_of_term style t1)
        op
        (acsl_of_term style t2)

let acsl_of_pred_list (style : term_style) (ps : predicate list)
  : string option =
  match ps with
  | [] -> None
  | _ ->
      Some
        (ps
         |> List.map (acsl_of_predicate style)
         |> String.concat " && ")

let requires_clause_flat (b : behavior) : string =
  match acsl_of_pred_list Plain b.requires with
  | None -> "\\true"
  | Some s -> s

let assigns_clause_of_frame (frame : ptr list) : string =
  match frame with
  | [] -> "\\nothing"
  | ptrs ->
      ptrs
      |> List.map (fun p -> Printf.sprintf "*%s" p)
      |> String.concat ", "

let ensures_clause_flat (b : behavior) : string option =
  acsl_of_pred_list Heap b.ensures

let global_frame_of_behaviors (bs : behavior list) : ptr list =
  let set =
    List.fold_left
      (fun acc b ->
         List.fold_left
           (fun acc p -> StringSet.add p acc)
           acc b.frame)
      StringSet.empty
      bs
  in
  StringSet.elements set

let behavior_name index : string =
  Printf.sprintf "case%d" (index + 1)


let spec_to_acsl (s : spec) : string =
  match s.behaviors with
  | [] -> "/*@\n*/"

  | [b] when b.assumes = [] ->
      let req  = requires_clause_flat b in
      let asgn = assigns_clause_of_frame b.frame in
      (match ensures_clause_flat b with
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
             req asgn ens)

  | behaviors ->
      let buf = Buffer.create 256 in
      Buffer.add_string buf "/*@\r\n";

      let global_frame = global_frame_of_behaviors behaviors in
      let assigns_str  = assigns_clause_of_frame global_frame in
      Buffer.add_string buf
        (Printf.sprintf "  assigns  %s;\r\n" assigns_str);

      List.iteri
        (fun i b ->
           let name = behavior_name i in
           Buffer.add_string buf
             (Printf.sprintf "  behavior %s:\r\n" name);

           (match acsl_of_pred_list Plain b.assumes with
            | None -> ()
            | Some s ->
                Buffer.add_string buf
                  (Printf.sprintf "    assumes %s;\r\n" s));

           (match acsl_of_pred_list Plain b.requires with
            | None -> ()
            | Some s ->
                Buffer.add_string buf
                  (Printf.sprintf "    requires %s;\r\n" s));

           (match ensures_clause_flat b with
            | None -> ()
            | Some s ->
                Buffer.add_string buf
                  (Printf.sprintf "    ensures  %s;\r\n" s));
        )
        behaviors;

      Buffer.add_string buf "*/";
      Buffer.contents buf
