open Acsl_ast

let string_of_binop = function
  | Eq  -> "=="
  | Neq -> "!="
  | Lt  -> "<"
  | Lte -> "<="
  | Gt  -> ">"
  | Gte -> ">="

let rec acsl_term = function
  | TVar x ->
      x
  | TInt n ->
      string_of_int n
  | TDeref t ->
      Printf.sprintf "*%s" (acsl_term t)
  | TOld t ->
      Printf.sprintf "\\old(%s)" (acsl_term t)
  | TApp ("\\valid", [arg]) ->
      Printf.sprintf "\\valid(%s)" (acsl_term arg)
  | TApp (f, args) ->
      let args_str =
        args
        |> List.map acsl_term
        |> String.concat ", "
      in
      Printf.sprintf "%s(%s)" f args_str
  | TBinOp (op, t1, t2) ->
      Printf.sprintf "%s %s %s"
        (acsl_term t1)
        (string_of_binop op)
        (acsl_term t2)

let acsl_pred (p : predicate) : string =
  acsl_term p

let acsl_pred_list (ps : predicate list) : string option =
  match ps with
  | [] -> None
  | _  ->
      Some
        (ps
         |> List.map acsl_pred
         |> String.concat " && ")

let acsl_assigns (ts : term list) : string =
  match ts with
  | [] -> "\\nothing"
  | _  ->
      ts
      |> List.map acsl_term
      |> String.concat ", "

let acsl_behavior_name (i : int) (b : behavior) : string =
  match b.b_name with
  | Some name -> name
  | None      -> Printf.sprintf "case%d" (i + 1)

let acsl_behavior_block (i : int) (b : behavior) : string =
  let buf = Buffer.create 128 in
  let name = acsl_behavior_name i b in
  Buffer.add_string buf (Printf.sprintf "  behavior %s:\r\n" name);

  (*assumes*)
  (match acsl_pred_list b.b_assumes with
   | None -> ()
   | Some s ->
       Buffer.add_string buf (Printf.sprintf "    assumes %s;\r\n" s));

  (*requires*)
  (match acsl_pred_list b.b_requires with
   | None -> ()
   | Some s ->
       Buffer.add_string buf (Printf.sprintf "    requires %s;\r\n" s));

  (*ensures*)
  (match acsl_pred_list b.b_ensures with
   | None -> ()
   | Some s ->
       Buffer.add_string buf (Printf.sprintf "    ensures  %s;\r\n" s));

  Buffer.contents buf

let acsl_contract (c : contract) : string =
  match c.behaviors with
  | [] ->
      "/*@\r\n*/"

  | [b] when b.b_assumes = [] ->
      let req =
        match acsl_pred_list b.b_requires with
        | None   -> "\\true"
        | Some s -> s
      in
      let asgn = acsl_assigns c.assigns in
      (match acsl_pred_list b.b_ensures with
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
      let assigns_str = acsl_assigns c.assigns in
      Buffer.add_string buf "/*@\r\n";
      Buffer.add_string buf (Printf.sprintf "  assigns  %s;\r\n" assigns_str);
      List.iteri
        (fun i b ->
           Buffer.add_string buf (acsl_behavior_block i b))
        behaviors;
      Buffer.add_string buf "*/";
      Buffer.contents buf

let acsl_loop_contract (lc : loop_contract) : string =
  let buf = Buffer.create 128 in
  Buffer.add_string buf "/*@\r\n";

  (match acsl_pred_list lc.l_invariants with
   | None -> ()
   | Some s ->
       Buffer.add_string buf
         (Printf.sprintf "  loop invariant %s;\r\n" s));

  let assigns_str = acsl_assigns lc.l_assigns in
  Buffer.add_string buf
    (Printf.sprintf "  loop assigns %s;\r\n" assigns_str);

  (match lc.l_variant with
   | None -> ()
   | Some v ->
       Buffer.add_string buf
         (Printf.sprintf "  loop variant %s;\r\n" (acsl_term v)));

  Buffer.add_string buf "*/";
  Buffer.contents buf