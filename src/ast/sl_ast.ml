type ptr = string
type car_type = string
type car = string

type heap_atom = 
  | PointTo of ptr * car_type * car 

type heap = 
  | Atom of heap_atom
  | Sep of heap * heap

type arith_expr =
  | A_var of string
  | A_int of int
  | A_add of arith_expr * arith_expr
  | A_sub of arith_expr * arith_expr
  | A_mul of arith_expr * arith_expr
  | A_div of arith_expr * arith_expr

type conditional_expr =
  | E_eq of arith_expr * arith_expr
  | E_neq of arith_expr * arith_expr
  | E_lte of arith_expr * arith_expr
  | E_lt of arith_expr * arith_expr
  | E_gte of arith_expr * arith_expr
  | E_gt of arith_expr * arith_expr

type terminate_expr =
  | Term_none
  | Term of arith_expr

type base_spec = {
  pre : heap;
  post : heap;
}

type case_spec = {
  test : conditional_expr;
  term : terminate_expr option;
  pre : heap;
  post : heap;
}

type spec =
  | Simple of base_spec
  | Case of case_spec list


(*Prints*)
let rec string_of_heap = function
  | Atom (PointTo (p, t, v)) ->
      Printf.sprintf "%s->%s*(%s)" p t v
  | Sep (h1, h2) ->
      Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)    

let rec string_of_arith = function
  | A_var x -> x
  | A_int n -> string_of_int n
  | A_add (e1, e2) -> Printf.sprintf "%s+%s" (string_of_arith e1) (string_of_arith e2)
  | A_sub (e1, e2) -> Printf.sprintf "%s-%s" (string_of_arith e1) (string_of_arith e2)
  | A_mul (e1, e2) -> Printf.sprintf "%s*%s" (string_of_arith e1) (string_of_arith e2)
  | A_div (e1, e2) -> Printf.sprintf "%s/%s" (string_of_arith e1) (string_of_arith e2)

let string_of_expr = function
  | E_eq (e1, e2) -> Printf.sprintf "%s==%s" (string_of_arith e1) (string_of_arith e2)
  | E_neq (e1, e2) -> Printf.sprintf "%s!=%s" (string_of_arith e1) (string_of_arith e2)
  | E_lt (e1, e2) -> Printf.sprintf "%s<%s" (string_of_arith e1) (string_of_arith e2)
  | E_lte (e1, e2) -> Printf.sprintf "%s<=%s" (string_of_arith e1) (string_of_arith e2)
  | E_gt (e1, e2) -> Printf.sprintf "%s>%s" (string_of_arith e1) (string_of_arith e2)
  | E_gte (e1, e2) -> Printf.sprintf "%s>=%s" (string_of_arith e1) (string_of_arith e2)

let string_of_base_spec (s : base_spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)

let string_of_sl_case (c : case_spec) : string =
  let guard = string_of_expr c.test in
  match c.term with
  | None ->
      let bs = { pre = c.pre; post = c.post } in
      Printf.sprintf "%s => %s" guard (string_of_base_spec bs)
  | Some (Term e) ->
      Printf.sprintf "%s => req Term[%s]; ens %s;"
        guard
        (string_of_arith e)
        (string_of_heap c.post)
  | Some Term_none ->
      Printf.sprintf "%s => req Term[]; ens %s;"
        guard
        (string_of_heap c.post)

let string_of_spec = function
  | Simple bs -> string_of_base_spec bs
  | Case cases ->
      let body =
        cases
        |> List.map string_of_sl_case
        |> String.concat " "
      in
      Printf.sprintf "case {%s};" body


(* **** Desugar functions ***** *)
module StringSet = Set.Make (String)
module SMap = Map.Make(String)

(*Helper Functions*)
let heap_of_atoms atoms =
  match atoms with
  | [] -> failwith "heap_of_atoms: empty"
  | (p,t,v) :: rest ->
        List.fold_left
          (fun acc (p,t,v) -> Sep (acc, Atom (PointTo (p,t,v))))
          (Atom (PointTo (p,t,v)))
          rest

(*Eg: a -> int*(u)   =>   {"a"}*)
let ptrs_of_pairs pairs =
  List.fold_left
    (fun acc (_p, q) -> StringSet.add q acc)
    StringSet.empty pairs

(*Desugaring functions*)
let spec_of_pointer_pairs (pairs : (ptr * ptr) list) : spec =
  let srcs = ptrs_of_pairs pairs |> StringSet.elements in

  let var_map =
    List.mapi (fun i q -> (q, Printf.sprintf "v%d" i)) srcs
    |> List.fold_left (fun m (q,v) -> SMap.add q v m) SMap.empty
  in

  let dummy_type = "int" in

  let pre_atoms =
    List.map
      (fun q -> (q, dummy_type, SMap.find q var_map))
      srcs
  in

  let post_atoms =
    List.map
      (fun (p,q) -> (p, dummy_type, SMap.find q var_map))
      pairs
  in

  Simple {
    pre  = heap_of_atoms pre_atoms;
    post = heap_of_atoms post_atoms;
  }
