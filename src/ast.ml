type ptr = string
type car_type = string
type car = string

type heap_atom = 
  | PointTo of ptr * car_type * car 

type heap = 
  | Atom of heap_atom
  | Sep of heap * heap


type spec = {
  pre : heap;
  post : heap;
}


(*Prints*)
let rec string_of_heap = function
  | Atom (PointTo (p, t, v)) ->
      Printf.sprintf "%s->%s*(%s)" p t v
  | Sep (h1, h2) ->
      Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)

let string_of_spec s =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)


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

  {
    pre  = heap_of_atoms pre_atoms;
    post = heap_of_atoms post_atoms;
  }
