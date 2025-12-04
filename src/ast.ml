type ptr = string
type car = string

type heap_atom = 
  | PointTo of ptr * car 

type heap = 
  | Emp
  | Atom of heap_atom
  | Sep of heap * heap


type spec = {
  pre : heap;
  post : heap;
}


(*Prints*)
let rec string_of_heap = function
  | Emp ->
      ""
  | Atom (PointTo (p, v)) ->
      Printf.sprintf "%s->int*(%s)" p v
  | Sep (h1, h2) ->
      Printf.sprintf "%s && %s" (string_of_heap h1) (string_of_heap h2)

let string_of_spec s =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)