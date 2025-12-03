type ptr = string
type car = string

type heap_atom = 
  | PointTo of ptr * car 

type heap = 
  | Emp
  | Atom of heap_atom
  | Sep of heap * heap

type formula = 
  | HeapOnly of heap
  | And of formula * formula

type spec = {
  pre : formula;
  post : formula;
}


(*Prints*)
let rec string_of_heap = function
  | Emp ->
      "emp"
  | Atom (PointTo (p, v)) ->
      Printf.sprintf "%s->int*(%s)" p v
  | Sep (h1, h2) ->
      Printf.sprintf "(%s * %s)" (string_of_heap h1) (string_of_heap h2)

let rec string_of_formula = function
  | HeapOnly h ->
      string_of_heap h
  | And (f1, f2) ->
      Printf.sprintf "(%s && %s)" (string_of_formula f1) (string_of_formula f2)

let string_of_spec s =
  Printf.sprintf "req %s; ens %s;"
    (string_of_formula s.pre)
    (string_of_formula s.post)