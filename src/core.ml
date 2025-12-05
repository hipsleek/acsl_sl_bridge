type ptr = string
type ty = string
type lvar = string

type heap_atom = {
  loc : ptr;
  ty  : ty;
  value : lvar;
}

type heap = heap_atom list

type spec = {
  pre  : heap;
  post : heap;
}

(*Prints*)
let string_of_heap_atom (a : heap_atom) : string =
  Printf.sprintf "%s->%s*(%s)" a.loc a.ty a.value

let string_of_heap (h : heap) : string =
  match h with
  | [] -> ""
  | _ ->
      h
      |> List.map string_of_heap_atom
      |> String.concat " && "

let string_of_spec (s : spec) : string =
  Printf.sprintf "req %s; ens %s;"
    (string_of_heap s.pre)
    (string_of_heap s.post)