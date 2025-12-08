(* the idea of this interface is generalise and distill the key information.
so, it writes about the io variables, memory loc to be chanhged, the pre-state, the relation bw
pre state and post state*)

type ptr = string
type ty = string
type var = string

type mode = 
  | In
  | Out
  | InOut

type heap =
  | Pre
  | Post

type term =
  | T_var of var
  | T_int of int
  | T_heap of heap * ptr

type predicate =
  | P_eq of term * term
  | P_valid of ptr

type param = {
  name : var;
  (* ty : ty; *)
  mode : mode;
}

type spec = {
  params : param list;
  frame : ptr list;
  requires : predicate list;
  ensures : predicate list;
}


(* operator helpers*)
let mk_param mode name : param = { name; mode; }

let heap_pre (p : ptr) : term = T_heap (Pre, p)

let heap_post (p : ptr) : term = T_heap (Post, p)

let eq (t1 : term) (t2 : term) : predicate = P_eq (t1, t2)

let valid (p : ptr) : predicate = P_valid p


(* Preety prints*)

let string_of_heap_phase = function
  | Pre  -> "H"
  | Post -> "H'"

let string_of_term = function
  | T_var x -> x
  | T_int n -> string_of_int n
  | T_heap (ph, p) -> Printf.sprintf "%s(%s)" (string_of_heap_phase ph) p

let string_of_predicate = function
  | P_eq (t1, t2) -> Printf.sprintf "%s == %s" (string_of_term t1) (string_of_term t2)
  | P_valid p -> Printf.sprintf "valid(%s)" p

let string_of_spec (s : spec) : string =
  let params_str =
    s.params
    |> List.map (fun p ->
           let mode_str =
             match p.mode with
             | In -> "in"
             | Out -> "out"
             | InOut -> "inout"
           in
           Printf.sprintf "%s:%s" p.name mode_str)
    |> String.concat ", "
  in
  let frame_str =
    s.frame |> String.concat ", "
  in
  let preds_to_str ps =
    match ps with
    | [] -> "true"
    | _  ->
        ps
        |> List.map string_of_predicate
        |> String.concat " && "
  in
  Printf.sprintf
    "params (%s)\nframe {%s}\nrequires %s\nensures %s"
    params_str frame_str
    (preds_to_str s.requires)
    (preds_to_str s.ensures)