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

type phase =
  | Pre
  | Post

type term =
  | T_var of phase * var
  | T_int of int
  | T_heap of phase * ptr
  | T_ptr of ptr  

type predicate =
  | P_eq of term * term
  | P_neq of term * term
  | P_lte of term * term
  | P_lt of term * term
  | P_gte of term * term
  | P_gt of term * term
  | P_valid of ptr

type param = {
  name : var;
  (* ty : ty; *)
  mode : mode;
}

type behavior = {
  assumes : predicate list; 
  requires : predicate list;
  ensures : predicate list;
  frame : ptr list;
  variant : term option;
}

type spec = {
  params : param list;
  behaviors : behavior list;
}




(* Preety prints*)

let string_of_heap_phase = function
  | Pre -> "H"
  | Post -> "H'"

let string_of_term = function
  | T_var (_,x) -> x
  | T_int n -> string_of_int n
  | T_heap (ph, p) -> Printf.sprintf "%s(%s)" (string_of_heap_phase ph) p
  | T_ptr p -> p

let string_of_predicate = function
  | P_eq (t1, t2) -> Printf.sprintf "%s == %s" (string_of_term t1) (string_of_term t2)
  | P_neq (t1, t2) -> Printf.sprintf "%s != %s" (string_of_term t1) (string_of_term t2)
  | P_lte (t1, t2) -> Printf.sprintf "%s <= %s" (string_of_term t1) (string_of_term t2)
  | P_lt (t1, t2) -> Printf.sprintf "%s < %s" (string_of_term t1) (string_of_term t2)
  | P_gte (t1, t2) -> Printf.sprintf "%s >= %s" (string_of_term t1) (string_of_term t2)
  | P_gt (t1, t2) -> Printf.sprintf "%s > %s" (string_of_term t1) (string_of_term t2)
  | P_valid p -> Printf.sprintf "valid(%s)" p

let string_of_mode = function
  | In    -> "in"
  | Out   -> "out"
  | InOut -> "inout"

let string_of_param (p : param) : string =
  Printf.sprintf "%s:%s" p.name (string_of_mode p.mode)

let string_of_behavior (b : behavior) : string =
  let preds_to_str ps =
    match ps with
    | [] -> "true"
    | _ ->
        ps
        |> List.map string_of_predicate
        |> String.concat " && "
  in
  let frame_str = String.concat ", " b.frame in
  Printf.sprintf
    "assumes %s\nrequires %s\nensures %s\nframe {%s}"
    (preds_to_str b.assumes)
    (preds_to_str b.requires)
    (preds_to_str b.ensures)
    frame_str

let string_of_spec (s : spec) : string =
  let params_str = s.params |> List.map string_of_param |> String.concat ", " in
  let behaviors_str = s.behaviors |> List.map string_of_behavior |> String.concat "\n" in
  Printf.sprintf "params (%s)\n%s" params_str behaviors_str