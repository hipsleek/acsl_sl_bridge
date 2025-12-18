open Core

let string_of_heap_phase = function
  | Pre -> "H"
  | Post -> "H'"

let string_of_arith_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

let rec string_of_term = function
  | T_var (_,x) -> x
  | T_int n -> string_of_int n
  | T_heap (ph, p) -> Printf.sprintf "%s(%s)" (string_of_heap_phase ph) p
  | T_ptr p -> p
  | T_arith (op, t1, t2) -> Printf.sprintf "%s%s%s" (string_of_term t1) (string_of_arith_op op) (string_of_term t2)
  | T_result -> Printf.sprintf "\\result"

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

let string_of_param (p : param) : string = Printf.sprintf "%s:%s" p.name (string_of_mode p.mode)

let string_of_behavior (b : behavior) : string =
  let preds_to_str ps =
    match ps with
    | [] -> "true"
    | _ -> ps |> List.map string_of_predicate |> String.concat " && "
  in
  let frame_str = String.concat ", " b.frame in
  let base = Printf.sprintf
    "assumes %s\nrequires %s\nensures %s\nframe {%s}"
    (preds_to_str b.assumes)
    (preds_to_str b.requires)
    (preds_to_str b.ensures)
    frame_str
  in
  match b.variant with
  | None -> base
  | Some t ->
      let variant_str = string_of_term t in
      base ^ Printf.sprintf "\nvariant %s" variant_str

let string_of_spec (s : spec) : string =
  let params_str = s.params |> List.map string_of_param |> String.concat ", " in
  let behaviors_str = s.behaviors |> List.map string_of_behavior |> String.concat "\n" in
  Printf.sprintf "params (%s)\n%s" params_str behaviors_str