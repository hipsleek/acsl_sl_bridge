(* core_to_sl.ml *)

open Core
module S = Sl_ast

let extract_core_ensures (b : Core.behavior) : Core.predicate =
  let rec go = function
    | [] -> Core.PTrue
    | Ensures p :: _ -> p
    | _ :: tl -> go tl
  in
  go b.clauses

let extract_swap_eqs (p : Core.predicate) : (string * string) list =
  let rec atoms acc = function
    | Core.PAnd ps -> List.fold_left atoms acc ps
    | Core.PAtom (Core.ARel (Core.Eq, Core.THeap (Core.Post, a), Core.THeap (Core.Pre, b))) ->
        (a, b) :: acc
    | Core.PAtom (Core.ARel (Core.Eq, Core.THeap (Core.Pre, b), Core.THeap (Core.Post, a))) ->
        (a, b) :: acc
    | _ -> acc
  in
  atoms [] p |> List.rev

let core_to_sl (core_spec : Core.spec) : string =
  match core_spec.kind with
  | Core.LoopContract ->
      failwith "Not implemented yet: Core_to_sl.core_to_sl (LoopContract)"

  | Core.FunctionContract -> (
      match core_spec.behaviors with
      | [] -> failwith "Core_to_sl.core_to_sl: empty behaviors"
      | b0 :: _ ->
          let ensures_p = extract_core_ensures b0 in
          let swap_pairs = extract_swap_eqs ensures_p in

          (* Prefer \\old sugar, do not try to infer heaplet types / pre-heap variables. *)
          let eqs =
            swap_pairs
            |> List.map (fun (a, b) -> "(*" ^ a ^ ")==\\old(*" ^ b ^ ")")
            |> String.concat " && "
          in

          "ens " ^ eqs ^ ";" )
