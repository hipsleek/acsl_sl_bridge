open Helper_core_to_acsl
open Core

let contract_of_spec (s : Core.spec) : A.contract =
  match s.behaviors with
  | [] -> { A.requires = []; A.assigns = []; behaviors = [] }
  | [b] ->
      let assigns  = acsl_assigns_of_frame b.frame in
      let requires = acsl_preds_of_core b.requires in
      let assumes  = acsl_preds_of_core b.assumes in
      let ensures  = acsl_preds_of_core b.ensures in
      let behavior : A.behavior =
        {
          A.b_name    = None;
          A.b_assumes = assumes;
          A.b_ensures = ensures;
        }
      in
      {
        A.requires;
        A.assigns;
        behaviors = [ behavior ];
      }

  | b0 :: bs -> (*find multi-level case statements*)
      let all = b0 :: bs in

      let common_requires = (*check for the same requires clause*)
        if List.for_all (fun b -> b.requires = b0.requires) all
        then acsl_preds_of_core b0.requires
        else failwith "make_contract_of_spec: inconsistent requires across behaviors"
      in

      let global_frame = global_frame_of_behaviors all in
      let assigns = acsl_assigns_of_frame global_frame in

      let behaviors = all |> List.mapi (fun i (b : Core.behavior) ->
               let name = Some (Printf.sprintf "case%d" (i + 1)) in
               let assumes = acsl_preds_of_core b.assumes in
               let ensures = acsl_preds_of_core b.ensures in
               {
                 A.b_name = name;
                 A.b_assumes = assumes;
                 A.b_ensures = ensures;
               })
      in
      {
        A.requires = common_requires;
        A.assigns;
        behaviors;
      }
