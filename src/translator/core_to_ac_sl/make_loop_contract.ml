open Helper_core_to_acsl

(* loop contract iff at least one behavior has a variant. *)
let loop_contract_of_spec (s : Core.spec) : A.loop_contract option =
  match s.behaviors with
  | [] -> None
  | bs ->
      (* Search for variant keyword *)
      let with_variant = List.filter (fun (b : Core.behavior) -> b.variant <> None) bs in
      match with_variant with
      | [] -> None
      | b :: _ ->
          let invariants = acsl_preds_of_core b.assumes in
          let ensures = acsl_preds_of_core b.ensures in
          let vars = vars_of_preds (invariants @ ensures) in
          let vars =
            match b.variant with
            | None -> vars
            | Some t_c -> vars_of_term vars (acsl_term_of_core t_c)
          in
          let assigns = vars |> StringSet.elements |> List.map (fun x -> A.TVar x) in
          let variant =
            match b.variant with
            | None     -> None
            | Some t_c -> Some (acsl_term_of_core t_c)
          in
          Some {
            A.l_invariants = invariants;
            A.l_assigns    = assigns;
            A.l_variant    = variant;
          }
