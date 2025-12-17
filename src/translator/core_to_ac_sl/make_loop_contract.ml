open Helper_core_to_acsl

module C = Core
module A = Acsl_ast

let upper_bound_of_pred (p : C.predicate) : (string * [ `Lt | `Lte ] * int) option =
  match p with
  | C.P_lt  (C.T_var (C.Post, x), C.T_int k) -> Some (x, `Lt,  k)
  | C.P_lte (C.T_var (C.Post, x), C.T_int k) -> Some (x, `Lte, k)
  | _ -> None

let choose_best_upper_bound
    (cands : (string * [ `Lt | `Lte ] * int) list)
  : (string * [ `Lt | `Lte ] * int) option =
  let better (_x1, op1, k1) (_x2, op2, k2) =
    if k1 <> k2 then k1 > k2
    else
      match (op1, op2) with
      | (`Lte, `Lt) -> true
      | (`Lt, `Lte) -> false
      | _ -> false
  in
  match cands with
  | [] -> None
  | c0 :: cs ->
      Some (List.fold_left (fun best c -> if better c best then c else best) c0 cs)

let core_pred_of_upper_bound (x : string) (op : [ `Lt | `Lte ]) (k : int) : C.predicate =
  match op with
  | `Lt  -> C.P_lt  (C.T_var (C.Post, x), C.T_int k)
  | `Lte -> C.P_lte (C.T_var (C.Post, x), C.T_int k)

let loop_contract_of_spec (s : C.spec) : A.loop_contract option =
  match s.behaviors with
  | [] -> None
  | bs ->
      let looping =
        bs
        |> List.filter (fun (b : C.behavior) -> b.variant <> None)
      in
      match looping with
      | [] -> None

      | [b] ->
          let invariants = acsl_preds_of_core b.assumes in
          let ensures    = acsl_preds_of_core b.ensures in
          let vars       = vars_of_preds (invariants @ ensures) in
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
          Some { A.l_invariants = invariants; A.l_assigns = assigns; A.l_variant = variant }

      | looping_bs ->
          let upper_bounds =
            looping_bs
            |> List.concat_map (fun (b : C.behavior) ->
                   b.assumes |> List.filter_map upper_bound_of_pred)
          in

          let inv_core_preds =
            match choose_best_upper_bound upper_bounds with
            | Some (x, op, k) -> [ core_pred_of_upper_bound x op k ]
            | None ->
                (List.hd looping_bs).assumes
          in

          let b0 = List.hd looping_bs in
          let invariants = acsl_preds_of_core inv_core_preds in
          let ensures    = acsl_preds_of_core b0.ensures in
          let vars       = vars_of_preds (invariants @ ensures) in
          let vars =
            match b0.variant with
            | None -> vars
            | Some t_c -> vars_of_term vars (acsl_term_of_core t_c)
          in
          let assigns = vars |> StringSet.elements |> List.map (fun x -> A.TVar x) in
          let variant =
            match b0.variant with
            | None     -> None
            | Some t_c -> Some (acsl_term_of_core t_c)
          in
          Some { A.l_invariants = invariants; A.l_assigns = assigns; A.l_variant = variant }
