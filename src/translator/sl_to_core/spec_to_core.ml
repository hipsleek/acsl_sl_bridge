open Make_simple_core
open Make_case_core
open Make_sugar_core
open Sl_ast

let spec_to_core (s : Sl_ast.spec) : Core.spec =
  match s with
  | Simple { pre; post } ->
      make_simple_core pre post

  | Case sl_cases ->
      make_case_core sl_cases

  | Ens a ->
      begin match a with
      | A_sugar_prime pairs -> make_sugar_core pairs
      | A_sugar_old pairs   -> make_sugar_core pairs
      | _ -> failwith "Ens: only sugar_prime/sugar_old assertions are supported in SL→Core right now" end
