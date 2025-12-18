open Make_simple_core
open Make_case_core
open Make_sugar_core
open Make_result_core
open Sl_ast
open Helper

let spec_to_core (s : Sl_ast.spec) : Core.spec =
  match s with
  | Simple { pre; post } ->
      make_simple_core pre post

  | Case sl_cases ->
      make_case_core sl_cases

  | Ens e ->
      let post =
        match e.ret with
        | None -> e.post
        | Some r -> subst_result_assertion r e.post
      in
      begin match post with
      | A_sugar_prime pairs -> make_sugar_core pairs
      | A_sugar_old pairs -> make_sugar_core pairs
      | _ -> make_result_core post
      end
