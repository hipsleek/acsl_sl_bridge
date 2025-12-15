open Make_contract_of_spec
open Make_loop_contract
module AP = Acsl_ast_printer

let spec_to_acsl (s : Core.spec) : string =
  match loop_contract_of_spec s with
  | Some lc -> AP.acsl_loop_contract lc
  | None -> s |> contract_of_spec |> AP.acsl_contract