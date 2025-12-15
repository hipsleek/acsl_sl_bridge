open Helper
open Make_simple_core
open Make_case_core
open Make_sugar_core
open Make_loop_core

let spec_to_core (s : Sl_ast.spec) : Core.spec =
  match s with
  | Simple { pre; post } ->
      let pre_atoms  = atoms_of_heap pre in
      let post_atoms = atoms_of_heap post in
      make_simple_core pre_atoms post_atoms

  | Case sl_cases ->
      make_case_core sl_cases
  | Loop loop_spec ->
      make_loop_core loop_spec
  | Sugar_prime pairs
  | Sugar_old pairs ->
      make_sugar_core pairs
