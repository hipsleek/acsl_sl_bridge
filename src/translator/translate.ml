let sl_to_acsl (s : Sl_ast.spec) : string =
  let core_spec = Spec_to_core.spec_to_core s in
  Core_to_acsl.spec_to_acsl core_spec
