let sl_to_acsl (sl_spec : Sl_ast.spec) : string =
  let core_spec = Spec_to_core.sl_to_core sl_spec in
  Core_to_acsl.spec_to_acsl core_spec
