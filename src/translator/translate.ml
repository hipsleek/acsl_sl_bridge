let sl_to_acsl (sl_spec : Sl_ast.spec) : string =
  let desugar_spec = Sl_desugar.Prime_to_old.desugar_spec sl_spec in
  let core_spec = Sl_to_core.sl_to_core desugar_spec in
  Core_to_acsl.spec_to_acsl core_spec

let acsl_to_sl (acsl_spec : Acsl_ast.spec) : string =
  let core_spec = Acsl_to_core.acsl_to_core acsl_spec in
  Core_to_sl.core_to_sl core_spec
