(* Entry point: attach the SL-derived contracts right after the AST is built,
   so they are in place before any analysis (e.g. WP) consumes them. *)

let () =
  Ast.apply_after_computed (fun _file ->
      if Sl_options.Enabled.get () then Sl_attach.process ())
