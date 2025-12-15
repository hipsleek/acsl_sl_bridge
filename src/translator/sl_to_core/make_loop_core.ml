open Helper
open Make_case_core

module C = Core

let make_loop_simple_core (ls : Sl_ast.loop_simple) : C.spec =
  let assumes = preds_of_pred ls.req in

  let variant =
    match ls.term with
    | None
    | Some Term_none -> None
    | Some (Term e)  -> Some (term_of_arith e)
  in

  let frame = frame_of_pred ls.ens in

  {
    C.params = [];
    C.behaviors =
      [
        {
          C.assumes;
          C.requires = [];
          C.ensures  = [];
          C.frame    = frame;
          C.variant  = variant;
        }
      ];
  }

let make_loop_core (loop_spec : Sl_ast.loop_spec) : C.spec =
  match loop_spec with
  | Loop_case cases ->
      make_case_core cases

  | Loop_simple ls ->
      make_loop_simple_core ls
