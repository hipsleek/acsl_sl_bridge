open Helper
module C = Core

let make_result_core (post : Sl_ast.assertion) : C.spec =
  let ensures = preds_of_assertion post in
  let behavior : C.behavior =
    { C.assumes = []; requires = []; ensures; frame = []; variant = None }
  in
  { C.params = []; behaviors = [ behavior ] }
