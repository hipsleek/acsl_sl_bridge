open Helper_core_to_acsl

let contract_of_spec (s : Core.spec) : A.contract =
  match s.behaviors with
  | [] -> { A.assigns = []; behaviors = [] } (*empty list*)
  | [b] when b.assumes = [] -> (*single behaviour*)
      let assigns = acsl_assigns_of_frame b.frame in
      let requires = acsl_preds_of_core b.requires in
      let ensures = acsl_preds_of_core b.ensures in
      let behavior : A.behavior =
        {
          A.b_name = None;
          A.b_assumes = [];
          A.b_requires = requires;
          A.b_ensures = ensures;
        }
      in
      {
        A.assigns;
        behaviors = [ behavior ];
      }

  | bs ->
      let global_frame = global_frame_of_behaviors bs in
      let assigns = acsl_assigns_of_frame global_frame in
      let behaviors =
        bs
        |> List.mapi (fun i (b : Core.behavior)->
               let name =
                 Some (Printf.sprintf "case%d" (i + 1))
               in
               let assumes = acsl_preds_of_core b.assumes in
               let requires = acsl_preds_of_core b.requires in
               let ensures = acsl_preds_of_core b.ensures in
               {
                 A.b_name = name;
                 A.b_assumes = assumes;
                 A.b_requires = requires;
                 A.b_ensures = ensures;
               })
      in { A.assigns; behaviors; }