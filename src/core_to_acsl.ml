open Core

module A = Acsl_ast
module AP = Acsl_ast_printer
module StringSet = Set.Make (String)

let rec acsl_term_of_core (t : term) : A.term =
  match t with
  | T_var (Pre, x) -> A.TOld (A.TVar x)
  | T_var (Post, x) -> A.TVar x
  | T_heap (Pre, p)  -> A.TOld (A.TDeref (A.TVar p))
  | T_heap (Post, p) -> A.TDeref (A.TVar p)
  | T_int n -> A.TInt n
  | T_ptr p -> A.TVar p
  | T_arith (op, t1, t2) -> let op_prime =
        match op with
        | Add -> A.Add
        | Sub -> A.Sub
        | Mul -> A.Mul
        | Div -> A.Div
      in
      A.TBinOp (op_prime, acsl_term_of_core t1, acsl_term_of_core t2)

let acsl_pred_of_core (p : predicate) : A.predicate =
  match p with
  | P_valid q -> A.TApp ("\\valid", [ A.TVar q ])
  | P_eq (t1, t2) -> A.TBinOp (A.Eq, acsl_term_of_core t1, acsl_term_of_core t2)
  | P_neq (t1, t2) -> A.TBinOp (A.Neq,acsl_term_of_core t1, acsl_term_of_core t2)
  | P_lte (t1, t2) -> A.TBinOp (A.Lte, acsl_term_of_core t1, acsl_term_of_core t2)
  | P_lt  (t1, t2) -> A.TBinOp (A.Lt, acsl_term_of_core t1, acsl_term_of_core t2)
  | P_gte (t1, t2) -> A.TBinOp (A.Gte, acsl_term_of_core t1, acsl_term_of_core t2)
  | P_gt  (t1, t2) -> A.TBinOp (A.Gt, acsl_term_of_core t1, acsl_term_of_core t2)

let acsl_preds_of_core (ps : predicate list) : A.predicate list =
  List.map acsl_pred_of_core ps

let global_frame_of_behaviors (bs : behavior list) : ptr list =
  let set =
    List.fold_left
      (fun acc b ->
         List.fold_left
           (fun acc p -> StringSet.add p acc)
           acc b.frame)
      StringSet.empty
      bs
  in
  StringSet.elements set

let acsl_assigns_of_frame (ptrs : ptr list) : A.term list =
  List.map (fun p -> A.TDeref (A.TVar p)) ptrs



let contract_of_spec (s : spec) : A.contract =
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
        |> List.mapi (fun i b ->
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


let rec vars_of_term (acc : StringSet.t) (t : A.term) : StringSet.t =
  match t with
  | A.TVar x -> StringSet.add x acc
  | A.TInt _ -> acc
  | A.TDeref t'
  | A.TOld t' -> vars_of_term acc t'
  | A.TApp (_, args) ->
      List.fold_left vars_of_term acc args
  | A.TBinOp (_, t1, t2) ->
      let acc = vars_of_term acc t1 in
      vars_of_term acc t2

let vars_of_preds (ps : A.predicate list) : StringSet.t =
  List.fold_left vars_of_term StringSet.empty ps

(* if behavior has variant field, interpret as a loop contract *)
let loop_contract_of_spec (s : spec) : A.loop_contract option =
  match s.behaviors with
  | [] -> None
  | bs ->
      let with_variant = List.filter (fun b -> b.variant <> None) bs in
      match with_variant with
      | [] -> None
      | b :: _ ->
          let invariants = acsl_preds_of_core b.assumes in
          let vars       = vars_of_preds invariants in
          let assigns =
            vars
            |> StringSet.elements
            |> List.map (fun x -> A.TVar x)
          in
          let variant =
            match b.variant with
            | None     -> None
            | Some t_c -> Some (acsl_term_of_core t_c)
          in
          Some {
            A.l_invariants = invariants;
            A.l_assigns    = assigns;
            A.l_variant    = variant;
          }

let spec_to_acsl (s : spec) : string =
  match loop_contract_of_spec s with
  | Some lc -> AP.acsl_loop_contract lc
  | None -> s |> contract_of_spec |> AP.acsl_contract
