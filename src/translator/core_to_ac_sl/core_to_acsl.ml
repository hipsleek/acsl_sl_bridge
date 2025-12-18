(* core_to_acsl.ml *)
module C = Core
module A = Acsl_ast

(* ---------- helpers ---------- *)

let binop_of_arith_op (op : C.arith_op) : A.binop =
  match op with
  | C.Add -> A.Add
  | C.Sub -> A.Sub
  | C.Mul -> A.Mul
  | C.Div -> A.Div

let rel_of_core_rel (r : C.rel) : A.rel =
  match r with
  | C.Eq  -> A.Eq
  | C.Neq -> A.Neq
  | C.Lt  -> A.Lt
  | C.Lte -> A.Lte
  | C.Gt  -> A.Gt
  | C.Gte -> A.Gte

let rec find_first (f : 'a -> 'b option) (xs : 'a list) : 'b option =
  match xs with
  | [] -> None
  | x :: tl ->
      match f x with
      | Some y -> Some y
      | None -> find_first f tl

let collect (f : 'a -> 'b option) (xs : 'a list) : 'b list =
  List.filter_map f xs

(* string-based dedup is simplest + robust for your use case *)
let dedup_by (to_key : 'a -> string) (xs : 'a list) : 'a list =
  let module S = Set.Make (String) in
  let rec go seen acc = function
    | [] -> List.rev acc
    | x :: tl ->
        let k = to_key x in
        if S.mem k seen then go seen acc tl
        else go (S.add k seen) (x :: acc) tl
  in
  go S.empty [] xs

let list_hd_opt = function
  | [] -> None
  | x :: _ -> Some x

  
(* ---------- term lowering (Core -> ACSL) ---------- *)

let rec term (t : C.term) : A.term =
  match t with
  | C.TInt n -> A.TInt n
  | C.TResult -> A.TResult

  | C.TVar (C.Post, x) -> A.TVar x
  | C.TVar (C.Pre,  x) -> A.TOld (A.TVar x)

  | C.THeap (C.Post, p) -> A.TDeref (A.TVar p)
  | C.THeap (C.Pre,  p) -> A.TOld (A.TDeref (A.TVar p))

  | C.TPtr p -> A.TVar p

  | C.TArith (op, t1, t2) ->
      A.TBinOp (binop_of_arith_op op, term t1, term t2)

  | C.TApp (f, args) ->
      A.TApp (f, List.map term args)

(* ---------- predicate lowering ---------- *)

let rec predicate (p : C.predicate) : A.predicate =
  match p with
  | C.PTrue  -> A.PTrue
  | C.PFalse -> A.PFalse

  | C.PAtom a ->
      atom a

  | C.PNot p1 ->
      A.PNot (predicate p1)

  | C.PAnd ps ->
      A.PAnd (List.map predicate ps)

  | C.POr ps ->
      A.POr (List.map predicate ps)

  | C.PImplies (p1, p2) ->
      A.PImplies (predicate p1, predicate p2)

  | C.PForall (bs, body) ->
      let bs' = List.map (fun (b : C.binder) -> (b.b_name, b.b_ty)) bs in
      A.PForall (bs', predicate body)

  | C.PExists (bs, body) ->
      let bs' = List.map (fun (b : C.binder) -> (b.b_name, b.b_ty)) bs in
      A.PExists (bs', predicate body)

and atom (a : C.atom) : A.predicate =
  match a with
  | C.ARel (r, t1, t2) ->
      A.PRel (rel_of_core_rel r, term t1, term t2)

  | C.APred (name, args) ->
      (* normalize "valid" to ACSL builtin "\valid" *)
      if name = "valid" || name = "\\valid" then
        A.PApp ("\\valid", List.map term args)
      else
        A.PApp (name, List.map term args)

(* ---------- assigns lowering ---------- *)

let assigns (xs : C.assignable list) : A.assigns =
  match xs with
  | [] -> A.ANothing
  | _  ->
      let to_term = function
        | C.AsVar v  -> A.TVar v
        | C.AsHeap p -> A.TDeref (A.TVar p)
        | C.AsRange (p, lo, hi) ->
            A.TApp ("range", [ A.TVar p; term lo; term hi ])
        | C.AsTerm t -> term t
      in
      A.AList (List.map to_term xs)

(* ---------- behavior extraction ---------- *)

let lower_behavior
    (b : C.behavior)
  : A.behavior * A.predicate list * A.assigns option * A.term option
  =
  let assumes_ps =
    b.clauses |> collect (function C.Assumes p -> Some (predicate p) | _ -> None)
  in
  let requires_ps =
    b.clauses |> collect (function C.Requires p -> Some (predicate p) | _ -> None)
  in
  let ensures_ps =
    b.clauses |> collect (function C.Ensures p -> Some (predicate p) | _ -> None)
  in
  let assigns_opt =
    find_first (function C.Assigns xs -> Some (assigns xs) | _ -> None) b.clauses
  in
  let variant_opt =
    find_first (function C.Variant t -> Some (term t) | _ -> None) b.clauses
  in
  ({ A.b_name = b.b_name; b_assumes = assumes_ps; b_ensures = ensures_ps },
   requires_ps,
   assigns_opt,
   variant_opt)

(* ---------- Core spec -> ACSL AST ---------- *)

let spec_to_acsl_ast (s : C.spec) : [ `Contract of A.contract | `Loop of A.loop_contract ] =
  match s.kind with
  | C.FunctionContract ->
      let lowered =
        List.map lower_behavior s.behaviors
      in
      let behaviors = List.map (fun (b,_,_,_) -> b) lowered in

      let all_requires =
        lowered |> List.concat_map (fun (_, reqs, _, _) -> reqs)
      in
      let all_requires =
        (* dedup to avoid "\valid(a) && \valid(b) && \valid(a)..." *)
        dedup_by Acsl_ast_printer.acsl_pred all_requires
      in

      let assigns_choice =
        lowered
        |> List.filter_map (fun (_,_,asg_opt,_) -> asg_opt)
        |> list_hd_opt
      in
      let assigns_final = Option.value assigns_choice ~default:A.ANothing in

      `Contract { A.requires = all_requires; assigns = assigns_final; behaviors }

  | C.LoopContract ->
      (* translator style: a single behavior carries:
         - Assumes = invariant(s)
         - Assigns = loop assigns
         - Variant = loop variant
      *)
      let b0 =
        match s.behaviors with
        | [] -> { C.b_name = None; clauses = [] }
        | b :: _ -> b
      in
      let invariants =
        b0.clauses |> collect (function C.Assumes p -> Some (predicate p) | _ -> None)
      in
      let assigns_final =
        match find_first (function C.Assigns xs -> Some (assigns xs) | _ -> None) b0.clauses with
        | Some a -> a
        | None -> A.ANothing
      in
      let variant_final =
        find_first (function C.Variant t -> Some (term t) | _ -> None) b0.clauses
      in
      `Loop { A.l_invariants = invariants; l_assigns = assigns_final; l_variant = variant_final }

(* ---------- Core spec -> string (what your pipeline expects) ---------- *)

let spec_to_acsl (s : C.spec) : string =
  match spec_to_acsl_ast s with
  | `Contract c -> Acsl_ast_printer.acsl_contract c
  | `Loop lc    -> Acsl_ast_printer.acsl_loop_contract lc
