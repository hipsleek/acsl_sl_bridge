(* spec_to_core.ml
   SL AST -> Core IR translation.

   Additions for spatial notation (**):
   - Parse "**" as SSep.
   - Infer non-aliasing constraints from SSep heaplets:
       req (p->... ** q->...)  ==>  Requires includes (p != q).
   - Avoid duplicating disequalities if already present as pure constraints.
*)

open Sl_ast
module C = Core

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

module PairOrd = struct
  type t = string * string
  let compare (a1, b1) (a2, b2) =
    let c = String.compare a1 a2 in
    if c <> 0 then c else String.compare b1 b2
end

module PairSet = Set.Make (PairOrd)

(***)
(* Small utilities *)
(***) 

let ( let* ) x f = match x with None -> None | Some v -> f v

let list_filter_map f xs =
  let rec go acc = function
    | [] -> List.rev acc
    | x :: tl -> (
        match f x with
        | None -> go acc tl
        | Some y -> go (y :: acc) tl )
  in
  go [] xs

let p_atom (a : C.atom) : C.predicate = C.PAtom a

let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (r, t1, t2))

let rec flatten_and (ps : C.predicate list) : C.predicate list =
  match ps with
  | [] -> []
  | p :: tl -> (
      match p with
      | C.PTrue -> flatten_and tl
      | C.PAnd qs -> flatten_and (qs @ tl)
      | _ -> p :: flatten_and tl )

let rec flatten_or (ps : C.predicate list) : C.predicate list =
  match ps with
  | [] -> []
  | p :: tl -> (
      match p with
      | C.PFalse -> flatten_or tl
      | C.POr qs -> flatten_or (qs @ tl)
      | _ -> p :: flatten_or tl )

let p_and (ps : C.predicate list) : C.predicate =
  let ps = flatten_and ps in
  match ps with
  | [] -> C.PTrue
  | [ p ] -> p
  | _ -> C.PAnd ps

let p_or (ps : C.predicate list) : C.predicate =
  let ps = flatten_or ps in
  match ps with
  | [] -> C.PFalse
  | [ p ] -> p
  | _ -> C.POr ps

(***)
(* Sort / binder translation *)
(***) 

let core_ty_of_sort_opt (s : Sl_ast.sort option) : string option =
  match s with
  | None -> None
  | Some SInt -> Some "int"
  | Some SBool -> Some "bool"
  | Some SPtr -> None
  | Some (SUser s) -> Some s

let binders_of_sl (bs : (ident * sort option) list) : C.binder list =
  List.map
    (fun (nm, tyopt) -> { C.b_name = nm; b_ty = core_ty_of_sort_opt tyopt })
    bs

(***)
(* Operators *)
(***) 

let arith_of_binop = function
  | BAdd -> Some C.Add
  | BSub -> Some C.Sub
  | BMul -> Some C.Mul
  | BDiv -> Some C.Div
  | _ -> None

let rel_of_binop = function
  | BEq -> Some C.Eq
  | BNeq -> Some C.Neq
  | BLt -> Some C.Lt
  | BLe -> Some C.Lte
  | BGt -> Some C.Gt
  | BGe -> Some C.Gte
  | _ -> None

(***)
(* Abstract traversals *)
(***) 

let rec fold_expr ~(f : 'a -> Sl_ast.expr -> 'a) (acc : 'a) (e : Sl_ast.expr) : 'a =
  let acc = f acc e in
  match e with
  | EVar _ | EConstInt _ | EConstBool _ | EResult -> acc
  | EUnop (_, e1) -> fold_expr ~f acc e1
  | EBinop (_, a, b) -> fold_expr ~f (fold_expr ~f acc a) b
  | EApp (_, es) -> List.fold_left (fold_expr ~f) acc es
  | EDeref e1 -> fold_expr ~f acc e1
  | EOld e1 -> fold_expr ~f acc e1
  | EPost e1 -> fold_expr ~f acc e1

let rec fold_sl
    ~(f_sl : 'a -> Sl_ast.sl -> 'a)
    ~(f_expr : 'a -> Sl_ast.expr -> 'a)
    (acc : 'a)
    (s : Sl_ast.sl)
  : 'a
  =
  let acc = f_sl acc s in
  match s with
  | STrue | SFalse | SEmp -> acc
  | SHeap h -> (
      match h with
      | HPt { loc; value; _ } ->
          let acc = fold_expr ~f:f_expr acc loc in
          fold_expr ~f:f_expr acc value
      | HPred (_, args) -> List.fold_left (fold_expr ~f:f_expr) acc args
      | HRange { loc; lo; hi; _ } ->
          let acc = fold_expr ~f:f_expr acc loc in
          let acc = fold_expr ~f:f_expr acc lo in
          fold_expr ~f:f_expr acc hi )
  | SPure e -> fold_expr ~f:f_expr acc e
  | SSep xs | SAnd xs | SOr xs ->
      List.fold_left (fun a x -> fold_sl ~f_sl ~f_expr a x) acc xs
  | SNot x -> fold_sl ~f_sl ~f_expr acc x
  | SImplies (a, b) ->
      let acc = fold_sl ~f_sl ~f_expr acc a in
      fold_sl ~f_sl ~f_expr acc b
  | SExists (_, body) | SForall (_, body) ->
      fold_sl ~f_sl ~f_expr acc body

(***)
(* Expr -> Core.term *)
(***) 

let rec term_of_expr (default_phase : C.phase) (e : Sl_ast.expr) : C.term =
  match e with
  | EVar x -> C.TVar (default_phase, x)
  | EConstInt n -> C.TInt n
  | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
  | EResult -> C.TResult
  | EApp (f, args) -> C.TApp (f, List.map (term_of_expr default_phase) args)
  | EUnop (_op, e1) -> C.TApp ("unop", [ term_of_expr default_phase e1 ])
  | EDeref (EBinop (BAdd, base, idx)) ->
      C.TIndex (default_phase, term_of_expr default_phase base, term_of_expr default_phase idx)
  | EDeref e1 -> C.TLoad (default_phase, term_of_expr default_phase e1)
  | EOld e1 -> term_of_expr C.Pre e1
  | EPost e1 -> term_of_expr C.Post e1
  | EBinop (op, e1, e2) -> (
      match arith_of_binop op with
      | Some aop ->
          C.TArith (aop, term_of_expr default_phase e1, term_of_expr default_phase e2)
      | None ->
          C.TApp ("binop", [ term_of_expr default_phase e1; term_of_expr default_phase e2 ]) )

(***)
(* SL -> Core.predicate (heap ignored) *)
(***) 

let pred_of_cmp_expr (default_phase : C.phase) (e : Sl_ast.expr) : C.predicate =
  match e with
  | EBinop (op, e1, e2) -> (
      match rel_of_binop op with
      | Some r -> mk_rel r (term_of_expr default_phase e1) (term_of_expr default_phase e2)
      | None -> p_atom (C.APred ("bool", [ term_of_expr default_phase e ])) )
  | _ ->
      p_atom (C.APred ("bool", [ term_of_expr default_phase e ]))

let rec pred_of_sl (s : Sl_ast.sl) : C.predicate =
  match s with
  | STrue -> C.PTrue
  | SFalse -> C.PFalse
  | SEmp -> C.PTrue
  | SHeap _ -> C.PTrue
  | SPure e -> pred_of_cmp_expr C.Pre e
  | SSep xs | SAnd xs -> p_and (List.map pred_of_sl xs)
  | SOr xs -> p_or (List.map pred_of_sl xs)
  | SNot x -> C.PNot (pred_of_sl x)
  | SImplies (a, b) -> C.PImplies (pred_of_sl a, pred_of_sl b)
  | SForall (bs, body) -> C.PForall (binders_of_sl bs, pred_of_sl body)
  | SExists (bs, body) -> C.PExists (binders_of_sl bs, pred_of_sl body)

(***)
(* Clause extraction *)
(***) 

let extract_req_ens_var
    (body : Sl_ast.block)
  : Sl_ast.sl option * Sl_ast.sl option * Sl_ast.expr option
  =
  let req = ref None in
  let ens = ref None in
  let var = ref None in
  List.iter
    (function
      | CReq s -> req := Some s
      | CEns s -> ens := Some s
      | CVar v -> var := v)
    body;
  (!req, !ens, !var)

(***)
(* Result rewriting *)
(***) 

let rewrite_result (ret : string) (s : Sl_ast.sl) : Sl_ast.sl =
  let rec map_expr = function
    | EVar x when x = ret -> EResult
    | EUnop (op, e1) -> EUnop (op, map_expr e1)
    | EBinop (op, a, b) -> EBinop (op, map_expr a, map_expr b)
    | EApp (f, es) -> EApp (f, List.map map_expr es)
    | EDeref e1 -> EDeref (map_expr e1)
    | EOld e1 -> EOld (map_expr e1)
    | EPost e1 -> EPost (map_expr e1)
    | x -> x
  in
  let rec map_sl = function
    | (STrue | SFalse | SEmp) as x -> x
    | SHeap h -> SHeap h
    | SPure e -> SPure (map_expr e)
    | SSep xs -> SSep (List.map map_sl xs)
    | SAnd xs -> SAnd (List.map map_sl xs)
    | SOr xs -> SOr (List.map map_sl xs)
    | SNot x -> SNot (map_sl x)
    | SImplies (a, b) -> SImplies (map_sl a, map_sl b)
    | SExists (bs, body) -> SExists (bs, map_sl body)
    | SForall (bs, body) -> SForall (bs, map_sl body)
  in
  map_sl s

(***)
(* Heaplet / range queries *)
(***) 

type pt_atom = { loc : string; value : string }
type pt_atom_any = { loc : string; value_e : Sl_ast.expr }
type range_atom = { base : string; lo : Sl_ast.expr; hi : Sl_ast.expr }

let collect_pt_atoms (s : Sl_ast.sl) : pt_atom list =
  let f_sl acc = function
    | SHeap (HPt { loc = EVar p; value = EVar v; _ }) -> { loc = p; value = v } :: acc
    | _ -> acc
  in
  fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

let collect_pt_atoms_any (s : Sl_ast.sl) : pt_atom_any list =
  let f_sl acc = function
    | SHeap (HPt { loc = EVar p; value; _ }) -> { loc = p; value_e = value } :: acc
    | _ -> acc
  in
  fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

let collect_range_atoms (s : Sl_ast.sl) : range_atom list =
  let f_sl acc = function
    | SHeap (HRange { loc = EVar p; lo; hi; _ }) -> { base = p; lo; hi } :: acc
    | _ -> acc
  in
  fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

let pre_value_to_loc_map (pre_atoms : pt_atom list) : string StringMap.t =
  List.fold_left
    (fun acc { loc; value } -> StringMap.add value loc acc)
    StringMap.empty
    pre_atoms

(***)
(* Rewrite value variables via pre_map: a ↦ *p *)
(***) 

let rewrite_value_vars_with_pre_map (pre_map : string StringMap.t) (s : Sl_ast.sl) : Sl_ast.sl =
  let rec map_expr = function
    | EVar x -> (
        match StringMap.find_opt x pre_map with
        | None -> EVar x
        | Some p -> EDeref (EVar p) )
    | EUnop (op, e1) -> EUnop (op, map_expr e1)
    | EBinop (op, a, b) -> EBinop (op, map_expr a, map_expr b)
    | EApp (f, es) -> EApp (f, List.map map_expr es)
    | EDeref e1 -> EDeref (map_expr e1)
    | EOld e1 -> EOld (map_expr e1)
    | EPost e1 -> EPost (map_expr e1)
    | x -> x
  in
  let rec map_sl = function
    | (STrue | SFalse | SEmp) as x -> x
    | SPure e -> SPure (map_expr e)
    | SHeap (HPt { loc; ty; value }) ->
        SHeap (HPt { loc = map_expr loc; ty; value = map_expr value })
    | SHeap (HRange { loc; ty; lo; hi }) ->
        SHeap (HRange { loc = map_expr loc; ty; lo = map_expr lo; hi = map_expr hi })
    | SHeap (HPred (nm, args)) ->
        SHeap (HPred (nm, List.map map_expr args))
    | SSep xs -> SSep (List.map map_sl xs)
    | SAnd xs -> SAnd (List.map map_sl xs)
    | SOr xs -> SOr (List.map map_sl xs)
    | SNot x -> SNot (map_sl x)
    | SImplies (a, b) -> SImplies (map_sl a, map_sl b)
    | SExists (bs, body) -> SExists (bs, map_sl body)
    | SForall (bs, body) -> SForall (bs, map_sl body)
  in
  map_sl s

(***)
(* Pure ensures sugar *)
(***) 

let collect_heap_equalities_from_pure (s : Sl_ast.sl) : (string * string) list =
  let extract_from_expr (e : Sl_ast.expr) : (string * string) option =
    match e with
    | EBinop (BEq, lhs, rhs) -> (
        match (lhs, rhs) with
        | (EPost (EDeref (EVar a)), EDeref (EVar b)) -> Some (a, b)
        | (EDeref (EVar b), EPost (EDeref (EVar a))) -> Some (a, b)
        | (EDeref (EVar a), EOld (EDeref (EVar b))) -> Some (a, b)
        | (EOld (EDeref (EVar b)), EDeref (EVar a)) -> Some (a, b)
        | (EPost (EDeref (EVar a)), EOld (EDeref (EVar b))) -> Some (a, b)
        | (EOld (EDeref (EVar b)), EPost (EDeref (EVar a))) -> Some (a, b)
        | _ -> None )
    | _ -> None
  in
  let f_sl acc = function
    | SPure e -> (
        match extract_from_expr e with
        | None -> acc
        | Some x -> x :: acc )
    | _ -> acc
  in
  fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

(***)
(* Loop normalization (unchanged) *)
(***) 

let try_rewrite_loop_suffix_write_to_prefix (s : Sl_ast.sl) : Sl_ast.sl option =
  let match_i_le_j = function
    | SPure (EBinop (BLe, EVar i, EVar j)) -> Some (i, j)
    | _ -> None
  in
  let match_j_lt_len = function
    | SPure (EBinop (BLt, EVar j, EVar len)) -> Some (j, len)
    | _ -> None
  in
  let match_post_array_j_eq_0 = function
    | SPure
        (EBinop
           ( BEq,
             EPost (EDeref (EBinop (BAdd, EVar arr, EVar j))),
             EConstInt 0 )) ->
        Some (arr, j)
    | _ -> None
  in
  match s with
  | SForall ([(j, jty)], SImplies (ante, cons)) -> (
      match ante with
      | SAnd [a1; a2] -> (
          match (match_i_le_j a1, match_j_lt_len a2, match_post_array_j_eq_0 cons) with
          | Some (i, j1), Some (j2, _len), Some (arr, j3)
            when j1 = j && j2 = j && j3 = j ->
              let new_ante =
                SAnd
                  [
                    SPure (EBinop (BLe, EConstInt 0, EVar j));
                    SPure (EBinop (BLt, EVar j, EVar i));
                  ]
              in
              let new_cons =
                SPure (EBinop (BEq, EDeref (EBinop (BAdd, EVar arr, EVar j)), EConstInt 0))
              in
              Some (SForall ([(j, jty)], SImplies (new_ante, new_cons)))
          | _ -> None )
      | _ -> None )
  | _ -> None

let rec normalize_loop_assumes (s : Sl_ast.sl) : Sl_ast.sl =
  let rewrite_here x =
    match try_rewrite_loop_suffix_write_to_prefix x with
    | Some y -> y
    | None -> x
  in
  match s with
  | SAnd xs -> SAnd (List.map (fun x -> x |> normalize_loop_assumes |> rewrite_here) xs)
  | SSep xs -> SSep (List.map normalize_loop_assumes xs)
  | SOr xs -> SOr (List.map normalize_loop_assumes xs)
  | SNot x -> SNot (normalize_loop_assumes x)
  | SImplies (a, b) -> SImplies (normalize_loop_assumes a, normalize_loop_assumes b)
  | SForall (bs, body) -> SForall (bs, normalize_loop_assumes body)
  | SExists (bs, body) -> SExists (bs, normalize_loop_assumes body)
  | x -> rewrite_here x

(***)
(* Assigns inference *)
(***) 

let collect_post_vars_in_sl (s : Sl_ast.sl) : StringSet.t =
  let f_expr acc = function
    | EPost (EVar x) -> StringSet.add x acc
    | _ -> acc
  in
  fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

let assigns_from_post_vars (post_sl : Sl_ast.sl) : C.assignable list =
  post_sl |> collect_post_vars_in_sl |> StringSet.elements |> List.map (fun v -> C.AsVar v)

let collect_post_write_bases_in_sl (s : Sl_ast.sl) : StringSet.t =
  let f_expr acc = function
    | EPost (EDeref (EBinop (BAdd, EVar base, _idx))) -> StringSet.add base acc
    | EPost (EDeref (EVar base)) -> StringSet.add base acc
    | _ -> acc
  in
  fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

let expr_mentions_var (x : string) (e : Sl_ast.expr) : bool =
  let found = ref false in
  let f _acc = function
    | EVar y when y = x -> found := true; ()
    | _ -> ()
  in
  ignore (fold_expr ~f (()) e);
  !found

let infer_length_name_from_ranges (ranges : range_atom list) : string option =
  let has_length r = expr_mentions_var "length" r.lo || expr_mentions_var "length" r.hi in
  if List.exists has_length ranges then Some "length" else None

let assigns_from_ranges_if_written
    ~(ranges : range_atom list)
    ~(written_bases : StringSet.t)
    ~(widen_to_full : bool)
  : C.assignable list =
  let len_name = infer_length_name_from_ranges ranges in
  let full_lo = EConstInt 0 in
  let full_hi =
    match len_name with
    | Some len -> EBinop (BSub, EVar len, EConstInt 1)
    | None -> EConstInt 0
  in
  ranges
  |> List.filter (fun { base; _ } -> StringSet.mem base written_bases)
  |> List.map (fun { base; lo; hi } ->
         if widen_to_full then
           C.AsRange (base, term_of_expr C.Pre full_lo, term_of_expr C.Pre full_hi)
         else
           C.AsRange (base, term_of_expr C.Pre lo, term_of_expr C.Pre hi))

(***)
(* Ptr discovery / sharing *)
(***) 

let ptrs_from_atoms (atoms : pt_atom list) : StringSet.t =
  List.fold_left (fun acc { loc; value = _ } -> StringSet.add loc acc) StringSet.empty atoms

let ptrs_of_behavior (b : Sl_ast.behavior) : StringSet.t =
  let (req_opt, ens_opt, _var_opt) = extract_req_ens_var b.body in
  let req_atoms = match req_opt with None -> [] | Some s -> collect_pt_atoms s in
  let ens_atoms = match ens_opt with None -> [] | Some s -> collect_pt_atoms s in
  let pure_eqs = match ens_opt with None -> [] | Some s -> collect_heap_equalities_from_pure s in
  let pure_ptrs =
    List.fold_left
      (fun acc (a, bb) -> acc |> StringSet.add a |> StringSet.add bb)
      StringSet.empty
      pure_eqs
  in
  StringSet.union (ptrs_from_atoms (req_atoms @ ens_atoms)) pure_ptrs

let global_ptrs_of_spec (spec : Sl_ast.spec) : StringSet.t =
  List.fold_left (fun acc b -> StringSet.union acc (ptrs_of_behavior b)) StringSet.empty spec.behaviors

(***)
(* Requires builders *)
(***) 

let mk_valid (x : string) : C.predicate =
  p_atom (C.APred ("valid", [ C.TPtr x ]))

let mk_valid_read_range (base : C.term) (lo : C.term) (hi : C.term) : C.predicate =
  p_atom (C.APred ("valid_read_range", [ base; lo; hi ]))

let assigns_from_ptrs (ptrs : StringSet.t) : C.assignable list =
  ptrs |> StringSet.elements |> List.map (fun p -> C.AsHeap p)

let requires_from_ptrs (ptrs : StringSet.t) : C.predicate =
  ptrs |> StringSet.elements |> List.map mk_valid |> p_and

let requires_from_ranges (ranges : range_atom list) : C.predicate =
  ranges
  |> List.map (fun { base; lo; hi } ->
         mk_valid_read_range
           (C.TVar (C.Pre, base))
           (term_of_expr C.Pre lo)
           (term_of_expr C.Pre hi))
  |> p_and

(***)
(* NEW: infer disequalities from SSep *)
(***) 

let canon_pair (a : string) (b : string) : string * string =
  if String.compare a b <= 0 then (a, b) else (b, a)

(* Collect explicit pure "x != y" present anywhere. *)
let collect_explicit_neq_pairs (s : Sl_ast.sl) : PairSet.t =
  let f_sl acc = function
    | SPure (EBinop (BNeq, EVar a, EVar b)) ->
        PairSet.add (canon_pair a b) acc
    | _ -> acc
  in
  fold_sl ~f_sl ~f_expr:(fun a _ -> a) PairSet.empty s

(* Flatten an SSep list, keeping only heaplet base locations that are variables. *)
let rec collect_sep_loc_vars_in (s : Sl_ast.sl) : StringSet.t list =
  match s with
  | SSep xs ->
      let rec flatten xs =
        List.concat_map
          (fun x ->
             match x with
             | SSep ys -> flatten ys
             | _ -> [ x ])
          xs
      in
      let xs = flatten xs in
      let vars =
        xs
        |> list_filter_map (function
             | SHeap (HPt { loc = EVar p; _ }) -> Some p
             | SHeap (HRange { loc = EVar p; _ }) -> Some p
             | _ -> None)
        |> List.fold_left (fun acc p -> StringSet.add p acc) StringSet.empty
      in
      [ vars ]
  | SAnd xs | SOr xs ->
      List.concat_map collect_sep_loc_vars_in xs
  | SNot x ->
      collect_sep_loc_vars_in x
  | SImplies (a, b) ->
      collect_sep_loc_vars_in a @ collect_sep_loc_vars_in b
  | SForall (_, body) | SExists (_, body) ->
      collect_sep_loc_vars_in body
  | _ ->
      []

let pairwise_neq_pairs (vars : StringSet.t) : PairSet.t =
  let vs = StringSet.elements vars in
  let rec all_pairs acc = function
    | [] -> acc
    | x :: tl ->
        let acc =
          List.fold_left
            (fun a y -> PairSet.add (canon_pair x y) a)
            acc
            tl
        in
        all_pairs acc tl
  in
  all_pairs PairSet.empty vs

let neq_predicate_from_pairs (pairs : PairSet.t) : C.predicate =
  let ps =
    pairs
    |> PairSet.elements
    |> List.map (fun (a, b) -> mk_rel C.Neq (C.TPtr a) (C.TPtr b))
  in
  p_and ps

(* Infer non-aliasing from SSep, skipping any explicit pure x!=y already present. *)
let infer_sep_neqs (req_sl : Sl_ast.sl) : C.predicate =
  let explicit = collect_explicit_neq_pairs req_sl in
  let sep_groups = collect_sep_loc_vars_in req_sl in
  let inferred =
    sep_groups
    |> List.fold_left
         (fun acc group -> PairSet.union acc (pairwise_neq_pairs group))
         PairSet.empty
  in
  let inferred = PairSet.diff inferred explicit in
  neq_predicate_from_pairs inferred

(***)
(* Ensures builders *)
(***) 

let mk_eq (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (C.Eq, t1, t2))

let ensures_from_post_heaplets (post_atoms : pt_atom_any list) : C.predicate =
  post_atoms
  |> List.map (fun { loc = p; value_e } ->
         mk_eq (C.THeap (C.Post, p)) (term_of_expr C.Pre value_e))
  |> p_and

let ensures_from_pure_heap_eqs (eqs : (string * string) list) : C.predicate =
  eqs
  |> List.map (fun (a, b) -> mk_eq (C.THeap (C.Post, a)) (C.THeap (C.Pre, b)))
  |> p_and

let build_ensures ~(post_sl : Sl_ast.sl) : C.predicate =
  let post_heap_atoms = collect_pt_atoms_any post_sl in
  let pure_heap_eqs = collect_heap_equalities_from_pure post_sl in
  let heaplet_part =
    if post_heap_atoms <> [] then ensures_from_post_heaplets post_heap_atoms else C.PTrue
  in
  let pure_part =
    if pure_heap_eqs <> [] then ensures_from_pure_heap_eqs pure_heap_eqs else C.PTrue
  in
  let general_part =
    if post_heap_atoms = [] && pure_heap_eqs = [] then pred_of_sl post_sl else C.PTrue
  in
  p_and [ heaplet_part; pure_part; general_part ]

(***)
(* Spec kind / behavior naming *)
(***) 

let kind_of_spec (spec : Sl_ast.spec) : C.spec_kind =
  let has_variant =
    List.exists
      (fun (b : Sl_ast.behavior) ->
         let (_req, _ens, v) = extract_req_ens_var b.body in
         v <> None)
      spec.behaviors
  in
  if has_variant then C.LoopContract else C.FunctionContract

let normalize_behavior_names (bs : Sl_ast.behavior list) : string option list =
  match bs with
  | [] -> []
  | [ b ] -> [ b.name ]
  | _ ->
      bs
      |> List.mapi (fun i b ->
             match b.name with
             | Some nm -> Some nm
             | None -> Some (Printf.sprintf "case%d" (i + 1)))

(***)
(* Analysis record *)
(***) 

type ptrs_choice =
  | LocalPerBehavior
  | GlobalShared of StringSet.t

let ptrs_for (choice : ptrs_choice) (b : Sl_ast.behavior) : StringSet.t =
  match choice with
  | LocalPerBehavior -> ptrs_of_behavior b
  | GlobalShared g -> g

type beh_analysis = {
  req_sl : Sl_ast.sl option;
  ens_sl : Sl_ast.sl option;
  var_expr : Sl_ast.expr option;

  assumes_sl : Sl_ast.sl;
  assumes_p : C.predicate;

  (* pure(req) always contributes to Requires *)
  req_pure : C.predicate;

  (* NEW: inferred non-aliasing from SSep in req *)
  req_sep_neqs : C.predicate;

  pre_atoms : pt_atom list;
  pre_map : string StringMap.t;
  req_ranges : range_atom list;

  post_sl_opt : Sl_ast.sl option;
  ensures_p : C.predicate;

  ptrs : StringSet.t;
}

(***)
(* Behavior analysis *)
(***) 

let analyze_behavior
    ~(kind : C.spec_kind)
    ~(spec_ret : string option)
    ~(ptrs_choice : ptrs_choice)
    (b : Sl_ast.behavior)
  : beh_analysis
  =
  let (req_opt, ens_opt, var_opt) = extract_req_ens_var b.body in

  let pre_source =
    match kind with
    | C.FunctionContract -> req_opt
    | C.LoopContract -> Some b.assumes
  in

  let pre_atoms = match pre_source with None -> [] | Some s -> collect_pt_atoms s in
  let pre_map = pre_value_to_loc_map pre_atoms in
  let req_ranges = match pre_source with None -> [] | Some s -> collect_range_atoms s in

  let assumes_sl_raw =
    match kind with
    | C.LoopContract -> normalize_loop_assumes b.assumes
    | C.FunctionContract -> b.assumes
  in
  let assumes_sl = rewrite_value_vars_with_pre_map pre_map assumes_sl_raw in
  let assumes_p = pred_of_sl assumes_sl in

  (* req: (1) infer sep neq from original req; (2) rewrite value vars for pure translation *)
  let req_sep_neqs =
    match req_opt with
    | None -> C.PTrue
    | Some req_sl -> infer_sep_neqs req_sl
  in

  let req_pure =
    match req_opt with
    | None -> C.PTrue
    | Some req_sl ->
        let req_sl' = rewrite_value_vars_with_pre_map pre_map req_sl in
        pred_of_sl req_sl'
  in

  let post_sl_opt =
    match ens_opt with
    | None -> None
    | Some post0 ->
        let post1 =
          match spec_ret with
          | None -> post0
          | Some r -> rewrite_result r post0
        in
        let post2 = rewrite_value_vars_with_pre_map pre_map post1 in
        Some post2
  in

  let ensures_p =
    match post_sl_opt with
    | None -> C.PTrue
    | Some post_sl -> build_ensures ~post_sl
  in

  let ptrs = ptrs_for ptrs_choice b in

  {
    req_sl = req_opt;
    ens_sl = ens_opt;
    var_expr = var_opt;

    assumes_sl;
    assumes_p;

    req_pure;
    req_sep_neqs;

    pre_atoms;
    pre_map;
    req_ranges;

    post_sl_opt;
    ensures_p;

    ptrs;
  }

(***)
(* Clause builders *)
(***) 

(* IMPORTANT: order here matters for your golden outputs.
   For spatial notation you want:
     requires p != q && \valid(p) && \valid(q) [&& ...]
   So put sep-neqs first.
*)
let mk_requires
    ~(ptrs : StringSet.t)
    ~(ranges : range_atom list)
    ~(sep_neqs : C.predicate)
    ~(pure : C.predicate)
  : C.clause
  =
  let p_valid = requires_from_ptrs ptrs in
  let p_read  = requires_from_ranges ranges in
  C.Requires (p_and [ sep_neqs; p_valid; p_read; pure ])

let mk_assigns
    ~(kind : C.spec_kind)
    ~(ptrs : StringSet.t)
    ~(req_ranges : range_atom list)
    ~(assumes_sl_for_writes : Sl_ast.sl)
    ~(post_sl_opt : Sl_ast.sl option)
  : C.clause
  =
  match kind with
  | C.FunctionContract ->
      let written_bases =
        match post_sl_opt with
        | None -> StringSet.empty
        | Some post_sl -> collect_post_write_bases_in_sl post_sl
      in
      let range_assigns =
        assigns_from_ranges_if_written ~ranges:req_ranges ~written_bases ~widen_to_full:false
      in
      let range_bases =
        List.fold_left
          (fun acc -> function
             | C.AsRange (p, _, _) -> StringSet.add p acc
             | _ -> acc)
          StringSet.empty
          range_assigns
      in
      let heap_assigns =
        assigns_from_ptrs ptrs
        |> List.filter (function
             | C.AsHeap p -> not (StringSet.mem p range_bases)
             | _ -> true)
      in
      C.Assigns (range_assigns @ heap_assigns)

  | C.LoopContract ->
      let var_assigns =
        match post_sl_opt with
        | None -> []
        | Some post_sl -> assigns_from_post_vars post_sl
      in
      let written_bases = collect_post_write_bases_in_sl assumes_sl_for_writes in
      let range_assigns =
        assigns_from_ranges_if_written ~ranges:req_ranges ~written_bases ~widen_to_full:true
      in
      C.Assigns (var_assigns @ range_assigns)

let mk_variant (vopt : Sl_ast.expr option) : C.clause list =
  match vopt with
  | None -> []
  | Some e -> [ C.Variant (term_of_expr C.Pre e) ]

let build_core_behavior
    ~(kind : C.spec_kind)
    ~(b_name : string option)
    ~(assumes_sl_for_writes : Sl_ast.sl)
    (a : beh_analysis)
  : C.behavior
  =
  let clauses =
    [
      C.Assumes a.assumes_p;
      mk_requires ~ptrs:a.ptrs ~ranges:a.req_ranges ~sep_neqs:a.req_sep_neqs ~pure:a.req_pure;
      C.Ensures a.ensures_p;
      mk_assigns
        ~kind
        ~ptrs:a.ptrs
        ~req_ranges:a.req_ranges
        ~assumes_sl_for_writes
        ~post_sl_opt:a.post_sl_opt;
    ]
    @ mk_variant a.var_expr
  in
  { C.b_name; clauses }

let behavior_of_sl
    ~(kind : C.spec_kind)
    ~(spec_ret : string option)
    ~(b_name : string option)
    ~(ptrs_choice : ptrs_choice)
    (b : Sl_ast.behavior)
  : C.behavior
  =
  let assumes_sl_for_writes = b.assumes in
  let a = analyze_behavior ~kind ~spec_ret ~ptrs_choice b in
  build_core_behavior ~kind ~b_name ~assumes_sl_for_writes a

(***)
(* Entry point *)
(***) 

let sl_to_core (spec : Sl_ast.spec) : C.spec =
  let kind = kind_of_spec spec in
  let names = normalize_behavior_names spec.behaviors in

  let ptrs_choice =
    match spec.behaviors with
    | [] | [ _ ] -> LocalPerBehavior
    | _ -> GlobalShared (global_ptrs_of_spec spec)
  in

  let behaviors =
    List.map2
      (fun nm b -> behavior_of_sl ~kind ~spec_ret:spec.ret ~b_name:nm ~ptrs_choice b)
      names
      spec.behaviors
  in

  { C.kind = kind; params = []; behaviors }
