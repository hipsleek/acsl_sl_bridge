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

module Util = struct
  let ( let* ) x f = match x with None -> None | Some v -> f v

  let list_filter_map f xs =
    let rec go acc = function
      | [] -> List.rev acc
      | x :: tl -> (
          match f x with
          | None -> go acc tl
          | Some y -> go (y :: acc) tl)
    in
    go [] xs

  let rec flatten_and (ps : C.predicate list) : C.predicate list =
    match ps with
    | [] -> []
    | p :: tl -> (
        match p with
        | C.PTrue -> flatten_and tl
        | C.PAnd qs -> flatten_and (qs @ tl)
        | _ -> p :: flatten_and tl)

  let rec flatten_or (ps : C.predicate list) : C.predicate list =
    match ps with
    | [] -> []
    | p :: tl -> (
        match p with
        | C.PFalse -> flatten_or tl
        | C.POr qs -> flatten_or (qs @ tl)
        | _ -> p :: flatten_or tl)

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

  let p_atom (a : C.atom) : C.predicate = C.PAtom a

  let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
    p_atom (C.ARel (r, t1, t2))

  let mk_eq (t1 : C.term) (t2 : C.term) : C.predicate =
    p_atom (C.ARel (C.Eq, t1, t2))
end

module Traverse = struct
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
            fold_expr ~f:f_expr acc hi)
    | SPure e -> fold_expr ~f:f_expr acc e
    | SSep xs | SAnd xs | SOr xs ->
        List.fold_left (fun a x -> fold_sl ~f_sl ~f_expr a x) acc xs
    | SNot x -> fold_sl ~f_sl ~f_expr acc x
    | SImplies (a, b) ->
        let acc = fold_sl ~f_sl ~f_expr acc a in
        fold_sl ~f_sl ~f_expr acc b
    | SExists (_, body) | SForall (_, body) -> fold_sl ~f_sl ~f_expr acc body
end

module Binder = struct
  let core_ty_of_sort_opt (s : Sl_ast.sort option) : string option =
    match s with
    | None -> None
    | Some SInt -> Some "int"
    | Some SBool -> Some "bool"
    | Some SPtr -> None
    | Some (SUser s) -> Some s

  let binders_of_sl (bs : (ident * sort option) list) : C.binder list =
    List.map (fun (nm, tyopt) -> { C.b_name = nm; b_ty = core_ty_of_sort_opt tyopt }) bs
end

module Op = struct
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
end

module Expr = struct
  let rec term_of_expr (kind : C.spec_kind) (default_phase : C.phase) (e : Sl_ast.expr) : C.term =
    match e with
    | EVar x -> C.TVar (default_phase, x)
    | EConstInt n -> C.TInt n
    | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
    | EResult -> C.TResult
    | EApp (f, args) -> C.TApp (f, List.map (term_of_expr kind default_phase) args)
    | EUnop (UNeg, e1) ->
        C.TArith (C.Sub, C.TInt 0, term_of_expr kind default_phase e1)
    | EUnop (UNot, e1) ->
        C.TApp ("not", [ term_of_expr kind default_phase e1 ])
    | EDeref (EBinop (BAdd, base, idx)) ->
        let sub_ph = if default_phase = C.LoopEntry then C.Post else default_phase in
        C.TIndex
          ( default_phase,
            term_of_expr kind sub_ph base,
            term_of_expr kind sub_ph idx )
    | EDeref e1 ->
        let sub_ph = if default_phase = C.LoopEntry then C.Post else default_phase in
        C.TLoad (default_phase, term_of_expr kind sub_ph e1)
    | EOld e1 ->
        let ph =
          match kind with
          | C.LoopContract -> C.LoopEntry
          | C.FunctionContract -> C.Pre
        in
        term_of_expr kind ph e1
    | EPost e1 -> term_of_expr kind C.Post e1
    | EBinop (op, e1, e2) -> (
        match Op.arith_of_binop op with
        | Some aop ->
            C.TArith
              ( aop,
                term_of_expr kind default_phase e1,
                term_of_expr kind default_phase e2 )
        | None ->
            C.TApp
              ( "binop",
                [ term_of_expr kind default_phase e1; term_of_expr kind default_phase e2 ] ))
end

module Pred = struct
  let pred_of_cmp_expr (kind : C.spec_kind) (default_phase : C.phase) (e : Sl_ast.expr) :
      C.predicate =
    match e with
    | EBinop (op, e1, e2) -> (
        match Op.rel_of_binop op with
        | Some r ->
            Util.mk_rel r
              (Expr.term_of_expr kind default_phase e1)
              (Expr.term_of_expr kind default_phase e2)
        | None ->
            Util.p_atom (C.APred ("bool", [ Expr.term_of_expr kind default_phase e ])))
    | _ -> Util.p_atom (C.APred ("bool", [ Expr.term_of_expr kind default_phase e ]))

  let rec pred_of_sl (kind : C.spec_kind) (s : Sl_ast.sl) : C.predicate =
    match s with
    | STrue -> C.PTrue
    | SFalse -> C.PFalse
    | SEmp -> C.PTrue
    | SHeap _ -> C.PTrue
    | SPure e -> pred_of_cmp_expr kind C.Pre e
    | SSep xs | SAnd xs -> Util.p_and (List.map (pred_of_sl kind) xs)
    | SOr xs -> Util.p_or (List.map (pred_of_sl kind) xs)
    | SNot x -> C.PNot (pred_of_sl kind x)
    | SImplies (a, b) -> C.PImplies (pred_of_sl kind a, pred_of_sl kind b)
    | SForall (bs, body) -> C.PForall (Binder.binders_of_sl bs, pred_of_sl kind body)
    | SExists (bs, body) -> C.PExists (Binder.binders_of_sl bs, pred_of_sl kind body)
end

module Block = struct
  let extract_req_ens_var (body : Sl_ast.block) : Sl_ast.sl option * Sl_ast.sl option * Sl_ast.expr option
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
end

module Rewrite = struct
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
      | SPure e -> SPure (map_expr e)
      | SHeap (HPt { loc; ty; value; mode }) ->
          SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
      | SHeap (HRange { loc; alias; ty; lo; hi; mode }) ->
          SHeap (HRange { loc = map_expr loc; alias; ty; lo = map_expr lo; hi = map_expr hi; mode })
      | SHeap (HPred (nm, args)) -> SHeap (HPred (nm, List.map map_expr args))
      | SSep xs -> SSep (List.map map_sl xs)
      | SAnd xs -> SAnd (List.map map_sl xs)
      | SOr xs -> SOr (List.map map_sl xs)
      | SNot x -> SNot (map_sl x)
      | SImplies (a, b) -> SImplies (map_sl a, map_sl b)
      | SExists (bs, body) -> SExists (bs, map_sl body)
      | SForall (bs, body) -> SForall (bs, map_sl body)
    in
    map_sl s

  let pre_value_to_loc_map (pre_atoms : (string * string) list) : string StringMap.t =
    List.fold_left (fun acc (loc, value) -> StringMap.add value loc acc) StringMap.empty pre_atoms

  let rewrite_value_vars_with_pre_map (pre_map : string StringMap.t) (s : Sl_ast.sl) : Sl_ast.sl =
    let rec map_expr = function
      | EVar x -> (
          match StringMap.find_opt x pre_map with
          | None -> EVar x
          | Some p -> EDeref (EVar p))
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
      | SHeap (HPt { loc; ty; value; mode }) ->
          SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
      | SHeap (HRange { loc; alias; ty; lo; hi; mode }) ->
          SHeap (HRange { loc = map_expr loc; alias; ty; lo = map_expr lo; hi = map_expr hi; mode })
      | SHeap (HPred (nm, args)) -> SHeap (HPred (nm, List.map map_expr args))
      | SSep xs -> SSep (List.map map_sl xs)
      | SAnd xs -> SAnd (List.map map_sl xs)
      | SOr xs -> SOr (List.map map_sl xs)
      | SNot x -> SNot (map_sl x)
      | SImplies (a, b) -> SImplies (map_sl a, map_sl b)
      | SExists (bs, body) -> SExists (bs, map_sl body)
      | SForall (bs, body) -> SForall (bs, map_sl body)
    in
    map_sl s
end

module Heap = struct
  type pt_atom = { loc : string; value : string }
  type pt_atom_any = { loc : string; value_e : Sl_ast.expr }

  type range_atom = { base : string; lo : Sl_ast.expr; hi : Sl_ast.expr; mode : Sl_ast.heap_mode }

  let collect_range_aliases (s : Sl_ast.sl) : string StringMap.t =
    let f_sl acc = function
      | SHeap (HRange { loc = EVar base; alias = Some a; _ }) -> StringMap.add a base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) StringMap.empty s

  let collect_pt_atoms (s : Sl_ast.sl) : pt_atom list =
    let f_sl acc = function
      | SHeap (HPt { loc = EVar p; value = EVar v; _ }) -> { loc = p; value = v } :: acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

  let collect_pt_atoms_any (s : Sl_ast.sl) : pt_atom_any list =
    let f_sl acc = function
      | SHeap (HPt { loc = EVar p; value; _ }) -> { loc = p; value_e = value } :: acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

  let collect_range_atoms (s : Sl_ast.sl) : range_atom list =
    let f_sl acc = function
      | SHeap (HRange { loc = EVar p; lo; hi; mode; _ }) -> { base = p; lo; hi; mode } :: acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev

  let ptrs_from_pt_atoms (atoms : pt_atom list) : StringSet.t =
    List.fold_left (fun acc ({ loc; value = _ } : pt_atom) -> StringSet.add loc acc) StringSet.empty atoms

  let pre_pairs_for_map (atoms : pt_atom list) : (string * string) list =
    List.map (fun { loc; value } -> (loc, value)) atoms
end

module Desugar = struct
  let desugar_expr ~(alias_map : string StringMap.t) (e : Sl_ast.expr) : Sl_ast.expr =
    let rec alias = function
      | EVar x -> (
          match StringMap.find_opt x alias_map with
          | Some base -> EVar base
          | None -> EVar x)
      | EUnop (op, e1) -> EUnop (op, alias e1)
      | EBinop (op, a, b) -> EBinop (op, alias a, alias b)
      | EApp (f, es) -> EApp (f, List.map alias es)
      | EDeref e1 -> EDeref (alias e1)
      | EOld e1 -> EOld (alias e1)
      | EPost e1 -> EPost (alias e1)
      | x -> x
    in
    let rec collapse = function
      | EDeref (EBinop (BAdd, EVar base1, EBinop (BSub, p, EVar base2))) when base1 = base2 ->
          EDeref (collapse (alias p))
      | EUnop (op, e1) -> EUnop (op, collapse e1)
      | EBinop (op, a, b) -> EBinop (op, collapse a, collapse b)
      | EApp (f, es) -> EApp (f, List.map collapse es)
      | EDeref e1 -> EDeref (collapse e1)
      | EOld e1 -> EOld (collapse e1)
      | EPost e1 -> EPost (collapse e1)
      | x -> x
    in
    e |> alias |> collapse

  let desugar_sl ~(alias_map : string StringMap.t) (s : Sl_ast.sl) : Sl_ast.sl =
    let map_expr = desugar_expr ~alias_map in
    let rec map_sl = function
      | (STrue | SFalse | SEmp) as x -> x
      | SPure e -> SPure (map_expr e)
      | SHeap (HPt { loc; ty; value; mode }) ->
          SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
      | SHeap (HRange { loc; alias; ty; lo; hi; mode }) ->
          SHeap (HRange { loc = map_expr loc; alias; ty; lo = map_expr lo; hi = map_expr hi; mode })
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
end

module Sugar = struct
  let collect_heap_equalities_from_pure (s : Sl_ast.sl) : (string * string) list =
    let extract_from_expr (e : Sl_ast.expr) : (string * string) option =
      match e with
      | EBinop (BEq, lhs, rhs) -> (
          match (lhs, rhs) with
          | EPost (EDeref (EVar a)), EDeref (EVar b) -> Some (a, b)
          | EDeref (EVar b), EPost (EDeref (EVar a)) -> Some (a, b)
          | EDeref (EVar a), EOld (EDeref (EVar b)) -> Some (a, b)
          | EOld (EDeref (EVar b)), EDeref (EVar a) -> Some (a, b)
          | EPost (EDeref (EVar a)), EOld (EDeref (EVar b)) -> Some (a, b)
          | EOld (EDeref (EVar b)), EPost (EDeref (EVar a)) -> Some (a, b)
          | _ -> None)
      | _ -> None
    in
    let f_sl acc = function
      | SPure e -> (
          match extract_from_expr e with
          | None -> acc
          | Some x -> x :: acc)
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev
end

module LoopNorm = struct
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
      | SPure (EBinop (BEq, EPost (EDeref (EBinop (BAdd, EVar arr, EVar j))), EConstInt 0)) ->
          Some (arr, j)
      | _ -> None
    in
    match s with
    | SForall ([(j, jty)], SImplies (ante, cons)) -> (
        match ante with
        | SAnd [ a1; a2 ] -> (
            match (match_i_le_j a1, match_j_lt_len a2, match_post_array_j_eq_0 cons) with
            | Some (i, j1), Some (j2, _len), Some (arr, j3) when j1 = j && j2 = j && j3 = j ->
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
            | _ -> None)
        | _ -> None)
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
end

module Collect = struct
  let vars_in_expr (e : Sl_ast.expr) : StringSet.t =
    let f acc = function
      | EVar x -> StringSet.add x acc
      | _ -> acc
    in
    Traverse.fold_expr ~f StringSet.empty e

  let expr_mentions_var (x : string) (e : Sl_ast.expr) : bool =
    let found = ref false in
    let f () = function
      | EVar y when y = x ->
          found := true;
          ()
      | _ -> ()
    in
    ignore (Traverse.fold_expr ~f () e);
    !found

  let deref_bases (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EDeref (EBinop (BAdd, EVar base, _idx)) -> StringSet.add base acc
      | EDeref (EVar base) -> StringSet.add base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let old_deref_bases (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EOld (EDeref (EBinop (BAdd, EVar base, _idx))) -> StringSet.add base acc
      | EOld (EDeref (EVar base)) -> StringSet.add base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let post_vars (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EPost (EVar x) -> StringSet.add x acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let old_vars (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EOld (EVar x) -> StringSet.add x acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let post_write_bases (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EPost (EDeref (EBinop (BAdd, EVar base, _idx))) -> StringSet.add base acc
      | EPost (EDeref (EVar base)) -> StringSet.add base acc
      | EDeref (EBinop (BAdd, EPost (EVar base), _idx)) -> StringSet.add base acc
      | EDeref (EPost (EVar base)) -> StringSet.add base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s
end

module Build = struct
  let mk_valid (x : string) : C.predicate =
    Util.p_atom (C.APred ("valid", [ C.TPtr x ]))

  let mk_valid_read_range (base : C.term) (lo : C.term) (hi : C.term) : C.predicate =
    Util.p_atom (C.APred ("valid_read_range", [ base; lo; hi ]))

  let mk_valid_range (base : C.term) (lo : C.term) (hi : C.term) : C.predicate =
    Util.p_atom (C.APred ("valid_range", [ base; lo; hi ]))

  let requires_from_ptrs (ptrs : StringSet.t) : C.predicate =
    ptrs |> StringSet.elements |> List.map mk_valid |> Util.p_and

  let requires_from_ranges (kind : C.spec_kind) (ranges : Heap.range_atom list) : C.predicate =
    ranges
    |> List.map (fun { Heap.base; lo; hi; mode } ->
           let base_t = C.TVar (C.Pre, base) in
           let lo_t = Expr.term_of_expr kind C.Pre lo in
           let hi_t = Expr.term_of_expr kind C.Pre hi in
           match mode with
           | Sl_ast.In -> mk_valid_read_range base_t lo_t hi_t
           | Sl_ast.Default -> mk_valid_range base_t lo_t hi_t)
    |> Util.p_and

  let assigns_from_ptrs (ptrs : StringSet.t) : C.assignable list =
    ptrs |> StringSet.elements |> List.map (fun p -> C.AsHeap p)

  let infer_length_name_from_ranges (ranges : Heap.range_atom list) : string option =
    let has_length (r : Heap.range_atom) =
      Collect.expr_mentions_var "length" r.Heap.lo || Collect.expr_mentions_var "length" r.Heap.hi
    in
    if List.exists has_length ranges then Some "length" else None

  let assigns_from_ranges_if_written
      ~(kind : C.spec_kind)
      ~(ranges : Heap.range_atom list)
      ~(written_bases : StringSet.t)
      ~(widen_to_full : bool)
    : C.assignable list
    =
    let len_name = infer_length_name_from_ranges ranges in
    let full_lo = EConstInt 0 in
    let full_hi =
      match len_name with
      | Some len -> EBinop (BSub, EVar len, EConstInt 1)
      | None -> EConstInt 0
    in
    ranges
    |> List.filter (fun { Heap.base; _ } -> StringSet.mem base written_bases)
    |> List.map (fun { Heap.base; lo; hi; _ } ->
           if widen_to_full then
             C.AsRange
               ( base,
                 Expr.term_of_expr kind C.Pre full_lo,
                 Expr.term_of_expr kind C.Pre full_hi )
           else
             C.AsRange
               ( base,
                 Expr.term_of_expr kind C.Pre lo,
                 Expr.term_of_expr kind C.Pre hi ))

  let progress_vars_from_variant (e : Sl_ast.expr) : StringSet.t =
    match e with
    | EVar v -> StringSet.singleton v
    | EBinop (BSub, _bound, EVar v) -> StringSet.singleton v
    | _ -> Collect.vars_in_expr e

  let mk_variant (kind : C.spec_kind) (vopt : Sl_ast.expr option) : C.clause list =
    match vopt with
    | None -> []
    | Some e -> [ C.Variant (Expr.term_of_expr kind C.Pre e) ]
end

module Ptrs = struct
  let ptrs_of_behavior (b : Sl_ast.behavior) : StringSet.t =
    let req_opt, ens_opt, _var_opt = Block.extract_req_ens_var b.body in
    let req_atoms = match req_opt with None -> [] | Some s -> Heap.collect_pt_atoms s in
    let ens_atoms = match ens_opt with None -> [] | Some s -> Heap.collect_pt_atoms s in
    let pure_eqs = match ens_opt with None -> [] | Some s -> Sugar.collect_heap_equalities_from_pure s in
    let pure_ptrs =
      List.fold_left
        (fun acc (a, bb) -> acc |> StringSet.add a |> StringSet.add bb)
        StringSet.empty
        pure_eqs
    in
    StringSet.union (Heap.ptrs_from_pt_atoms (req_atoms @ ens_atoms)) pure_ptrs

  let global_ptrs_of_spec (spec : Sl_ast.spec) : StringSet.t =
    List.fold_left (fun acc b -> StringSet.union acc (ptrs_of_behavior b)) StringSet.empty spec.behaviors
end

module SepNeq = struct
  let canon_pair (a : string) (b : string) : string * string =
    if String.compare a b <= 0 then (a, b) else (b, a)

  let collect_explicit_neq_pairs (s : Sl_ast.sl) : PairSet.t =
    let f_sl acc = function
      | SPure (EBinop (BNeq, EVar a, EVar b)) -> PairSet.add (canon_pair a b) acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) PairSet.empty s

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
          |> Util.list_filter_map (function
               | SHeap (HPt { loc = EVar p; _ }) -> Some p
               | SHeap (HRange { loc = EVar p; _ }) -> Some p
               | _ -> None)
          |> List.fold_left (fun acc p -> StringSet.add p acc) StringSet.empty
        in
        [ vars ]
    | SAnd xs | SOr xs -> List.concat_map collect_sep_loc_vars_in xs
    | SNot x -> collect_sep_loc_vars_in x
    | SImplies (a, b) -> collect_sep_loc_vars_in a @ collect_sep_loc_vars_in b
    | SForall (_, body) | SExists (_, body) -> collect_sep_loc_vars_in body
    | _ -> []

  let pairwise_neq_pairs (vars : StringSet.t) : PairSet.t =
    let vs = StringSet.elements vars in
    let rec all_pairs acc = function
      | [] -> acc
      | x :: tl ->
          let acc =
            List.fold_left (fun a y -> PairSet.add (canon_pair x y) a) acc tl
          in
          all_pairs acc tl
    in
    all_pairs PairSet.empty vs

  let neq_predicate_from_pairs (pairs : PairSet.t) : C.predicate =
    let ps =
      pairs
      |> PairSet.elements
      |> List.map (fun (a, b) -> Util.mk_rel C.Neq (C.TPtr a) (C.TPtr b))
    in
    Util.p_and ps

  let infer_sep_neqs (req_sl : Sl_ast.sl) : C.predicate =
    let explicit = collect_explicit_neq_pairs req_sl in
    let sep_groups = collect_sep_loc_vars_in req_sl in
    let inferred =
      sep_groups
      |> List.fold_left (fun acc group -> PairSet.union acc (pairwise_neq_pairs group)) PairSet.empty
    in
    let inferred = PairSet.diff inferred explicit in
    neq_predicate_from_pairs inferred
end

module Ensures = struct
  let ensures_from_post_heaplets (kind : C.spec_kind) (post_atoms : Heap.pt_atom_any list) : C.predicate =
    post_atoms
    |> List.map (fun { Heap.loc = p; value_e } ->
           Util.mk_eq (C.THeap (C.Post, p)) (Expr.term_of_expr kind C.Pre value_e))
    |> Util.p_and

  let ensures_from_pure_heap_eqs (eqs : (string * string) list) : C.predicate =
    eqs
    |> List.map (fun (a, b) -> Util.mk_eq (C.THeap (C.Post, a)) (C.THeap (C.Pre, b)))
    |> Util.p_and

  let build_ensures ~(kind : C.spec_kind) ~(post_sl : Sl_ast.sl) : C.predicate =
    let post_heap_atoms = Heap.collect_pt_atoms_any post_sl in
    let pure_heap_eqs = Sugar.collect_heap_equalities_from_pure post_sl in
    let heaplet_part =
      if post_heap_atoms <> [] then ensures_from_post_heaplets kind post_heap_atoms else C.PTrue
    in
    let pure_part =
      if pure_heap_eqs <> [] then ensures_from_pure_heap_eqs pure_heap_eqs else C.PTrue
    in
    let general_part =
      if post_heap_atoms = [] && pure_heap_eqs = [] then Pred.pred_of_sl kind post_sl else C.PTrue
    in
    Util.p_and [ heaplet_part; pure_part; general_part ]
end

module SpecInfo = struct
  let kind_of_spec (spec : Sl_ast.spec) : C.spec_kind =
    let has_variant =
      List.exists
        (fun (b : Sl_ast.behavior) ->
          let _req, _ens, v = Block.extract_req_ens_var b.body in
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
end

type ptrs_choice =
  | LocalPerBehavior
  | GlobalShared of StringSet.t

let ptrs_for (choice : ptrs_choice) (b : Sl_ast.behavior) : StringSet.t =
  match choice with
  | LocalPerBehavior -> Ptrs.ptrs_of_behavior b
  | GlobalShared g -> g

type beh_analysis = {
  req_sl : Sl_ast.sl option;
  ens_sl : Sl_ast.sl option;
  var_expr : Sl_ast.expr option;

  assumes_sl : Sl_ast.sl;
  assumes_p : C.predicate;

  req_pure : C.predicate;
  req_sep_neqs : C.predicate;

  pre_atoms : Heap.pt_atom list;
  pre_map : string StringMap.t;
  req_ranges : Heap.range_atom list;

  post_sl_opt : Sl_ast.sl option;
  ensures_p : C.predicate;

  ptrs : StringSet.t;
}

let analyze_behavior
    ~(kind : C.spec_kind)
    ~(spec_ret : string option)
    ~(ptrs_choice : ptrs_choice)
    (b : Sl_ast.behavior)
  : beh_analysis
  =
  let req_opt0, ens_opt0, var_opt = Block.extract_req_ens_var b.body in

  let pre_source0 =
    match kind with
    | C.FunctionContract -> req_opt0
    | C.LoopContract -> (match req_opt0 with Some r -> Some r | None -> Some b.assumes)
  in

  (* desugar alias + array[p-array] collapse based on range alias in the pre-source *)
  let alias_map =
    match pre_source0 with
    | None -> StringMap.empty
    | Some s -> Heap.collect_range_aliases s
  in

  let req_opt = Option.map (Desugar.desugar_sl ~alias_map) req_opt0 in
  let ens_opt = Option.map (Desugar.desugar_sl ~alias_map) ens_opt0 in

  let pre_source =
    match kind with
    | C.FunctionContract -> req_opt
    | C.LoopContract -> (match req_opt with Some r -> Some r | None -> Some (Desugar.desugar_sl ~alias_map b.assumes))
  in

  let pre_atoms = match pre_source with None -> [] | Some s -> Heap.collect_pt_atoms s in
  let pre_pairs = Heap.pre_pairs_for_map pre_atoms in
  let pre_map = Rewrite.pre_value_to_loc_map pre_pairs in
  let req_ranges = match pre_source with None -> [] | Some s -> Heap.collect_range_atoms s in

  let assumes_sl_raw =
    match kind with
    | C.LoopContract -> LoopNorm.normalize_loop_assumes (Desugar.desugar_sl ~alias_map b.assumes)
    | C.FunctionContract -> Desugar.desugar_sl ~alias_map b.assumes
  in
  let assumes_sl = Rewrite.rewrite_value_vars_with_pre_map pre_map assumes_sl_raw in
  let assumes_p = Pred.pred_of_sl kind assumes_sl in

  let req_sep_neqs =
    match req_opt with
    | None -> C.PTrue
    | Some req_sl -> SepNeq.infer_sep_neqs req_sl
  in

  let req_pure =
    match req_opt with
    | None -> C.PTrue
    | Some req_sl ->
        let req_sl' = Rewrite.rewrite_value_vars_with_pre_map pre_map req_sl in
        Pred.pred_of_sl kind req_sl'
  in

  let post_sl_opt =
    match ens_opt with
    | None -> None
    | Some post0 ->
        let post1 =
          match spec_ret with
          | None -> post0
          | Some r -> Rewrite.rewrite_result r post0
        in
        let post1 = Desugar.desugar_sl ~alias_map post1 in
        let post2 = Rewrite.rewrite_value_vars_with_pre_map pre_map post1 in
        Some post2
  in

  let ensures_p =
    match post_sl_opt with
    | None -> C.PTrue
    | Some post_sl -> Ensures.build_ensures ~kind ~post_sl
  in

  let ptrs = ptrs_for ptrs_choice b in

  {
    req_sl = req_opt0;
    ens_sl = ens_opt0;
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

let mk_requires
    ~(kind : C.spec_kind)
    ~(ptrs : StringSet.t)
    ~(ranges : Heap.range_atom list)
    ~(sep_neqs : C.predicate)
    ~(pure : C.predicate)
  : C.clause
  =
  let p_valid = Build.requires_from_ptrs ptrs in
  let p_read = Build.requires_from_ranges kind ranges in
  C.Requires (Util.p_and [ sep_neqs; p_valid; p_read; pure ])

let mk_assigns
    ~(kind : C.spec_kind)
    ~(ptrs : StringSet.t)
    ~(req_ranges : Heap.range_atom list)
    ~(assumes_sl_for_writes : Sl_ast.sl)
    ~(post_sl_opt : Sl_ast.sl option)
    ~(var_expr : Sl_ast.expr option)
  : C.clause
  =
  match kind with
  | C.FunctionContract ->
      let written_bases =
        match post_sl_opt with
        | None -> StringSet.empty
        | Some post_sl -> Collect.post_write_bases post_sl
      in
      let range_assigns =
        Build.assigns_from_ranges_if_written
          ~kind
          ~ranges:req_ranges
          ~written_bases
          ~widen_to_full:false
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
        Build.assigns_from_ptrs ptrs
        |> List.filter (function
             | C.AsHeap p -> not (StringSet.mem p range_bases)
             | _ -> true)
      in
      C.Assigns (range_assigns @ heap_assigns)

  | C.LoopContract ->
      let post_vars =
        match post_sl_opt with
        | None -> StringSet.empty
        | Some post_sl -> StringSet.union (Collect.post_vars post_sl) (Collect.old_vars post_sl)
      in

      let explicit_write_bases =
        match post_sl_opt with
        | None -> StringSet.empty
        | Some post_sl -> Collect.post_write_bases post_sl
      in

      let inv_current = Collect.deref_bases assumes_sl_for_writes in
      let inv_old = Collect.old_deref_bases assumes_sl_for_writes in
      let inv_write_bases = StringSet.inter inv_current inv_old in
      let written_bases = StringSet.union explicit_write_bases inv_write_bases in

      let range_assigns =
        Build.assigns_from_ranges_if_written
          ~kind
          ~ranges:req_ranges
          ~written_bases
          ~widen_to_full:true
      in

      let progress_vars =
        match var_expr with
        | None -> StringSet.empty
        | Some e -> Build.progress_vars_from_variant e
      in

      let all_var_assigns =
        StringSet.union post_vars progress_vars
        |> StringSet.elements
        |> List.map (fun v -> C.AsVar v)
      in

      C.Assigns (all_var_assigns @ range_assigns)

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
      mk_requires ~kind ~ptrs:a.ptrs ~ranges:a.req_ranges ~sep_neqs:a.req_sep_neqs ~pure:a.req_pure;
      C.Ensures a.ensures_p;
      mk_assigns
        ~kind
        ~ptrs:a.ptrs
        ~req_ranges:a.req_ranges
        ~assumes_sl_for_writes
        ~post_sl_opt:a.post_sl_opt
        ~var_expr:a.var_expr;
    ]
    @ Build.mk_variant kind a.var_expr
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
  (* compute alias_map the same way as analyze_behavior, so write-inference sees array not arr *)
  let req_opt0, _ens_opt0, _var_opt0 = Block.extract_req_ens_var b.body in
  let pre_source0 =
    match kind with
    | C.FunctionContract -> req_opt0
    | C.LoopContract -> (match req_opt0 with Some r -> Some r | None -> Some b.assumes)
  in
  let alias_map =
    match pre_source0 with
    | None -> StringMap.empty
    | Some s -> Heap.collect_range_aliases s
  in
  let assumes_sl_for_writes = Desugar.desugar_sl ~alias_map b.assumes in

  let a = analyze_behavior ~kind ~spec_ret ~ptrs_choice b in
  build_core_behavior ~kind ~b_name ~assumes_sl_for_writes a

let sl_to_core (spec : Sl_ast.spec) : C.spec =
  let kind = SpecInfo.kind_of_spec spec in
  let names = SpecInfo.normalize_behavior_names spec.behaviors in

  let ptrs_choice =
    match spec.behaviors with
    | [] | [ _ ] -> LocalPerBehavior
    | _ -> GlobalShared (Ptrs.global_ptrs_of_spec spec)
  in

  let behaviors =
    List.map2
      (fun nm b -> behavior_of_sl ~kind ~spec_ret:spec.ret ~b_name:nm ~ptrs_choice b)
      names
      spec.behaviors
  in

  { C.kind = kind; params = []; behaviors }
