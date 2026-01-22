(* sl_to_core.ml *)

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
    (* Prevent nested LoopEntry printing like:
         \at(\at(array,LoopEntry)[\at(j,LoopEntry)],LoopEntry)
       Desired for old reads:
         \at(array[j],LoopEntry)
       So: for mem-ops whose OUTER phase is LoopEntry, translate operands in Post.
    *)
    let inner_phase_for_mem_op (ph : C.phase) : C.phase =
      match ph with
      | C.LoopEntry -> C.Post
      | _ -> ph
    in
    match e with
    | EVar x -> C.TVar (default_phase, x)
    | EConstInt n -> C.TInt n
    | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
    | EResult -> C.TResult
    | EApp (f, args) -> C.TApp (f, List.map (term_of_expr kind default_phase) args)
    | EUnop (UNeg, e1) -> C.TArith (C.Sub, C.TInt 0, term_of_expr kind default_phase e1)
    | EUnop (UNot, e1) -> C.TApp ("not", [ term_of_expr kind default_phase e1 ])
    | EDeref (EBinop (BAdd, base, idx)) ->
        let inner = inner_phase_for_mem_op default_phase in
        C.TIndex (default_phase, term_of_expr kind inner base, term_of_expr kind inner idx)

    (* IMPORTANT: plain pointer deref becomes heap-read, not a load of an address term *)
    | EDeref (EVar p) ->
        C.THeap (default_phase, p)

    | EDeref e1 ->
        let inner = inner_phase_for_mem_op default_phase in
        C.TLoad (default_phase, term_of_expr kind inner e1)

    | EOld e1 ->
        let ph =
          match kind with
          | C.FunctionContract -> C.Pre
          | C.LoopContract -> C.LoopEntry
        in
        term_of_expr kind ph e1
    | EPost e1 -> term_of_expr kind C.Post e1
    | EBinop (op, e1, e2) -> (
        match Op.arith_of_binop op with
        | Some aop -> C.TArith (aop, term_of_expr kind default_phase e1, term_of_expr kind default_phase e2)
        | None -> C.TApp ("binop", [ term_of_expr kind default_phase e1; term_of_expr kind default_phase e2 ]))
end

module Pred = struct
  let pred_of_cmp_expr (kind : C.spec_kind) (default_phase : C.phase) (e : Sl_ast.expr) : C.predicate =
    match e with
    | EBinop (op, e1, e2) -> (
        match Op.rel_of_binop op with
        | Some r -> Util.mk_rel r (Expr.term_of_expr kind default_phase e1) (Expr.term_of_expr kind default_phase e2)
        | None -> Util.p_atom (C.APred ("bool", [ Expr.term_of_expr kind default_phase e ])))
    | _ -> Util.p_atom (C.APred ("bool", [ Expr.term_of_expr kind default_phase e ]))

  let rec pred_of_sl_with_phase (kind : C.spec_kind) (default_phase : C.phase) (s : Sl_ast.sl) : C.predicate =
    match s with
    | STrue -> C.PTrue
    | SFalse -> C.PFalse
    | SEmp -> C.PTrue
    | SHeap _ -> C.PTrue
    | SPure e -> pred_of_cmp_expr kind default_phase e
    | SSep xs | SAnd xs -> Util.p_and (List.map (pred_of_sl_with_phase kind default_phase) xs)
    | SOr xs -> Util.p_or (List.map (pred_of_sl_with_phase kind default_phase) xs)
    | SNot x -> C.PNot (pred_of_sl_with_phase kind default_phase x)
    | SImplies (a, b) -> C.PImplies (pred_of_sl_with_phase kind default_phase a, pred_of_sl_with_phase kind default_phase b)
    | SForall (bs, body) -> C.PForall (Binder.binders_of_sl bs, pred_of_sl_with_phase kind default_phase body)
    | SExists (bs, body) -> C.PExists (Binder.binders_of_sl bs, pred_of_sl_with_phase kind default_phase body)

  let pred_of_sl (kind : C.spec_kind) (s : Sl_ast.sl) : C.predicate =
    pred_of_sl_with_phase kind C.Pre s
end

module Block = struct
  let extract_req_ens_var (body : Sl_ast.block) : Sl_ast.sl option * Sl_ast.sl option * Sl_ast.expr option =
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
      | SHeap (HPt { loc; ty; value; mode }) -> SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
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
      let rec map_expr ~(under_old : bool) (e : Sl_ast.expr) : Sl_ast.expr =
        match e with
        | EVar x -> (
            match StringMap.find_opt x pre_map with
            | None -> EVar x
            | Some p ->
                let deref = EDeref (EVar p) in
                (* value-vars (u,v,...) denote PRE-state values.
                  If we are already under an EOld, don’t wrap again. *)
                if under_old then deref else EOld deref)

        | EUnop (op, e1) -> EUnop (op, map_expr ~under_old e1)
        | EBinop (op, a, b) -> EBinop (op, map_expr ~under_old a, map_expr ~under_old b)
        | EApp (f, es) -> EApp (f, List.map (map_expr ~under_old) es)
        | EDeref e1 -> EDeref (map_expr ~under_old e1)

        | EOld e1 ->
            (* entering an old-context *)
            EOld (map_expr ~under_old:true e1)

        | EPost e1 ->
            (* post-context doesn’t change whether something is “already old” *)
            EPost (map_expr ~under_old e1)

        | (EConstInt _ | EConstBool _ | EResult) as x -> x
      in

      let rec map_sl (t : Sl_ast.sl) : Sl_ast.sl =
        match t with
        | (STrue | SFalse | SEmp) as x -> x
        | SPure e -> SPure (map_expr ~under_old:false e)

        | SHeap (HPt { loc; ty; value; mode }) ->
            SHeap (HPt { loc = map_expr ~under_old:false loc;
                        ty;
                        value = map_expr ~under_old:false value;
                        mode })

        | SHeap (HRange { loc; alias; ty; lo; hi; mode }) ->
            SHeap (HRange { loc = map_expr ~under_old:false loc;
                            alias;
                            ty;
                            lo = map_expr ~under_old:false lo;
                            hi = map_expr ~under_old:false hi;
                            mode })

        | SHeap (HPred (nm, args)) ->
            SHeap (HPred (nm, List.map (map_expr ~under_old:false) args))

        | SSep xs -> SSep (List.map map_sl xs)
        | SAnd xs -> SAnd (List.map map_sl xs)
        | SOr xs -> SOr (List.map map_sl xs)
        | SNot x -> SNot (map_sl x)
        | SImplies (a, b) -> SImplies (map_sl a, map_sl b)
        | SExists (bs, body) -> SExists (bs, map_sl body)
        | SForall (bs, body) -> SForall (bs, map_sl body)
      in
      map_sl s


  let rewrite_range_aliases (alias_map : string StringMap.t) (s : Sl_ast.sl) : Sl_ast.sl =
    let rec map_expr (e : Sl_ast.expr) : Sl_ast.expr =
      match e with
      | EVar a -> (
          match StringMap.find_opt a alias_map with
          | None -> EVar a
          | Some base -> EVar base)
      | EBinop (BAdd, EVar a, idx) -> (
          match StringMap.find_opt a alias_map with
          | None -> EBinop (BAdd, EVar a, map_expr idx)
          | Some base -> EBinop (BAdd, EVar base, map_expr idx))
      | EDeref (EVar a) -> (
          match StringMap.find_opt a alias_map with
          | None -> EDeref (EVar a)
          | Some base -> EDeref (EVar base))
      | EUnop (op, e1) -> EUnop (op, map_expr e1)
      | EBinop (op, a, b) -> EBinop (op, map_expr a, map_expr b)
      | EApp (f, es) -> EApp (f, List.map map_expr es)
      | EDeref e1 -> EDeref (map_expr e1)
      | EOld e1 -> EOld (map_expr e1)
      | EPost e1 -> EPost (map_expr e1)
      | x -> x
    in
    let rec map_sl (t : Sl_ast.sl) : Sl_ast.sl =
      match t with
      | (STrue | SFalse | SEmp) as x -> x
      | SPure e -> SPure (map_expr e)
      | SHeap (HPt { loc; ty; value; mode }) -> SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
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

  let union_alias_maps (a : string StringMap.t) (b : string StringMap.t) : string StringMap.t =
    StringMap.union (fun _ v _ -> Some v) a b

  let collect_range_aliases (s : Sl_ast.sl) : string StringMap.t =
    let real_bases : StringSet.t =
      let f_sl acc = function
        | SHeap (HPt { loc = EVar p; _ }) -> StringSet.add p acc
        | SHeap (HRange { loc = EVar p; _ }) -> StringSet.add p acc
        | _ -> acc
      in
      Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) StringSet.empty s
    in
    let add_mapping (k : string) (v : string) (acc : string StringMap.t) : string StringMap.t =
      if String.equal k v then acc else StringMap.add k v acc
    in
    let f_sl acc = function
      | SHeap (HRange { loc = EVar base; alias = Some a; _ }) ->
          let base_is_real = StringSet.mem base real_bases in
          let a_is_real = StringSet.mem a real_bases in
          if (not base_is_real) && a_is_real then add_mapping base a acc else add_mapping a base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) StringMap.empty s

  let expand_n_aliases (m : string StringMap.t) : string StringMap.t =
    StringMap.fold
      (fun alias base acc ->
        let acc = StringMap.add alias base acc in
        if String.length alias > 0 && alias.[0] = 'n' then acc else StringMap.add ("n" ^ alias) base acc)
      m
      StringMap.empty

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
    let base_of_loc (loc : Sl_ast.expr) : string option =
      match loc with
      | EVar p -> Some p
      | EBinop (BAdd, EVar p, _off) -> Some p
      | EOld (EVar p) -> Some p
      | EPost (EVar p) -> Some p
      | _ -> None
    in

    let take_last_two (xs : 'a list) : ('a * 'a) option =
      match List.rev xs with
      | hi :: lo :: _ -> Some (lo, hi)
      | _ -> None
    in

    let f_sl acc = function
      | SHeap (HRange { loc; lo; hi; mode; _ }) -> (
          match base_of_loc loc with
          | None -> acc
          | Some p -> { base = p; lo; hi; mode } :: acc)

      | SHeap (HPred (_nm, args)) -> (
          (* Robustly recognize array->int*(lo,hi) encodings:
            - [loc; lo; hi]
            - [loc; ...; lo; hi] (e.g. type in the middle)
          *)
          match args with
          | loc :: rest -> (
              match (base_of_loc loc, take_last_two rest) with
              | Some p, Some (lo, hi) ->
                  { base = p; lo; hi; mode = Sl_ast.Default } :: acc
              | _ -> acc)
          | _ -> acc)

      | _ -> acc
    in

    Traverse.fold_sl ~f_sl ~f_expr:(fun a _ -> a) [] s |> List.rev



  let ptrs_from_pt_atoms (atoms : pt_atom list) : StringSet.t =
    List.fold_left (fun acc ({ loc; value = _ } : pt_atom) -> StringSet.add loc acc) StringSet.empty atoms

  let pre_pairs_for_map (atoms : pt_atom list) : (string * string) list =
    List.map (fun { loc; value } -> (loc, value)) atoms
end

module Desugar = struct
  let desugar_expr ~(pre_alias : string StringMap.t) ~(post_alias : string StringMap.t) (e : Sl_ast.expr) : Sl_ast.expr
    =
    let wrap_old (d : Sl_ast.expr) = EOld d in
    let wrap_post (d : Sl_ast.expr) = EPost d in
    let rec go (e : Sl_ast.expr) : Sl_ast.expr =
      match e with
      | EDeref (EBinop (BAdd, EVar a, idx)) -> (
          match idx with
          | EBinop (BSub, p, EVar base2) when a = base2 -> go (EDeref p)
          | _ ->
              let idx' = go idx in
              match (StringMap.find_opt a pre_alias, StringMap.find_opt a post_alias) with
              | Some base, _ -> wrap_old (EDeref (EBinop (BAdd, EVar base, idx')))
              | None, Some base -> wrap_post (EDeref (EBinop (BAdd, EVar base, idx')))
              | None, None -> EDeref (EBinop (BAdd, EVar a, idx')))
      | EDeref (EVar a) -> (
          match (StringMap.find_opt a pre_alias, StringMap.find_opt a post_alias) with
          | Some base, _ -> wrap_old (EDeref (EVar base))
          | None, Some base -> wrap_post (EDeref (EVar base))
          | None, None -> EDeref (EVar a))
      | EUnop (op, e1) -> EUnop (op, go e1)
      | EBinop (op, a, b) -> EBinop (op, go a, go b)
      | EApp (f, es) -> EApp (f, List.map go es)
      | EDeref e1 -> EDeref (go e1)
      | EOld e1 -> EOld (go e1)
      | EPost e1 -> EPost (go e1)
      | x -> x
    in
    go e

  let desugar_sl ~(pre_alias : string StringMap.t) ~(post_alias : string StringMap.t) (s : Sl_ast.sl) : Sl_ast.sl =
    let map_expr = desugar_expr ~pre_alias ~post_alias in
    let rec map_sl = function
      | (STrue | SFalse | SEmp) as x -> x
      | SPure e -> SPure (map_expr e)
      | SHeap (HPt { loc; ty; value; mode }) -> SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode })
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

module Collect = struct
  let primed_scalar_vars (s : Sl_ast.sl) : StringSet.t =
    let f_expr (acc : StringSet.t) (e : Sl_ast.expr) : StringSet.t =
      match e with
      | EPost (EVar x) -> StringSet.add x acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let vars_in_expr (e : Sl_ast.expr) : StringSet.t =
    let f acc = function
      | EVar x -> StringSet.add x acc
      | _ -> acc
    in
    Traverse.fold_expr ~f StringSet.empty e

  let post_write_bases (s : Sl_ast.sl) : StringSet.t =
    let f_expr acc = function
      | EPost (EDeref (EBinop (BAdd, EVar base, _idx))) -> StringSet.add base acc
      | EPost (EDeref (EVar base)) -> StringSet.add base acc
      | EDeref (EBinop (BAdd, EPost (EVar base), _idx)) -> StringSet.add base acc
      | EDeref (EPost (EVar base)) -> StringSet.add base acc
      | _ -> acc
    in
    Traverse.fold_sl ~f_sl:(fun a _ -> a) ~f_expr StringSet.empty s

  let written_bases_from_ens_default_post (s : Sl_ast.sl) : StringSet.t =
    let rec collect_expr ~(protected : bool) (acc : StringSet.t) (e : Sl_ast.expr) : StringSet.t =
      match e with
      | EOld e1 -> collect_expr ~protected:true acc e1
      | EPost e1 -> collect_expr ~protected:false acc e1
      | EDeref (EBinop (BAdd, EVar base, idx)) ->
          let acc = if protected then acc else StringSet.add base acc in
          collect_expr ~protected acc idx
      | EDeref (EVar base) -> if protected then acc else StringSet.add base acc
      | EUnop (_op, e1) -> collect_expr ~protected acc e1
      | EBinop (_op, a, b) ->
          let acc = collect_expr ~protected acc a in
          collect_expr ~protected acc b
      | EApp (_f, es) -> List.fold_left (fun a x -> collect_expr ~protected a x) acc es
      | EDeref e1 -> collect_expr ~protected acc e1
      | EVar _ | EConstInt _ | EConstBool _ | EResult -> acc
    in
    let rec collect_sl (acc : StringSet.t) (t : Sl_ast.sl) : StringSet.t =
      match t with
      | STrue | SFalse | SEmp -> acc
      | SPure e -> collect_expr ~protected:false acc e
      | SHeap h -> (
          match h with
          | HPt { loc; value; _ } ->
              let acc = collect_expr ~protected:false acc loc in
              collect_expr ~protected:false acc value
          | HPred (_nm, args) -> List.fold_left (fun a x -> collect_expr ~protected:false a x) acc args
          | HRange { loc; lo; hi; _ } ->
              let acc = collect_expr ~protected:false acc loc in
              let acc = collect_expr ~protected:false acc lo in
              collect_expr ~protected:false acc hi)
      | SSep xs | SAnd xs | SOr xs -> List.fold_left collect_sl acc xs
      | SNot x -> collect_sl acc x
      | SImplies (a, b) ->
          let acc = collect_sl acc a in
          collect_sl acc b
      | SExists (_bs, body) | SForall (_bs, body) -> collect_sl acc body
    in
    collect_sl StringSet.empty s
end

module Build = struct
  let mk_valid (x : string) : C.predicate = Util.p_atom (C.APred ("valid", [ C.TPtr x ]))
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

  let progress_vars_from_variant (e : Sl_ast.expr) : StringSet.t =
    match e with
    | EVar v -> StringSet.singleton v
    | EBinop (BSub, _bound, EVar v) -> StringSet.singleton v
    | _ -> Collect.vars_in_expr e
end

module Ptrs = struct
  let ptrs_of_behavior (b : Sl_ast.behavior) : StringSet.t =
    let req_opt, ens_opt, _var_opt = Block.extract_req_ens_var b.body in
    let req_atoms = match req_opt with None -> [] | Some s -> Heap.collect_pt_atoms s in
    let ens_atoms = match ens_opt with None -> [] | Some s -> Heap.collect_pt_atoms s in
    let pure_eqs = match ens_opt with None -> [] | Some s -> Sugar.collect_heap_equalities_from_pure s in
    let pure_ptrs =
      List.fold_left (fun acc (a, bb) -> acc |> StringSet.add a |> StringSet.add bb) StringSet.empty pure_eqs
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
          List.concat_map (fun x -> match x with SSep ys -> flatten ys | _ -> [ x ]) xs
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
          let acc = List.fold_left (fun a y -> PairSet.add (canon_pair x y) a) acc tl in
          all_pairs acc tl
    in
    all_pairs PairSet.empty vs

  let neq_predicate_from_pairs (pairs : PairSet.t) : C.predicate =
    let ps = pairs |> PairSet.elements |> List.map (fun (a, b) -> Util.mk_rel C.Neq (C.TPtr a) (C.TPtr b)) in
    Util.p_and ps

  let infer_sep_neqs (req_sl : Sl_ast.sl) : C.predicate =
    let explicit = collect_explicit_neq_pairs req_sl in
    let sep_groups = collect_sep_loc_vars_in req_sl in
    let inferred =
      sep_groups |> List.fold_left (fun acc group -> PairSet.union acc (pairwise_neq_pairs group)) PairSet.empty
    in
    let inferred = PairSet.diff inferred explicit in
    neq_predicate_from_pairs inferred
end

module Ensures = struct
  let ensures_from_post_heaplets (kind : C.spec_kind) (post_atoms : Heap.pt_atom_any list) : C.predicate =
    post_atoms
    |> List.map (fun { Heap.loc = p; value_e } -> Util.mk_eq (C.THeap (C.Post, p)) (Expr.term_of_expr kind C.Post value_e))
    |> Util.p_and

  let ensures_from_pure_heap_eqs (eqs : (string * string) list) : C.predicate =
    eqs |> List.map (fun (a, b) -> Util.mk_eq (C.THeap (C.Post, a)) (C.THeap (C.Pre, b))) |> Util.p_and

  let build_ensures ~(kind : C.spec_kind) ~(post_sl : Sl_ast.sl) : C.predicate =
    let post_heap_atoms = Heap.collect_pt_atoms_any post_sl in
    let pure_heap_eqs = Sugar.collect_heap_equalities_from_pure post_sl in
    let heaplet_part = if post_heap_atoms <> [] then ensures_from_post_heaplets kind post_heap_atoms else C.PTrue in
    let pure_part = if pure_heap_eqs <> [] then ensures_from_pure_heap_eqs pure_heap_eqs else C.PTrue in
    let general_part =
      if post_heap_atoms = [] && pure_heap_eqs = [] then Pred.pred_of_sl_with_phase kind C.Post post_sl else C.PTrue
    in
    Util.p_and [ heaplet_part; pure_part; general_part ]
end

module SpecInfo = struct
  let kind_of_spec (spec : Sl_ast.spec) : C.spec_kind =
    let has_variant_clause (b : Sl_ast.behavior) =
      let _req, _ens, var = Block.extract_req_ens_var b.body in
      Option.is_some var
    in
    if List.exists has_variant_clause spec.behaviors then C.LoopContract else C.FunctionContract

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

  let pre_source0 = req_opt0 in
  let pre_alias_map =
    match pre_source0 with None -> StringMap.empty | Some s -> Heap.collect_range_aliases s
  in
  let post_alias_map =
    match ens_opt0 with None -> StringMap.empty | Some s -> Heap.collect_range_aliases s
  in

  let alias_from_req = match req_opt0 with None -> StringMap.empty | Some s -> Heap.collect_range_aliases s in
  let alias_from_ens = match ens_opt0 with None -> StringMap.empty | Some s -> Heap.collect_range_aliases s in
  let alias_from_assm = Heap.collect_range_aliases b.assumes in
  let alias_map_raw = Heap.union_alias_maps alias_from_req (Heap.union_alias_maps alias_from_ens alias_from_assm) in
  let alias_map = Heap.expand_n_aliases alias_map_raw in
  let norm_sl = Rewrite.rewrite_range_aliases alias_map in

  let req_opt =
    req_opt0
    |> Option.map (Desugar.desugar_sl ~pre_alias:pre_alias_map ~post_alias:post_alias_map)
    |> Option.map norm_sl
  in
  let ens_opt =
    ens_opt0
    |> Option.map (Desugar.desugar_sl ~pre_alias:pre_alias_map ~post_alias:post_alias_map)
    |> Option.map norm_sl
  in
  let assumes_desugared =
    b.assumes
    |> Desugar.desugar_sl ~pre_alias:pre_alias_map ~post_alias:post_alias_map
    |> norm_sl
  in

  (* ------------------------------------------------------------ *)
  (* IMPORTANT: choose a “heap/range source” robustly.             *)
  (* In some ASTs, the heap-range predicate ends up in `assumes`.  *)
  (* ------------------------------------------------------------ *)
  let heap_src_sl : Sl_ast.sl option =
    match req_opt with
    | Some s when Heap.collect_range_atoms s <> [] || Heap.collect_pt_atoms s <> [] -> Some s
    | _ ->
        let has_heap =
          (Heap.collect_range_atoms assumes_desugared <> []) || (Heap.collect_pt_atoms assumes_desugared <> [])
        in
        if has_heap then Some assumes_desugared else req_opt
  in

  let pre_atoms = match heap_src_sl with None -> [] | Some s -> Heap.collect_pt_atoms s in
  let pre_pairs = Heap.pre_pairs_for_map pre_atoms in
  let pre_map = Rewrite.pre_value_to_loc_map pre_pairs in
  let req_ranges = match heap_src_sl with None -> [] | Some s -> Heap.collect_range_atoms s in

  let assumes_sl_raw = assumes_desugared in
  let assumes_sl = Rewrite.rewrite_value_vars_with_pre_map pre_map assumes_sl_raw in
  let assumes_p = Pred.pred_of_sl kind assumes_sl in

  let req_sep_neqs =
    match req_opt with
    | None -> C.PTrue
    | Some req_sl -> SepNeq.infer_sep_neqs req_sl
  in

  (* FIX: req_pure source for loop invariants
     If the parser placed the "req ..." content into b.assumes (and body has no CReq),
     then req_opt=None and we'd otherwise lose all the pure invariants (like forall).
     For LoopContract, fall back to assumes_desugared as the "req/pure" source. *)
  let req_pure =
    let pure_src_opt : Sl_ast.sl option =
      match req_opt with
      | Some s -> Some s
      | None ->
          (match kind with
          | C.LoopContract -> Some assumes_desugared
          | C.FunctionContract -> None)
    in
    match pure_src_opt with
    | None -> C.PTrue
    | Some pure_src ->
        let pure_src' = Rewrite.rewrite_value_vars_with_pre_map pre_map pure_src in
        let phase =
          match kind with
          | C.FunctionContract -> C.Pre
          | C.LoopContract -> C.Post
        in
        Pred.pred_of_sl_with_phase kind phase pure_src'
  in

  let post_sl_opt =
    match ens_opt with
    | None -> None
    | Some post0 ->
        let post1 = match spec_ret with None -> post0 | Some r -> Rewrite.rewrite_result r post0 in
        let post1 = post1 |> Desugar.desugar_sl ~pre_alias:pre_alias_map ~post_alias:post_alias_map |> norm_sl in
        let post2 = Rewrite.rewrite_value_vars_with_pre_map pre_map post1 in
        Some post2
  in

  let ensures_p =
    match post_sl_opt with
    | None -> C.PTrue
    | Some post_sl -> Ensures.build_ensures ~kind ~post_sl
  in

  let ptrs =
    match ptrs_choice with
    | GlobalShared g -> g
    | LocalPerBehavior ->
        let body' =
          (match req_opt with None -> [] | Some s -> [ CReq s ])
          @ (match ens_opt with None -> [] | Some s -> [ CEns s ])
          @ [ CVar var_opt ]
        in
        let b' = { b with assumes = assumes_desugared; body = body' } in
        Ptrs.ptrs_of_behavior b'
  in

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



module Loop_contract = struct
  let cur_phase : C.phase = C.Post

  let scalar_accumulator_invariants
      ~(post_sl_opt : Sl_ast.sl option)
      ~(var_expr : Sl_ast.expr option)
    : C.predicate list
    =
    let pvars =
      match var_expr with
      | None -> StringSet.empty
      | Some v -> Build.progress_vars_from_variant v
    in
    match StringSet.elements pvars with
    | [ i ] -> (
        let rec collect_eqs (s : Sl_ast.sl) : (Sl_ast.expr * Sl_ast.expr) list =
          match s with
          | SPure (EBinop (BEq, lhs, rhs)) -> [ (lhs, rhs) ]
          | SAnd xs | SSep xs -> List.concat_map collect_eqs xs
          | SOr xs -> List.concat_map collect_eqs xs
          | SNot x -> collect_eqs x
          | SImplies (a, b) -> collect_eqs a @ collect_eqs b
          | SForall (_, body) | SExists (_, body) -> collect_eqs body
          | _ -> []
        in

        let is_evar x = function EVar y when y = x -> true | _ -> false in
        let is_epost_evar x = function EPost (EVar y) when y = x -> true | _ -> false in

        let mk_inv (x : string) : C.predicate =
          let x_cur = C.TVar (C.Post, x) in
          let x_le  = C.TVar (C.LoopEntry, x) in
          let i_cur = C.TVar (C.Post, i) in
          let i_le  = C.TVar (C.LoopEntry, i) in
          Util.mk_eq x_cur (C.TArith (C.Add, x_le, C.TArith (C.Sub, i_cur, i_le)))
        in

        match post_sl_opt with
        | None -> []
        | Some post_sl ->
            collect_eqs post_sl
            |> List.filter_map (fun (lhs, rhs) ->
                 match lhs with
                 | EPost (EVar x) -> (
                     (* rhs must be: x + (i' - i) *)
                     match rhs with
                     | EBinop (BAdd, e_x, EBinop (BSub, e_ip, e_i)) ->
                         if is_evar x e_x && is_epost_evar i e_ip && is_evar i e_i
                         then Some (mk_inv x)
                         else None
                     | _ -> None)
                 | _ -> None))
    | _ -> []


  let base_invariants
      ~(req_sep_neqs : C.predicate)
      ~(ptrs : StringSet.t)
      ~(req_ranges : Heap.range_atom list)
      ~(req_pure : C.predicate)
    : C.predicate list
    =
    ignore ptrs;
    let range_bounds : C.predicate list =
      req_ranges
      |> List.filter_map (fun (r : Heap.range_atom) ->
            match r.lo with
            | EVar i ->
                let i_cur = C.TVar (C.Post, i) in
                let zero = C.TInt 0 in
                let hi_t = Expr.term_of_expr C.LoopContract C.Post r.hi in
                let hi_plus_1 = C.TArith (C.Add, hi_t, C.TInt 1) in
                Some
                  [
                    Util.mk_rel C.Lte zero i_cur;
                    Util.mk_rel C.Lte i_cur hi_plus_1;
                  ]
            | _ -> None)
      |> List.concat
    in
    let global = Util.p_and [ req_sep_neqs; req_pure ] in
    global :: range_bounds

  let variant_clause (vopt : Sl_ast.expr option) : C.clause list =
    match vopt with
    | None -> []
    | Some e -> [ C.Variant (Expr.term_of_expr C.LoopContract cur_phase e) ]
  
  let writes_base_in_post (base : string) (p : C.predicate) : bool =
    let rec term_mentions_base = function
      | C.TIndex (_, C.TVar (_, b), _) when b = base -> true
      | C.THeap (_, b) when b = base -> true
      | C.TArith (_, a, b) -> term_mentions_base a || term_mentions_base b
      | C.TApp (_, ts) -> List.exists term_mentions_base ts
      | _ -> false
    in
    let rec pred = function
      | C.PAtom (C.ARel (_, t1, t2)) ->
          term_mentions_base t1 || term_mentions_base t2
      | C.PImplies (_, q) -> pred q
      | C.PForall (_, q) -> pred q
      | C.PAnd ps | C.POr ps -> List.exists pred ps
      | _ -> false
    in
    pred p


  let assigns_clause
      ~(req_ranges : Heap.range_atom list)
      ~(post_sl_opt : Sl_ast.sl option)
      ~(var_expr : Sl_ast.expr option)
    : C.clause
    =
    let progress_vars =
      match var_expr with
      | None -> StringSet.empty
      | Some v -> Build.progress_vars_from_variant v
    in

    (* NEW: also assign any primed scalar vars appearing in the postcondition *)
    let primed_scalars =
      match post_sl_opt with
      | None -> StringSet.empty
      | Some post_sl -> Collect.primed_scalar_vars post_sl
    in

    let all_scalar_writes = StringSet.union progress_vars primed_scalars in
    let scalar_assigns =
      all_scalar_writes
      |> StringSet.elements
      |> List.map (fun x -> C.AsVar x)
    in

    let written_bases =
      match post_sl_opt with
      | None -> StringSet.empty
      | Some post_sl -> Collect.post_write_bases post_sl
    in

    let range_assigns =
      req_ranges
      |> List.filter (fun (r : Heap.range_atom) ->
          match r.mode with
          | Sl_ast.In -> false
          | Sl_ast.Default ->
              StringSet.mem r.base written_bases
              ||
              writes_base_in_post r.base
                (match post_sl_opt with
                | None -> C.PTrue
                | Some post_sl -> Ensures.build_ensures ~kind:C.LoopContract ~post_sl))
      |> List.map (fun (r : Heap.range_atom) ->
          let lo_term =
            match (StringSet.elements progress_vars, r.lo) with
            | [ i ], EVar x when x = i -> C.TVar (C.LoopEntry, i)
            | _ -> Expr.term_of_expr C.LoopContract C.Post r.lo
          in
          let hi_term = Expr.term_of_expr C.LoopContract C.Post r.hi in
          C.AsRange (r.base, lo_term, hi_term))
    in

    C.Assigns (scalar_assigns @ range_assigns)


  let unchanged_suffix_invariants
      ~(req_ranges : Heap.range_atom list)
      ~(var_expr : Sl_ast.expr option)
    : C.predicate list
    =
    let pvars =
      match var_expr with
      | None -> StringSet.empty
      | Some v -> Build.progress_vars_from_variant v
    in
    match (StringSet.elements pvars, req_ranges) with
    | [ i ], ({ Heap.base; hi; _ } : Heap.range_atom) :: _ ->
        let j_b = { C.b_name = "j"; b_ty = Some "size_t" } in
        let j = C.TVar (cur_phase, "j") in
        let i_cur = C.TVar (cur_phase, i) in
        let hi_t = Expr.term_of_expr C.LoopContract cur_phase hi in
        let hi_plus_1 = C.TArith (C.Add, hi_t, C.TInt 1) in

        let idx_cur = C.TIndex (cur_phase, C.TVar (cur_phase, base), j) in
        let idx_le  = C.TIndex (C.LoopEntry, C.TVar (cur_phase, base), j) in


        let guard = Util.p_and [ Util.mk_rel C.Lte i_cur j; Util.mk_rel C.Lt j hi_plus_1 ] in
        let body = Util.mk_eq idx_cur idx_le in
        [ C.PForall ([ j_b ], C.PImplies (guard, body)) ]
    | _ -> []

  let processed_prefix_invariants ~(ensures_p : C.predicate) ~(var_expr : Sl_ast.expr option) : C.predicate list =
    let pvars =
      match var_expr with
      | None -> StringSet.empty
      | Some v -> Build.progress_vars_from_variant v
    in
    match StringSet.elements pvars with
    | [ i ] ->
        let rec split_and = function
          | C.PAnd ps -> List.concat_map split_and ps
          | p -> [ p ]
        in
        let and_of ps = Util.p_and ps in

        let rewrite_guard_for_prefix ~(jname : string) (g : C.predicate) : C.predicate option =
          let cs = split_and g in
          let has_lower = ref false in
          let has_upper = ref false in

          let is_j_var (t : C.term) : bool =
            match t with
            | C.TVar (_, x) when x = jname -> true
            | _ -> false
          in
          let is_i_cur (t : C.term) : bool =
            match t with
            | C.TVar (C.Post, x) when x = i -> true
            | _ -> false
          in

          let term_mentions_j (t : C.term) : bool =
            let rec go = function
              | C.TVar (_, x) -> x = jname
              | C.TArith (_, a, b) -> go a || go b
              | C.TApp (_, args) -> List.exists go args
              | C.TIndex (_, a, b) -> go a || go b
              | C.TLoad (_, a) -> go a
              | C.THeap _ | C.TPtr _ | C.TInt _ | C.TResult -> false
            in
            go t
          in

          let is_lower_conj (p : C.predicate) : bool =
            match p with
            | C.PAtom (C.ARel (C.Lte, t1, t2))
            | C.PAtom (C.ARel (C.Lt, t1, t2)) ->
                is_i_cur t1 && is_j_var t2
            | _ -> false
          in

          let is_upper_conj (p : C.predicate) : bool =
            match p with
            | C.PAtom (C.ARel (C.Lt, t1, t2))
            | C.PAtom (C.ARel (C.Lte, t1, t2)) ->
                is_j_var t1 && not (term_mentions_j t2)
            | _ -> false
          in

          let kept =
            List.filter
              (fun c ->
                if is_lower_conj c then (has_lower := true; false)
                else if is_upper_conj c then (has_upper := true; false)
                else true)
              cs
          in

          if (not !has_lower) || not !has_upper then None
          else
            let j = C.TVar (C.Post, jname) in
            let lower' = Util.mk_rel C.Lte (C.TVar (C.LoopEntry, i)) j in
            let upper' = Util.mk_rel C.Lt j (C.TVar (C.Post, i)) in
            Some (and_of (lower' :: upper' :: kept))
        in

        let rec collect (p : C.predicate) : C.predicate list =
          match p with
          | C.PAnd ps -> List.concat_map collect ps
          | C.PForall (bs, body) -> (
              match bs with
              | [ ({ C.b_name = jname; _ } as jb) ] -> (
                  match body with
                  | C.PImplies (g, concl) -> (
                      match rewrite_guard_for_prefix ~jname g with
                      | None -> []
                      | Some g' -> [ C.PForall ([ jb ], C.PImplies (g', concl)) ])
                  | _ -> [])
              | _ -> [])
          | _ -> []
        in
        collect ensures_p
    | _ -> []

  let progress_invariants
      ~(req_ranges : Heap.range_atom list)
      ~(var_expr : Sl_ast.expr option)
    : C.predicate list
    =
    match var_expr with
    | None -> []
    | Some v ->
        if req_ranges = [] then []
        else
          let pvars = Build.progress_vars_from_variant v in
          match StringSet.elements pvars with
          | [ i ] ->
              let i_le = C.TVar (C.LoopEntry, i) in
              let i_cur = C.TVar (C.Post, i) in
              [ Util.mk_rel C.Lte i_le i_cur ]
          | _ -> []




  let build_invariants
      ~(req_sep_neqs : C.predicate)
      ~(req_pure : C.predicate)
      ~(ptrs : StringSet.t)
      ~(req_ranges : Heap.range_atom list)
      ~(req_sl_opt : Sl_ast.sl option)
      ~(ensures_p : C.predicate)
      ~(post_sl_opt : Sl_ast.sl option)
      ~(var_expr : Sl_ast.expr option)
    : C.predicate list
    =
    ignore req_sl_opt;

    let base = base_invariants ~req_sep_neqs ~req_pure ~ptrs ~req_ranges in
    let prog = progress_invariants ~req_ranges ~var_expr in
    let suffix = unchanged_suffix_invariants ~req_ranges ~var_expr in
    let prefix = processed_prefix_invariants ~ensures_p ~var_expr in

    (* NEW: scalar accumulator invariants like b == at(b,LE) + (i - at(i,LE)) *)
    let scalar = scalar_accumulator_invariants ~post_sl_opt ~var_expr in

    base @ prog @ suffix @ prefix @ scalar


end

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
    ~(post_sl_opt : Sl_ast.sl option)
  : C.clause
  =
  let written_bases =
    match post_sl_opt with
    | None -> StringSet.empty
    | Some post_sl -> Collect.post_write_bases post_sl
  in
  let range_assigns =
    req_ranges
    |> List.filter (fun r -> StringSet.mem r.Heap.base written_bases)
    |> List.map (fun r -> C.AsRange (r.Heap.base, Expr.term_of_expr kind C.Pre r.Heap.lo, Expr.term_of_expr kind C.Pre r.Heap.hi))
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
    ptrs
    |> StringSet.elements
    |> List.filter (fun p -> not (StringSet.mem p range_bases))
    |> List.map (fun p -> C.AsHeap p)
  in
  C.Assigns (range_assigns @ heap_assigns)

let build_core_behavior ~(kind : C.spec_kind) ~(b_name : string option) (a : beh_analysis) : C.behavior =
  match kind with
  | C.FunctionContract ->
      let clauses =
        [
          C.Assumes a.assumes_p;
          mk_requires ~kind ~ptrs:a.ptrs ~ranges:a.req_ranges ~sep_neqs:a.req_sep_neqs ~pure:a.req_pure;
          C.Ensures a.ensures_p;
          mk_assigns ~kind ~ptrs:a.ptrs ~req_ranges:a.req_ranges ~post_sl_opt:a.post_sl_opt;
        ]
        @ (match a.var_expr with None -> [] | Some v -> [ C.Variant (Expr.term_of_expr kind C.Pre v) ])
      in
      { C.b_name; clauses }
  | C.LoopContract ->
      let invs =
        Loop_contract.build_invariants
          ~req_sep_neqs:a.req_sep_neqs
          ~req_pure:a.req_pure
          ~ptrs:a.ptrs
          ~req_ranges:a.req_ranges
          ~req_sl_opt:a.req_sl
          ~ensures_p:a.ensures_p
          ~post_sl_opt:a.post_sl_opt
          ~var_expr:a.var_expr
      in

      let inv_clauses = List.map (fun p -> C.Assumes p) invs in
      let ensures_clause = C.Ensures a.ensures_p in
      let assigns =
        Loop_contract.assigns_clause
          ~req_ranges:a.req_ranges
          ~post_sl_opt:a.post_sl_opt
          ~var_expr:a.var_expr
      in
      let variant = Loop_contract.variant_clause a.var_expr in
      { C.b_name; clauses = inv_clauses @ [ ensures_clause; assigns ] @ variant }


let behavior_of_sl
    ~(kind : C.spec_kind)
    ~(spec_ret : string option)
    ~(b_name : string option)
    ~(ptrs_choice : ptrs_choice)
    (b : Sl_ast.behavior)
  : C.behavior
  =
  let a = analyze_behavior ~kind ~spec_ret ~ptrs_choice b in
  build_core_behavior ~kind ~b_name a

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
