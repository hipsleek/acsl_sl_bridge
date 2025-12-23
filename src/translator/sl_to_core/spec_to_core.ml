(* spec_to_core.ml *)

open Sl_ast
module C = Core

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* ---------- Predicate helpers ---------- *)

let p_and (ps : C.predicate list) : C.predicate =
  let ps = ps |> List.filter (fun p -> p <> C.PTrue) in
  match ps with
  | [] -> C.PTrue
  | [ p ] -> p
  | _ -> C.PAnd ps

let p_or (ps : C.predicate list) : C.predicate =
  let ps = ps |> List.filter (fun p -> p <> C.PFalse) in
  match ps with
  | [] -> C.PFalse
  | [ p ] -> p
  | _ -> C.POr ps

let p_atom (a : C.atom) : C.predicate = C.PAtom a

let mk_valid (x : string) : C.predicate =
  p_atom (C.APred ("valid", [ C.TPtr x ]))

let mk_valid_read_range (base : C.term) (lo : C.term) (hi : C.term) : C.predicate =
  p_atom (C.APred ("valid_read_range", [ base; lo; hi ]))

let mk_eq (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (C.Eq, t1, t2))

let mk_rel (r : C.rel) (t1 : C.term) (t2 : C.term) : C.predicate =
  p_atom (C.ARel (r, t1, t2))

(* ---------- Operators ---------- *)

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

(* ---------- Expr -> Core.term ---------- *)

let rec term_of_expr (default_phase : C.phase) (e : Sl_ast.expr) : C.term =
  match e with
  | EVar x -> C.TVar (default_phase, x)
  | EConstInt n -> C.TInt n
  | EConstBool b -> C.TApp ((if b then "true" else "false"), [])
  | EResult -> C.TResult
  | EUnop (_op, e1) ->
      C.TApp ("unop", [ term_of_expr default_phase e1 ])
  | EApp (f, args) ->
      C.TApp (f, List.map (term_of_expr default_phase) args)

  (* *(base + idx) becomes Index(base, idx) (for array-like terms) *)
  | EDeref (EBinop (BAdd, base, idx)) ->
      C.TIndex
        ( default_phase
        , term_of_expr default_phase base
        , term_of_expr default_phase idx )

  (* *addr becomes Load(addr) *)
  | EDeref e1 ->
      C.TLoad (default_phase, term_of_expr default_phase e1)

  (* old(e) means phase Pre *)
  | EOld e1 ->
      term_of_expr C.Pre e1

  (* post(e) means phase Post *)
  | EPost e1 ->
      term_of_expr C.Post e1

  | EBinop (op, e1, e2) -> (
      match arith_of_binop op with
      | Some aop ->
          C.TArith
            ( aop
            , term_of_expr default_phase e1
            , term_of_expr default_phase e2 )
      | None ->
          C.TApp
            ( "binop"
            , [ term_of_expr default_phase e1
              ; term_of_expr default_phase e2 ] )
    )

(* ---------- Expr -> Core.predicate (boolean) ---------- *)

let pred_of_cmp_expr (default_phase : C.phase) (e : Sl_ast.expr) : C.predicate =
  match e with
  | EBinop (op, e1, e2) -> (
      match rel_of_binop op with
      | Some r ->
          mk_rel r (term_of_expr default_phase e1) (term_of_expr default_phase e2)
      | None ->
          p_atom (C.APred ("bool", [ term_of_expr default_phase e ]))
    )
  | _ ->
      p_atom (C.APred ("bool", [ term_of_expr default_phase e ]))

(* ---------- Sorts ---------- *)

let core_ty_of_sort_opt (s : Sl_ast.sort option) : string option =
  match s with
  | None -> None
  | Some SInt -> Some "int"
  | Some SBool -> Some "bool"
  | Some SPtr -> None
  | Some (SUser s) -> Some s

(* ---------- SL -> Core.predicate (pure-ish view) ---------- *)

let rec pred_of_sl (s : Sl_ast.sl) : C.predicate =
  match s with
  | STrue -> C.PTrue
  | SFalse -> C.PFalse
  | SEmp -> C.PTrue
  | SHeap _ -> C.PTrue
  | SPure e -> pred_of_cmp_expr C.Pre e
  | SSep xs -> p_and (List.map pred_of_sl xs)
  | SAnd xs -> p_and (List.map pred_of_sl xs)
  | SOr xs -> p_or (List.map pred_of_sl xs)
  | SNot x -> C.PNot (pred_of_sl x)
  | SImplies (a, b) -> C.PImplies (pred_of_sl a, pred_of_sl b)
  | SForall (binders, body) ->
      let bs =
        binders
        |> List.map (fun (nm, tyopt) ->
               { C.b_name = nm; b_ty = core_ty_of_sort_opt tyopt })
      in
      C.PForall (bs, pred_of_sl body)
  | SExists (binders, body) ->
      let bs =
        binders
        |> List.map (fun (nm, tyopt) ->
               { C.b_name = nm; b_ty = core_ty_of_sort_opt tyopt })
      in
      C.PExists (bs, pred_of_sl body)

(* ---------- Heaplet collection (existing points-to support) ---------- *)

type pt_atom = { loc : string; value : string }

let rec collect_pt_atoms (s : Sl_ast.sl) : pt_atom list =
  match s with
  | SHeap (HPt { loc = EVar p; value = EVar v; _ }) ->
      [ { loc = p; value = v } ]
  | SSep xs | SAnd xs | SOr xs ->
      List.concat_map collect_pt_atoms xs
  | SImplies (a, b) ->
      collect_pt_atoms a @ collect_pt_atoms b
  | SNot x ->
      collect_pt_atoms x
  | SExists (_, body) | SForall (_, body) ->
      collect_pt_atoms body
  | _ ->
      []

(* ---------- NEW: collect read-only array ranges from req ---------- *)

type range_atom = { base : string; lo : Sl_ast.expr; hi : Sl_ast.expr }

let rec collect_range_atoms (s : Sl_ast.sl) : range_atom list =
  match s with
  | SHeap (HRange { loc = EVar p; lo; hi; _ }) ->
      [ { base = p; lo; hi } ]
  | SSep xs | SAnd xs | SOr xs ->
      List.concat_map collect_range_atoms xs
  | SImplies (a, b) ->
      collect_range_atoms a @ collect_range_atoms b
  | SNot x ->
      collect_range_atoms x
  | SExists (_, body) | SForall (_, body) ->
      collect_range_atoms body
  | _ ->
      []

(* ---------- Heap equalities (existing pure patterns) ---------- *)

let rec collect_heap_equalities_from_pure (s : Sl_ast.sl) : (string * string) list =
  let go_expr (e : Sl_ast.expr) : (string * string) option =
    match e with
    | EBinop (BEq, lhs, rhs) -> (
        match (lhs, rhs) with
        | (EPost (EDeref (EVar a)), EDeref (EVar b)) -> Some (a, b)
        | (EDeref (EVar b), EPost (EDeref (EVar a))) -> Some (a, b)
        | (EDeref (EVar a), EOld (EDeref (EVar b))) -> Some (a, b)
        | (EOld (EDeref (EVar b)), EDeref (EVar a)) -> Some (a, b)
        | (EPost (EDeref (EVar a)), EOld (EDeref (EVar b))) -> Some (a, b)
        | (EOld (EDeref (EVar b)), EPost (EDeref (EVar a))) -> Some (a, b)
        | _ -> None
      )
    | _ -> None
  in
  match s with
  | SPure e ->
      (match go_expr e with None -> [] | Some x -> [ x ])
  | SAnd xs | SSep xs | SOr xs ->
      List.concat_map collect_heap_equalities_from_pure xs
  | SImplies (a, b) ->
      collect_heap_equalities_from_pure a @ collect_heap_equalities_from_pure b
  | SNot x ->
      collect_heap_equalities_from_pure x
  | SExists (_, body) | SForall (_, body) ->
      collect_heap_equalities_from_pure body
  | _ ->
      []

(* ---------- Requires/Assigns from pointers (existing behavior) ---------- *)

let ptrs_from_atoms (atoms : pt_atom list) : StringSet.t =
  List.fold_left
    (fun acc { loc; value = _ } -> StringSet.add loc acc)
    StringSet.empty
    atoms

let assigns_from_ptrs (ptrs : StringSet.t) : C.assignable list =
  ptrs |> StringSet.elements |> List.map (fun p -> C.AsHeap p)

let requires_from_ptrs (ptrs : StringSet.t) : C.predicate =
  ptrs |> StringSet.elements |> List.map mk_valid |> p_and

(* ---------- NEW: Requires from read-only ranges ---------- *)

let requires_from_ranges (ranges : range_atom list) : C.predicate =
  ranges
  |> List.map (fun { base; lo; hi } ->
         mk_valid_read_range
           (C.TVar (C.Pre, base))
           (term_of_expr C.Pre lo)
           (term_of_expr C.Pre hi))
  |> p_and

(* ---------- Ensures generation (existing behavior) ---------- *)

let pre_value_to_loc_map (pre_atoms : pt_atom list) : string StringMap.t =
  List.fold_left
    (fun acc { loc; value } -> StringMap.add value loc acc)
    StringMap.empty
    pre_atoms

let ensures_from_heaplets
    ~(pre_map : string StringMap.t)
    ~(post_atoms : pt_atom list)
  : C.predicate
  =
  let eqs =
    post_atoms
    |> List.filter_map (fun { loc = a; value = v } ->
           match StringMap.find_opt v pre_map with
           | Some pre_loc ->
               Some (mk_eq (C.THeap (C.Post, a)) (C.THeap (C.Pre, pre_loc)))
           | None -> None)
  in
  p_and eqs

let ensures_from_pure_heap_eqs (eqs : (string * string) list) : C.predicate =
  eqs
  |> List.map (fun (a, b) -> mk_eq (C.THeap (C.Post, a)) (C.THeap (C.Pre, b)))
  |> p_and

let ensures_from_sl_pred (s : Sl_ast.sl) : C.predicate =
  pred_of_sl s

let build_ensures ~(pre_map : string StringMap.t) ~(post_sl : Sl_ast.sl) : C.predicate =
  let post_heap_atoms = collect_pt_atoms post_sl in
  let pure_heap_eqs = collect_heap_equalities_from_pure post_sl in

  let heaplet_part =
    if post_heap_atoms <> [] then
      ensures_from_heaplets ~pre_map ~post_atoms:post_heap_atoms
    else
      C.PTrue
  in
  let pure_part =
    if pure_heap_eqs <> [] then
      ensures_from_pure_heap_eqs pure_heap_eqs
    else
      C.PTrue
  in

  let need_general = (post_heap_atoms = []) && (pure_heap_eqs = []) in
  let general_part =
    if need_general then
      ensures_from_sl_pred post_sl
    else
      C.PTrue
  in

  p_and [ heaplet_part; pure_part; general_part ]

(* ---------- Rewrite named return into TResult ---------- *)

let rewrite_result (ret : string) (s : Sl_ast.sl) : Sl_ast.sl =
  let re (e : Sl_ast.expr) : Sl_ast.expr =
    let rec go = function
      | EVar x when x = ret -> EResult
      | EUnop (op, e1) -> EUnop (op, go e1)
      | EBinop (op, e1, e2) -> EBinop (op, go e1, go e2)
      | EApp (f, es) -> EApp (f, List.map go es)
      | EDeref e1 -> EDeref (go e1)
      | EOld e1 -> EOld (go e1)
      | EPost e1 -> EPost (go e1)
      | x -> x
    in
    go e
  in
  let rec gs = function
    | STrue | SFalse | SEmp as x -> x
    | SHeap h -> SHeap h
    | SPure e -> SPure (re e)
    | SSep xs -> SSep (List.map gs xs)
    | SAnd xs -> SAnd (List.map gs xs)
    | SOr xs -> SOr (List.map gs xs)
    | SNot x -> SNot (gs x)
    | SImplies (a, b) -> SImplies (gs a, gs b)
    | SExists (bs, body) -> SExists (bs, gs body)
    | SForall (bs, body) -> SForall (bs, gs body)
  in
  gs s

(* ---------- Clause extraction ---------- *)

let extract_req_ens_var (body : Sl_ast.block) :
    Sl_ast.sl option * Sl_ast.sl option * Sl_ast.expr option =
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

(* ---------- Loop assigns inference (existing behavior) ---------- *)

let rec collect_post_vars_in_expr (e : Sl_ast.expr) : StringSet.t =
  match e with
  | EPost (EVar x) -> StringSet.singleton x
  | EPost e1 -> collect_post_vars_in_expr e1
  | EBinop (_op, a, b) ->
      StringSet.union (collect_post_vars_in_expr a) (collect_post_vars_in_expr b)
  | EUnop (_op, e1) ->
      collect_post_vars_in_expr e1
  | EApp (_f, es) ->
      List.fold_left
        (fun acc x -> StringSet.union acc (collect_post_vars_in_expr x))
        StringSet.empty
        es
  | EDeref e1 -> collect_post_vars_in_expr e1
  | EOld e1 -> collect_post_vars_in_expr e1
  | _ -> StringSet.empty

let rec collect_post_vars_in_sl (s : Sl_ast.sl) : StringSet.t =
  match s with
  | SPure e -> collect_post_vars_in_expr e
  | SAnd xs | SSep xs | SOr xs ->
      List.fold_left
        (fun acc x -> StringSet.union acc (collect_post_vars_in_sl x))
        StringSet.empty
        xs
  | SImplies (a, b) ->
      StringSet.union (collect_post_vars_in_sl a) (collect_post_vars_in_sl b)
  | SNot x -> collect_post_vars_in_sl x
  | SExists (_, body) | SForall (_, body) -> collect_post_vars_in_sl body
  | _ -> StringSet.empty

let assigns_from_post_vars (post_sl : Sl_ast.sl) : C.assignable list =
  post_sl
  |> collect_post_vars_in_sl
  |> StringSet.elements
  |> List.map (fun v -> C.AsVar v)

(* ---------- Kind and behavior naming ---------- *)

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

(* ---------- Pointer discovery for existing valid/assigns ---------- *)

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
  let heap_ptrs = ptrs_from_atoms (req_atoms @ ens_atoms) in
  StringSet.union heap_ptrs pure_ptrs

let global_ptrs_of_spec (spec : Sl_ast.spec) : StringSet.t =
  List.fold_left
    (fun acc b -> StringSet.union acc (ptrs_of_behavior b))
    StringSet.empty
    spec.behaviors

(* ---------- Behavior translation ---------- *)

let core_behavior_of_sl
    ~(kind : C.spec_kind)
    ~(spec_ret : string option)
    ~(b_name : string option)
    ~(global_ptrs : StringSet.t option)
    (b : Sl_ast.behavior)
  : C.behavior =
  let (req_opt, ens_opt, var_opt) = extract_req_ens_var b.body in

  let pre_atoms = match req_opt with None -> [] | Some s -> collect_pt_atoms s in
  let pre_map = pre_value_to_loc_map pre_atoms in

  (* NEW: read-only ranges from req *)
  let req_ranges = match req_opt with None -> [] | Some s -> collect_range_atoms s in

  let assumes_p = pred_of_sl b.assumes in

  let post_sl_opt =
    match ens_opt, spec_ret with
    | None, _ -> None
    | Some post, None -> Some post
    | Some post, Some r -> Some (rewrite_result r post)
  in

  let ensures_p =
    match post_sl_opt with
    | None -> C.PTrue
    | Some post_sl -> build_ensures ~pre_map ~post_sl
  in

  let ptrs_for_req_assign =
    match global_ptrs, kind with
    | Some g, C.FunctionContract -> g
    | Some g, C.LoopContract -> g
    | None, _ -> ptrs_of_behavior b
  in

  (* UPDATED: requires = valid(ptrs) && valid_read_range(...) *)
  let requires_clause =
    let p_valid = requires_from_ptrs ptrs_for_req_assign in
    let p_read = requires_from_ranges req_ranges in
    C.Requires (p_and [ p_valid; p_read ])
  in

  (* UPDATED: function assigns still only from ptrs (read-only ranges contribute none) *)
  let assigns_clause =
    match kind with
    | C.FunctionContract ->
        C.Assigns (assigns_from_ptrs ptrs_for_req_assign)
    | C.LoopContract -> (
        match post_sl_opt with
        | None -> C.Assigns []
        | Some post_sl -> C.Assigns (assigns_from_post_vars post_sl)
      )
  in

  let variant_clause =
    match var_opt with
    | None -> []
    | Some e -> [ C.Variant (term_of_expr C.Pre e) ]
  in

  {
    C.b_name;
    clauses =
      [ C.Assumes assumes_p
      ; requires_clause
      ; C.Ensures ensures_p
      ; assigns_clause
      ]
      @ variant_clause;
  }

(* ---------- Spec translation ---------- *)

let sl_to_core (spec : Sl_ast.spec) : C.spec =
  let kind = kind_of_spec spec in
  let names = normalize_behavior_names spec.behaviors in

  let global_ptrs =
    match spec.behaviors with
    | [] | [ _ ] -> None
    | _ -> Some (global_ptrs_of_spec spec)
  in

  let behaviors =
    List.map2
      (fun nm b ->
         core_behavior_of_sl
           ~kind
           ~spec_ret:spec.ret
           ~b_name:nm
           ~global_ptrs
           b)
      names
      spec.behaviors
  in

  { C.kind = kind; params = []; behaviors }
