(* sl_to_core.ml *)
open Sl_ast
module C = Core

module SS = Set.Make (String)
module SM = Map.Make (String)

(* ----------------------------- *)
(* Helpers: SL traversal         *)
(* ----------------------------- *)

let rec ptrs_of_assertion (a : assertion) : SS.t =
  match a with
  | AEmp -> SS.empty
  | AHeapAtom (PointTo (p, _ty, _car)) -> SS.singleton p
  | ASep (x, y)
  | AAnd (x, y)
  | AOr (x, y)
  | AImplies (x, y) ->
      SS.union (ptrs_of_assertion x) (ptrs_of_assertion y)
  | ANot x -> ptrs_of_assertion x
  | APure _ -> SS.empty
  | ASugarPrime pairs
  | ASugarOld pairs ->
      List.fold_left
        (fun acc (p, q) -> SS.add p (SS.add q acc))
        SS.empty
        pairs

let rec heap_map_of_assertion (a : assertion) : string SM.t =
  (* map ptr -> car (value variable name) *)
  match a with
  | AEmp -> SM.empty
  | AHeapAtom (PointTo (p, _ty, car)) -> SM.add p car SM.empty
  | ASep (x, y)
  | AAnd (x, y) ->
      (* heap specs normally use Sep; but AND appears in your surface syntax too *)
      let mx = heap_map_of_assertion x in
      let my = heap_map_of_assertion y in
      SM.union (fun _ a _ -> Some a) mx my
  | AOr _
  | ANot _
  | AImplies _
  | APure _
  | ASugarPrime _
  | ASugarOld _ ->
      SM.empty

let rec vars_post_of_arith (e : arith) : SS.t =
  match e with
  | APostVar x -> SS.singleton x
  | AVar _ | AInt _ | AResult -> SS.empty
  | AOld a -> vars_post_of_arith a
  | AAdd (a,b)
  | ASub (a,b)
  | AMul (a,b)
  | ADiv (a,b) ->
      SS.union (vars_post_of_arith a) (vars_post_of_arith b)

let rec vars_post_of_assertion (a : assertion) : SS.t =
  match a with
  | AEmp -> SS.empty
  | AHeapAtom _ -> SS.empty
  | ASugarPrime _ | ASugarOld _ -> SS.empty
  | APure p ->
      (match p with
       | PEq (x,y)
       | PNeq (x,y)
       | PLt (x,y)
       | PLte (x,y)
       | PGt (x,y)
       | PGte (x,y) ->
           SS.union (vars_post_of_arith x) (vars_post_of_arith y))
  | ASep (x,y)
  | AAnd (x,y)
  | AOr (x,y)
  | AImplies (x,y) ->
      SS.union (vars_post_of_assertion x) (vars_post_of_assertion y)
  | ANot x -> vars_post_of_assertion x

(* Try to recognize Term[k - v] so we can choose the "main" variant case. *)
let variant_key (e : arith) : (int * string) option =
  match e with
  | ASub (AInt k, AVar v) -> Some (k, v)
  | _ -> None

(* ----------------------------- *)
(* SL -> Core term/predicate     *)
(* ----------------------------- *)

let arith_op_of_sl = function
  | AAdd _ -> C.Add
  | ASub _ -> C.Sub
  | AMul _ -> C.Mul
  | ADiv _ -> C.Div
  | _ -> failwith "not an operator node"

let rec term_of_arith ?(result_binder : string option = None) (e : arith) : C.term =
  match e with
  | AInt n -> C.TInt n

  | AVar x ->
      (* binder: ens[r] r == ... means r is \result *)
      (match result_binder with
       | Some r when r = x -> C.TResult
       | _ -> C.TVar (C.Pre, x))

  | APostVar x -> C.TVar (C.Post, x)

  | AOld a ->
      (* Core has no explicit old; encode old by forcing everything to Pre. *)
      term_of_arith ~result_binder a

  | AResult -> C.TResult

  | AAdd (a,b) -> C.TArith (C.Add, term_of_arith ~result_binder a, term_of_arith ~result_binder b)
  | ASub (a,b) -> C.TArith (C.Sub, term_of_arith ~result_binder a, term_of_arith ~result_binder b)
  | AMul (a,b) -> C.TArith (C.Mul, term_of_arith ~result_binder a, term_of_arith ~result_binder b)
  | ADiv (a,b) -> C.TArith (C.Div, term_of_arith ~result_binder a, term_of_arith ~result_binder b)

let rel_of_sl = function
  | PEq _  -> C.Eq
  | PNeq _ -> C.Neq
  | PLt _  -> C.Lt
  | PLte _ -> C.Lte
  | PGt _  -> C.Gt
  | PGte _ -> C.Gte

let predicate_of_pure ?(result_binder : string option = None) (p : pure_atom) : C.predicate =
  let mk r a b =
    C.PAtom (C.ARel (r, term_of_arith ~result_binder a, term_of_arith ~result_binder b))
  in
  match p with
  | PEq (a,b)  -> mk C.Eq a b
  | PNeq (a,b) -> mk C.Neq a b
  | PLt (a,b)  -> mk C.Lt a b
  | PLte (a,b) -> mk C.Lte a b
  | PGt (a,b)  -> mk C.Gt a b
  | PGte (a,b) -> mk C.Gte a b

let rec predicate_of_assertion ?(result_binder : string option = None) (a : assertion) : C.predicate =
  match a with
  | AEmp ->
      (* treat emp as true for guard purposes *)
      C.PTrue

  | APure p ->
      predicate_of_pure ~result_binder p

  | AAnd (x,y) ->
      C.PAnd [ predicate_of_assertion ~result_binder x; predicate_of_assertion ~result_binder y ]

  | AOr (x,y) ->
      C.POr [ predicate_of_assertion ~result_binder x; predicate_of_assertion ~result_binder y ]

  | ANot x ->
      C.PNot (predicate_of_assertion ~result_binder x)

  | AImplies (x,y) ->
      C.PImplies (predicate_of_assertion ~result_binder x, predicate_of_assertion ~result_binder y)

  | AHeapAtom _
  | ASep _
  | ASugarPrime _
  | ASugarOld _ ->
      (* heap structure isn't used as a boolean guard in your current tests;
         if it ever is, you can add a richer encoding later. *)
      C.PTrue

(* ----------------------------- *)
(* Heap swap logic (Core ensures) *)
(* ----------------------------- *)

let mk_valid (p : string) : C.predicate =
  C.PAtom (C.APred ("valid", [ C.TPtr p ]))

let mk_heap_eq_post_pre (p_post : string) (p_pre : string) : C.predicate =
  C.PAtom (C.ARel (C.Eq, C.THeap (C.Post, p_post), C.THeap (C.Pre, p_pre)))

let ensures_from_heap_maps (pre : string SM.t) (post : string SM.t) : C.predicate list =
  (* match post ptr's car to the pre ptr that had the same car *)
  let pre_rev =
    SM.fold
      (fun pre_ptr car acc -> SM.add car pre_ptr acc)
      pre
      SM.empty
  in
  SM.fold
    (fun post_ptr car acc ->
       match SM.find_opt car pre_rev with
       | None -> acc
       | Some pre_ptr -> mk_heap_eq_post_pre post_ptr pre_ptr :: acc)
    post
    []

let ensures_from_sugar_prime (pairs : (ptr * ptr) list) : C.predicate list =
  List.map (fun (a,b) -> mk_heap_eq_post_pre a b) pairs

let ensures_from_sugar_old (pairs : (ptr * ptr) list) : C.predicate list =
  List.map (fun (a,b) -> mk_heap_eq_post_pre a b) pairs

(* ----------------------------- *)
(* Loop detection + extraction   *)
(* ----------------------------- *)

let is_loop_case (c : case_spec) : bool =
  match c.term with
  | None -> false
  | Some _ ->
      (* your loop desugaring sets pre = AEmp; keep it permissive anyway *)
      true

let choose_main_variant_case (cases : case_spec list) : case_spec option =
  let candidates =
    cases
    |> List.filter (fun c ->
           match c.term with Some (Term _) -> true | _ -> false)
  in
  match candidates with
  | [] -> None
  | [c] -> Some c
  | cs ->
      (* pick the one with max k in (k - v) when possible, else first *)
      let score c =
        match c.term with
        | Some (Term e) ->
            (match variant_key e with Some (k, _) -> k | None -> min_int)
        | _ -> min_int
      in
      Some (List.fold_left (fun best c -> if score c > score best then c else best) (List.hd cs) (List.tl cs))

let term_of_terminate = function
  | TermNone -> None
  | Term e -> Some (term_of_arith e)

(* ----------------------------- *)
(* Building Core specs/behaviors *)
(* ----------------------------- *)

let behavior_of_simple (b : base_spec) : C.behavior =
  let pre_map = heap_map_of_assertion b.pre in
  let post_map = heap_map_of_assertion b.post in
  let ptrs =
    SS.union (ptrs_of_assertion b.pre) (ptrs_of_assertion b.post)
    |> SS.elements
  in
  let requires = ptrs |> List.map mk_valid in
  let assigns  = ptrs |> List.map (fun p -> C.AsHeap p) in
  let ensures  = ensures_from_heap_maps pre_map post_map in
  {
    b_name = None;
    clauses =
      (List.map (fun p -> C.Requires p) requires)
      @ [ C.Assigns assigns ]
      @ (List.map (fun p -> C.Ensures p) ensures);
  }

let behavior_of_case (idx : int) (global_ptrs : string list) (c : case_spec) : C.behavior =
  let name = Some (Printf.sprintf "case%d" idx) in
  let assumes = predicate_of_assertion c.test in

  (* requires/assigns are “global” in ACSL output; we keep them as per-behavior clauses
     for now, and let Core->ACSL backend hoist/merge as you already do. *)
  let requires = global_ptrs |> List.map mk_valid in
  let assigns  = global_ptrs |> List.map (fun p -> C.AsHeap p) in

  let ensures =
    match c.post with
    | ASugarPrime pairs -> ensures_from_sugar_prime pairs
    | ASugarOld pairs -> ensures_from_sugar_old pairs
    | _ ->
        let pre_map = heap_map_of_assertion c.pre in
        let post_map = heap_map_of_assertion c.post in
        let heap_ens = ensures_from_heap_maps pre_map post_map in
        if heap_ens <> [] then heap_ens
        else
          (* loop-ish post conditions like i'==30, a'==a+(...) are pure assertions *)
          [ predicate_of_assertion c.post ]
  in

  let variant_clause =
    match c.term with
    | None -> []
    | Some TermNone -> [ C.Variant (C.TInt 0) ]  (* won't be used for function contracts *)
    | Some (Term e) -> [ C.Variant (term_of_arith e) ]
  in

  {
    b_name = name;
    clauses =
      [ C.Assumes assumes ]
      @ (List.map (fun p -> C.Requires p) requires)
      @ [ C.Assigns assigns ]
      @ (List.concat_map (fun p -> [C.Ensures p]) ensures)
      @ variant_clause;
  }

let spec_of_loop_cases (cases : case_spec list) : C.spec =
  (* invariant/variant from the “main” Term[k - v] case (matches your expectations) *)
  let main =
    match choose_main_variant_case cases with
    | Some c -> c
    | None -> List.hd cases
  in

  let invariant = predicate_of_assertion main.test in

  (* assigns: all vars that appear as post-vars in any post condition *)
  let assigns_vars =
    cases
    |> List.fold_left
        (fun acc (c : case_spec) ->
            SS.union acc (vars_post_of_assertion c.post))
        SS.empty
    |> SS.elements
    |> List.map (fun v -> C.AsVar v)
  in


  let variant =
    match main.term with
    | Some (Term e) -> Some (term_of_arith e)
    | _ -> None
  in

  let clauses =
    [ C.Assumes invariant; C.Assigns assigns_vars ]
    @ (match variant with None -> [] | Some t -> [ C.Variant t ])
  in
  {
    kind = C.LoopContract;
    params = [];
    behaviors = [ { b_name = None; clauses } ];
  }

let spec_of_function_cases (cases : case_spec list) : C.spec =
  let global_ptrs =
    cases
    |> List.fold_left
         (fun acc c ->
            SS.union acc (SS.union (ptrs_of_assertion c.pre) (ptrs_of_assertion c.post)))
         SS.empty
    |> SS.elements
  in
  let behaviors =
    cases |> List.mapi (fun i c -> behavior_of_case (i+1) global_ptrs c)
  in
  { kind = C.FunctionContract; params = []; behaviors }

let behavior_of_ens (e : ens_spec) : C.behavior =
  (* expects post is typically a pure eq involving binder r *)
  let ensures =
    match e.post with
    | APure p -> predicate_of_pure ~result_binder:e.ret p
    | _ -> predicate_of_assertion ~result_binder:e.ret e.post
  in
  {
    b_name = None;
    clauses =
      [ C.Requires C.PTrue
      ; C.Assigns [] (* will become \nothing in ACSL backend *)
      ; C.Ensures ensures
      ];
  }

(* ----------------------------- *)
(* Public entrypoint             *)
(* ----------------------------- *)

let sl_to_core (s : Sl_ast.spec) : C.spec =
  match s with
  | Simple b ->
      { kind = C.FunctionContract; params = []; behaviors = [ behavior_of_simple b ] }

  | Ens e ->
      { kind = C.FunctionContract; params = []; behaviors = [ behavior_of_ens e ] }

  | Case cases ->
      if cases <> [] && List.for_all is_loop_case cases
      then spec_of_loop_cases cases
      else spec_of_function_cases cases
