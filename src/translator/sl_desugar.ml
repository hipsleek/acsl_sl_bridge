open Sl_ast

module Prime_to_old = struct
  let rec expr_has_post (e : expr) : bool =
    match e with
    | EPost _ -> true
    | EOld e1 -> expr_has_post e1
    | EDeref e1 -> expr_has_post e1
    | EUnop (_, e1) -> expr_has_post e1
    | EBinop (_, a, b) -> expr_has_post a || expr_has_post b
    | EApp (_, es) -> List.exists expr_has_post es
    | EVar _ | EConstInt _ | EConstBool _ | EResult -> false

  let rec sl_has_post (s : sl) : bool =
    match s with
    | STrue | SFalse | SEmp -> false
    | SPure e -> expr_has_post e
    | SHeap h -> (
        match h with
        | HPt { loc; value; _ } -> expr_has_post loc || expr_has_post value
        | HPred (_nm, args) -> List.exists expr_has_post args
        | HRange { loc; lo; hi; _ } -> expr_has_post loc || expr_has_post lo || expr_has_post hi
      )
    | SSep xs | SAnd xs | SOr xs -> List.exists sl_has_post xs
    | SNot x -> sl_has_post x
    | SImplies (a, b) -> sl_has_post a || sl_has_post b
    | SExists (_bs, body) | SForall (_bs, body) -> sl_has_post body

  type mode =
    | PrimeMode
    | OldMode

  type ctx =
    | InPre
    | InPost
    | InOld 

  let wrap_old (e : expr) : expr = EOld e
  let rec rewrite_expr_prime (ctx : ctx) (e : expr) : expr * bool =
    match e with
    | EResult -> (EResult, true)

    | EVar _ | EConstInt _ | EConstBool _ ->
        (e, false)

    | EOld e1 ->
        let (e1', _hp) = rewrite_expr_prime InOld e1 in
        (EOld e1', false)

    | EPost e1 -> 
        let (e1', _hp) = rewrite_expr_prime InPost e1 in
        (e1', true)

    | EDeref e1 ->
        let (e1', hp) = rewrite_expr_prime ctx e1 in
        let out = EDeref e1' in let out =
          match ctx with
          | InPre when not hp -> wrap_old out
          | _ -> out
        in
        (out, hp)

    | EUnop (op, e1) ->
        let (e1', hp) = rewrite_expr_prime ctx e1 in
        let out = EUnop (op, e1') in
        let out =
          match ctx with
          | InPre when not hp -> wrap_old out
          | _ -> out
        in
        (out, hp)

    | EBinop (op, a, b) ->
        let (a', ha) = rewrite_expr_prime ctx a in
        let (b', hb) = rewrite_expr_prime ctx b in
        let hp = ha || hb in
        let out = EBinop (op, a', b') in
        let out =
          match ctx with
          | InPre when not hp -> wrap_old out
          | _ -> out
        in
        (out, hp)

    | EApp (f, es) ->
        let (es', hp) =
          List.fold_right
            (fun x (acc_es, acc_hp) ->
              let (x', hx) = rewrite_expr_prime ctx x in
              (x' :: acc_es, acc_hp || hx))
            es
            ([], false)
        in
        let out = EApp (f, es') in
        let out =
          match ctx with
          | InPre when not hp -> wrap_old out
          | _ -> out
        in
        (out, hp)

  let rec map_sl_in_ens (mode : mode) (s : sl) : sl =
    let map_expr (e : expr) : expr =
      match mode with
      | OldMode -> e
      | PrimeMode -> fst (rewrite_expr_prime InPre e)
    in
    match s with
    | STrue | SFalse | SEmp -> s
    | SPure e -> SPure (map_expr e)
    | SHeap (HPt { loc; ty; value; mode = hm }) ->
        SHeap (HPt { loc = map_expr loc; ty; value = map_expr value; mode = hm })
    | SHeap (HRange { loc; alias; ty; lo; hi; mode = hm }) ->
        SHeap (HRange { loc = map_expr loc; alias; ty; lo = map_expr lo; hi = map_expr hi; mode = hm })
    | SHeap (HPred (nm, args)) ->
        SHeap (HPred (nm, List.map map_expr args))
    | SSep xs -> SSep (List.map (map_sl_in_ens mode) xs)
    | SAnd xs -> SAnd (List.map (map_sl_in_ens mode) xs)
    | SOr xs -> SOr (List.map (map_sl_in_ens mode) xs)
    | SNot x -> SNot (map_sl_in_ens mode x)
    | SImplies (a, b) -> SImplies (map_sl_in_ens mode a, map_sl_in_ens mode b)
    | SExists (bs, body) -> SExists (bs, map_sl_in_ens mode body)
    | SForall (bs, body) -> SForall (bs, map_sl_in_ens mode body)

  let desugar_block (blk : block) : block =
    List.map
      (function
        | CEns post_sl ->
            let mode = if sl_has_post post_sl then PrimeMode else OldMode in
            CEns (map_sl_in_ens mode post_sl)
        | other -> other)
      blk

  let desugar_behavior (b : behavior) : behavior =
    { b with body = desugar_block b.body }

  let desugar_spec (sp : spec) : spec =
    { sp with behaviors = List.map desugar_behavior sp.behaviors }
end
