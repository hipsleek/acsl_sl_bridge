open Ast

type swap_pattern = {
  a : ptr;
  b : ptr;
  u : car;
  v : car;
}


let recognise_swap (s : spec) : swap_pattern option =
  match s.pre, s.post with
  | Sep (Atom (PointTo (a, u)), Atom (PointTo (b, v))),
    Sep (Atom (PointTo (a', v')), Atom (PointTo (b', u')))
      when a = a' && b = b' && u = u' && v = v' ->
        Some { a; b; u; v }
  | _ ->
      None

let acsl_of_swap (sp : swap_pattern) : string =
  let a = sp.a in
  let b = sp.b in
  Printf.sprintf
"/*@
  requires \\valid(%s) && \\valid(%s);
  assigns  *%s, *%s;
  ensures  *%s == \\old(*%s) && *%s == \\old(*%s);
*/"
    a b
    a b
    a b
    b a

let sl_spec_to_acsl (s : spec) : string =
  match recognise_swap s with
  | Some sp -> acsl_of_swap sp
  | None -> "/* unsupported SL spec for now */"
