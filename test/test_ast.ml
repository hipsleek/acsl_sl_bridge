let test_string_of_spec_swap () =
  let open Ast in
  let h_pre =
    Sep (
      Atom (PointTo ("a", "u")),
      Atom (PointTo ("b", "v"))
    )
  in
  let f_pre = HeapOnly h_pre in

  let h_post =
    Sep (
      Atom (PointTo ("a", "v")),
      Atom (PointTo ("b", "u"))
    )
  in
  let f_post = HeapOnly h_post in

  let spec_swap = { pre = f_pre; post = f_post } in
  let actual = string_of_spec spec_swap in

  let expected =
    "req (a->int*(u) * b->int*(v)); ens (a->int*(v) * b->int*(u));"
  in

  if actual <> expected then
    failwith
      (Printf.sprintf "string_of_spec failed.\nExpected: %S\nGot:      %S\n"
         expected actual)

let () =
  test_string_of_spec_swap ()
