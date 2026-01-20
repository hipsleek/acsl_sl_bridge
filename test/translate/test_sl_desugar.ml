open OUnit2

let parse_spec (input : string) : Sl_ast.spec =
  let lexbuf = Lexing.from_string input in
  Sl_parser.main Sl_lexer.token lexbuf

let desugar_of (input : string) : string =
  let sl_spec = parse_spec input in
  let core_spec = Sl_desugar.Prime_to_old.desugar_spec sl_spec in
  Sl_ast_printer.string_of_spec core_spec

let test_framework (input : string) (expected : string) : unit =
  let desugar = desugar_of input in
  assert_equal ~printer:(fun s -> "\n" ^ s ^ "\n") expected desugar 


let test_translate_swap_prime_notation_sugar _ctx =
  let input = "ens (*a)' == (*b) && (*b)' == (*a);" in
  let expected = "ens (*a) == \\old(*b) && (*b) == \\old(*a);" in
  test_framework input expected

let test_translate_swap_old_notation_sugar _ctx =
  let input = "ens (*a) == \\old(*b) && (*b) == \\old(*a);" in
  let expected = "ens (*a) == \\old(*b) && (*b) == \\old(*a);" in
  test_framework input expected

let suite =
  "translate" >::: [
    "swap_prime_notation_sugar"  >:: test_translate_swap_prime_notation_sugar;
    "swap_old_notation_sugar" >:: test_translate_swap_old_notation_sugar;
    
  ]

let () = run_test_tt_main suite