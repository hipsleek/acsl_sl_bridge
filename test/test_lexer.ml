open Sl_parser

(*helper*)
let string_of_token = function
  | REQ -> "REQ"
  | ENS -> "ENS"
  | ARROW -> "ARROW"
  | TYPE s -> "TYPE(" ^ s ^ ")"
  | STAR -> "STAR"
  | AND -> "AND"
  | EQEQ -> "EQEQ"
  | PRIME -> "PRIME"
  | OLD -> "OLD"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | SEMICOLON -> "SEMICOLON"
  | EOF -> "EOF"
  | ID s -> "ID(" ^ s ^ ")"

let lex_all (input : string) : token list =
  let lexbuf = Lexing.from_string input in
  let rec loop acc =
    match Sl_lexer.token lexbuf with
    | EOF -> List.rev acc
    | tok -> loop (tok :: acc)
  in
  loop []

let assert_string_list_equal name expected actual =
  let rec go e a i =
    match e, a with
    | [], [] -> () (*Both lists empty list*)
    | x :: xs, y :: ys when x = y -> go xs ys (i + 1) (*First elem both lists match*)
    | x :: _,  y :: _ -> (*First element dont match*)
        failwith
          (Printf.sprintf
             "Test %s failed at index %d.\nExpected: %s\nGot:      %s\n"
             name i x y)
    | [], _ -> (*There were more tokens produced than expected*)
        failwith
          (Printf.sprintf
             "Test %s failed: expected end of list but got extra tokens."
             name)
    | _, [] -> (*There were fewer tokens produced than expected*)
        failwith
          (Printf.sprintf
             "Test %s failed: expected more tokens but list ended."
             name)
    in go expected actual 0

let test_framework test_name input expected =
  let tokens = lex_all input in
  let token_strings = List.map string_of_token tokens in
  assert_string_list_equal test_name expected token_strings
  
(*unit test*)
let test_lexer_atom_int () =
  let test_name = "lexer_atom_int" in
  let input = "a->int*(u)" in
  let expected = [
      "ID(a)";
      "ARROW";
      "TYPE(int)";
      "STAR";
      "LPAREN";
      "ID(u)";
      "RPAREN";
  ] in
  test_framework test_name input expected

let test_lexer_atom_char () =
  let test_name = "lexer_atom_char" in
  let input = "a->char*(u)" in
  let expected = [
      "ID(a)";
      "ARROW";
      "TYPE(char)";
      "STAR";
      "LPAREN";
      "ID(u)";
      "RPAREN";
  ] in
  test_framework test_name input expected

let test_lexer_formula () =
  let test_name = "lexer_formula" in
  let input = "a->int*(u) && b->int*(v)" in
  let expected = [
      "ID(a)";
      "ARROW";
      "TYPE(int)";
      "STAR";
      "LPAREN";
      "ID(u)";
      "RPAREN";
      "AND";
      "ID(b)";
      "ARROW";
      "TYPE(int)";
      "STAR";
      "LPAREN";
      "ID(v)";
      "RPAREN";
  ] in
  test_framework test_name input expected

let test_lexer_spec_swap () =
  let test_name = "lexer_spec_swap" in
  let input = "req a->int*(u) && b->int*(v);" in
  let expected =
    [
      "REQ";
      "ID(a)";
      "ARROW";
      "TYPE(int)";
      "STAR";
      "LPAREN";
      "ID(u)";
      "RPAREN";
      "AND";
      "ID(b)";
      "ARROW";
      "TYPE(int)";
      "STAR";
      "LPAREN";
      "ID(v)";
      "RPAREN";
      "SEMICOLON";
    ] in
  test_framework test_name input expected

let test_lexer_spec_prime_sugar () =
  let test_name = "lexer_spec_prime_sugar" in
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN";
      "STAR";
      "ID(a)";
      "RPAREN";
      "PRIME";
      "EQEQ";
      "LPAREN";
      "STAR";
      "ID(b)";
      "RPAREN";
      "AND";
      "LPAREN";
      "STAR";
      "ID(b)";
      "RPAREN";
      "PRIME";
      "EQEQ";
      "LPAREN";
      "STAR";
      "ID(a)";
      "RPAREN";
      "SEMICOLON";
    ] in
  test_framework test_name input expected

let test_lexer_spec_prime_old () =
  let test_name = "lexer_spec_prime_old" in
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN";
      "STAR";
      "ID(a)";
      "RPAREN";
      "EQEQ";
      "OLD";
      "LPAREN";
      "STAR";
      "ID(b)";
      "RPAREN";
      "AND";
      "LPAREN";
      "STAR";
      "ID(b)";
      "RPAREN";
      "EQEQ";
      "OLD";
      "LPAREN";
      "STAR";
      "ID(a)";
      "RPAREN";
      "SEMICOLON";
    ] in
  test_framework test_name input expected

let () =
  test_lexer_atom_int ();
  test_lexer_atom_char ();
  test_lexer_formula ();
  test_lexer_spec_swap ();
  test_lexer_spec_prime_sugar ();
  test_lexer_spec_prime_old ();
