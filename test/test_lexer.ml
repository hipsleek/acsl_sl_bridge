open Sl_parser

(*helper*)
let string_of_token = function
  | REQ -> "REQ"
  | ENS -> "ENS"
  | CASE -> "CASE"
  | TERM -> "TERM"
  | ARROW -> "ARROW"
  | TYPE s -> "TYPE(" ^ s ^ ")"
  | STAR -> "STAR"
  | AND -> "AND"
  | SL_CONJ -> "SL_CONJ"
  | EQEQ -> "EQEQ"
  | NEQ -> "NEQ"
  | GTE -> "GTE"
  | GT -> "GT"
  | LTE -> "LTE"
  | LT -> "LT"
  | PRIME -> "PRIME"
  | OLD -> "OLD"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LBRACK -> "LBRACK"
  | RBRACK -> "RBRACK"
  | IMPLIES -> "IMPLIES"
  | SEMICOLON -> "SEMICOLON"
  | EOF -> "EOF"
  | MINUS -> "MINUS"
  | ID s -> "ID(" ^ s ^ ")"
  | INT n -> "INT(" ^ string_of_int n ^ ")"

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

let test_lexer_case_spec () =
  let test_name = "lexer_case_spec" in
  let input =
    "case {\n" ^
    "  a==b => req a->int*(u); ens a->int*(u);\n" ^
    "  a!=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a<=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a<b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a>=b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "  a>b => req a->int*(u) && b->int*(v); ens a->int*(v) && b->int*(u);\n" ^
    "};"
  in
  let expected = [
    "CASE";
    "LBRACE";

    "ID(a)";
    "EQEQ";
    "ID(b)";
    "IMPLIES";
    "REQ";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(a)";
    "NEQ";
    "ID(b)";
    "IMPLIES";
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
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "AND";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(a)";
    "LTE";
    "ID(b)";
    "IMPLIES";
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
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "AND";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(a)";
    "LT";
    "ID(b)";
    "IMPLIES";
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
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "AND";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(a)";
    "GTE";
    "ID(b)";
    "IMPLIES";
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
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "AND";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(a)";
    "GT";
    "ID(b)";
    "IMPLIES";
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
    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "AND";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "RBRACE";
    "SEMICOLON";
  ] in
  test_framework test_name input expected

let test_lexer_arith_sub () =
  let test_name = "lexer_arith_sub" in
  let input = "30-i" in
  let expected = [
    "INT(30)";
    "MINUS";
    "ID(i)";
  ] in
  test_framework test_name input expected

let test_lexer_conditional_lt () =
  let test_name = "lexer_conditional_lt" in
  let input = "i<30" in
  let expected = [
    "ID(i)";
    "LT";
    "INT(30)";
  ] in
  test_framework test_name input expected

let test_lexer_all_comparators () =
  let test_name = "lexer_all_comparators" in
  let input = "a==b a!=b a<=b a<b a>=b a>b" in
  let expected = [
    "ID(a)"; "EQEQ"; "ID(b)";
    "ID(a)"; "NEQ";  "ID(b)";
    "ID(a)"; "LTE";  "ID(b)";
    "ID(a)"; "LT";   "ID(b)";
    "ID(a)"; "GTE";  "ID(b)";
    "ID(a)"; "GT";   "ID(b)";
  ] in
  test_framework test_name input expected


let test_lexer_case_loop_term () =
  let test_name = "lexer_case_loop_term" in
  let input =
    "case { i<30 => req Term[30-i]; ens a->int*(u); \
            i>=30 => req Term[]; ens b->int*(v);};"
  in
  let expected = [
    "CASE";
    "LBRACE";

    "ID(i)";
    "LT";
    "INT(30)";
    "IMPLIES";

    "REQ";
    "TERM";
    "LBRACK";
    "INT(30)";
    "MINUS";
    "ID(i)";
    "RBRACK";
    "SEMICOLON";

    "ENS";
    "ID(a)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(u)";
    "RPAREN";
    "SEMICOLON";

    "ID(i)";
    "GTE";
    "INT(30)";
    "IMPLIES";

    "REQ";
    "TERM";
    "LBRACK";
    "RBRACK";
    "SEMICOLON";

    "ENS";
    "ID(b)";
    "ARROW";
    "TYPE(int)";
    "STAR";
    "LPAREN";
    "ID(v)";
    "RPAREN";
    "SEMICOLON";

    "RBRACE";
    "SEMICOLON";
  ] in
  test_framework test_name input expected

let test_lexer_prime_sugar () =
  let test_name = "lexer_prime_sugar" in
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected = [
    "ENS";
    "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "PRIME"; "EQEQ";
    "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
    "AND";
    "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "PRIME"; "EQEQ";
    "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
    "SEMICOLON";
  ] in
  test_framework test_name input expected

let test_lexer_old_sugar () =
  let test_name = "lexer_old_sugar" in
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected = [
    "ENS";
    "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "EQEQ"; "OLD";
    "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
    "AND";
    "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "EQEQ"; "OLD";
    "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
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

  test_lexer_case_spec ();

  test_lexer_arith_sub ();
  test_lexer_conditional_lt ();
  test_lexer_all_comparators ();
  test_lexer_case_loop_term ();
  test_lexer_prime_sugar ();
  test_lexer_old_sugar ();
