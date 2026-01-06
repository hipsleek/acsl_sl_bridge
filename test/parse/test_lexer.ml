(* test_sl_lexer_ounit.ml *)

open OUnit2
open Sl_parser

(* helper *)
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
  | PLUS -> "PLUS"
  | TIMES -> "TIMES"
  | DIV -> "DIV"
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

let test_framework (input : string) (expected : string list) : unit =
  let tokens = lex_all input in
  let actual = List.map string_of_token tokens in
  assert_equal
    expected
    actual

(* unit tests *)
let test_lexer_atom_int _ctx =
  let input = "a->int*(u)" in
  let expected =
    [ "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN" ]
  in
  test_framework input expected

let test_lexer_atom_char _ctx =
  let input = "a->char*(u)" in
  let expected =
    [ "ID(a)"; "ARROW"; "TYPE(char)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN" ]
  in
  test_framework input expected

let test_lexer_formula _ctx =
  let input = "a->int*(u) && b->int*(v)" in
  let expected =
    [
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
    ]
  in
  test_framework input expected

let test_lexer_spec_swap _ctx =
  let input = "req a->int*(u) && b->int*(v);" in
  let expected =
    [
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_spec_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "PRIME"; "EQEQ";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
      "AND";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "PRIME"; "EQEQ";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
      "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_spec_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "EQEQ"; "OLD";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
      "AND";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "EQEQ"; "OLD";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
      "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_case_spec _ctx =
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
  let expected =
    [
      "CASE"; "LBRACE";

      "ID(a)"; "EQEQ"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(a)"; "NEQ"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(a)"; "LTE"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(a)"; "LT"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(a)"; "GTE"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(a)"; "GT"; "ID(b)"; "IMPLIES";
      "REQ";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";
      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "AND";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "RBRACE"; "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_arith_sub _ctx =
  let input = "30-i" in
  let expected = [ "INT(30)"; "MINUS"; "ID(i)" ] in
  test_framework input expected

let test_lexer_conditional_lt _ctx =
  let input = "i<30" in
  let expected = [ "ID(i)"; "LT"; "INT(30)" ] in
  test_framework input expected

let test_lexer_all_comparators _ctx =
  let input = "a==b a!=b a<=b a<b a>=b a>b" in
  let expected =
    [
      "ID(a)"; "EQEQ"; "ID(b)";
      "ID(a)"; "NEQ";  "ID(b)";
      "ID(a)"; "LTE";  "ID(b)";
      "ID(a)"; "LT";   "ID(b)";
      "ID(a)"; "GTE";  "ID(b)";
      "ID(a)"; "GT";   "ID(b)";
    ]
  in
  test_framework input expected

let test_lexer_case_loop_term _ctx =
  let input =
    "case { i<30 => req Term[30-i]; ens a->int*(u); \
            i>=30 => req Term[]; ens b->int*(v);};"
  in
  let expected =
    [
      "CASE"; "LBRACE";

      "ID(i)"; "LT"; "INT(30)"; "IMPLIES";

      "REQ"; "TERM"; "LBRACK"; "INT(30)"; "MINUS"; "ID(i)"; "RBRACK";
      "SEMICOLON";

      "ENS";
      "ID(a)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(u)"; "RPAREN";
      "SEMICOLON";

      "ID(i)"; "GTE"; "INT(30)"; "IMPLIES";

      "REQ"; "TERM"; "LBRACK"; "RBRACK"; "SEMICOLON";

      "ENS";
      "ID(b)"; "ARROW"; "TYPE(int)"; "STAR"; "LPAREN"; "ID(v)"; "RPAREN";
      "SEMICOLON";

      "RBRACE"; "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_prime_sugar _ctx =
  let input = "ens (*a)'==(*b) && (*b)'==(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "PRIME"; "EQEQ";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
      "AND";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "PRIME"; "EQEQ";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
      "SEMICOLON";
    ]
  in
  test_framework input expected

let test_lexer_old_sugar _ctx =
  let input = "ens (*a)==\\old(*b) && (*b)==\\old(*a);" in
  let expected =
    [
      "ENS";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN"; "EQEQ"; "OLD";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN";
      "AND";
      "LPAREN"; "STAR"; "ID(b)"; "RPAREN"; "EQEQ"; "OLD";
      "LPAREN"; "STAR"; "ID(a)"; "RPAREN";
      "SEMICOLON";
    ]
  in
  test_framework input expected

let suite =
  "sl_lexer" >::: [
    "atom_int"          >:: test_lexer_atom_int;
    "atom_char"         >:: test_lexer_atom_char;
    "formula"           >:: test_lexer_formula;
    "spec_swap"         >:: test_lexer_spec_swap;
    "spec_prime_sugar"  >:: test_lexer_spec_prime_sugar;
    "spec_old_sugar"    >:: test_lexer_spec_old_sugar;
    "case_spec"         >:: test_lexer_case_spec;
    "arith_sub"         >:: test_lexer_arith_sub;
    "conditional_lt"    >:: test_lexer_conditional_lt;
    "all_comparators"   >:: test_lexer_all_comparators;
    "case_loop_term"    >:: test_lexer_case_loop_term;
    "prime_sugar"       >:: test_lexer_prime_sugar;
    "old_sugar"         >:: test_lexer_old_sugar;
  ]

let () = run_test_tt_main suite
