{
  open Sl_parser
}

let whitespace = [' ' '\t' '\r' '\n']+
let digits = ['0'-'9']+
let ident_start = ['a'-'z' 'A'-'Z' '_']
let ident_char  = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let ident = ident_start ident_char*

rule token = parse
  | whitespace { token lexbuf }

  (* keywords *)
  | "req"  { REQ }
  | "ens"  { ENS }
  | "case" { CASE }

  (* types *)
  | "int"    { TYPE "int" }
  | "char"   { TYPE "char" }
  | "bool"   { TYPE "bool" }
  | "void"   { TYPE "void" }
  | "long"   { TYPE "long" }
  | "short"  { TYPE "short" }
  | "float"  { TYPE "float" }
  | "double" { TYPE "double" }

  (* IMPORTANT:
     recognize "&&   Term" as one token to avoid parser conflicts *)
  | "&&" [' ' '\t' '\r' '\n']* "Term" { TERM_AND }

  (* standalone keyword (still needed e.g. case branches) *)
  | "Term" { TERM }

  (* arrows / implications *)
  | "=>"   { IMPLIES }
  | "->"   { ARROW }

  (* SL conjunction *)
  | "/\\"  { SL_CONJ }

  (* boolean and comparison ops *)
  | "&&"   { AND }
  | "=="   { EQEQ }
  | "!="   { NEQ }
  | ">="   { GTE }
  | ">"    { GT }
  | "<="   { LTE }
  | "<"    { LT }

  (* arithmetic *)
  | "+"    { PLUS }
  | "-"    { MINUS }
  | "*"    { STAR }
  | "/"    { DIV }

  (* old / prime *)
  | "\\old" { OLD }
  | "'"     { PRIME }

  (* punctuation *)
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | ";" { SEMICOLON }

  (* literals *)
  | digits as n { INT (int_of_string n) }

  (* identifiers *)
  | ident as s { ID s }

  | eof { EOF }

  | _ as c
      { failwith (Printf.sprintf "Unexpected character: %c" c) }
