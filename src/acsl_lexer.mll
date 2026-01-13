{
  open Acsl_parser
}

let whitespace = [' ' '\t' '\r' '\n']+
let digits = ['0'-'9']+
let ident_start = ['a'-'z' 'A'-'Z' '_']
let ident_char  = ['a'-'z' 'A'-'Z' '0'-'9' '_']
let ident = ident_start ident_char*

rule token = parse
  | whitespace { token lexbuf }

  | "/*@" { ANNOT_START }
  | "*/"  { ANNOT_END }

  | "requires" { REQUIRES }
  | "assigns"  { ASSIGNS }
  | "ensures"  { ENSURES }

  | "behavior" { BEHAVIOR }
  | "assumes"  { ASSUMES }
  | "complete" { COMPLETE }
  | "disjoint" { DISJOINT }
  | "behaviors" { BEHAVIORS }

  | "loop"      { LOOP }
  | "invariant" { INVARIANT }
  | "variant"   { VARIANT }

  | "\\valid"      { VALID }
  | "\\valid_read" { VALID_READ }
  | "\\old"        { OLD }
  | "\\at"         { AT }

  | "\\true"   { TRUE }
  | "\\false"  { FALSE }
  | "\\nothing" { NOTHING }
  | "\\result" { RESULT }
  | "NULL"     { NULL }

  | "\\forall" { FORALL }
  | "\\exists" { EXISTS }

  | "<==>" { IFF }
  | "==>"  { IMPLIES }
  | "&&"   { AND }
  | "||"   { OR }

  | "==" { EQEQ }
  | "!=" { NEQ }
  | ">=" { GTE }
  | ">"  { GT }
  | "<=" { LTE }
  | "<"  { LT }

  | ".." { DOTDOT }
  | "+"  { PLUS }
  | "-"  { MINUS }
  | "*"  { STAR }
  | "/"  { DIV }
  | "!"  { NOT }

  | "." { DOT }
  | "," { COMMA }
  | ":" { COLON }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | ";" { SEMICOLON }

  | ("int" | "integer" | "bool" | "boolean" | "ptr") as t { TYPE t }

  | digits as n { INT (int_of_string n) }
  | ident as s  { ID s }

  | eof { EOF }

  | _ as c
      { failwith (Printf.sprintf "Unexpected character in ACSL lexer: %c" c) }
