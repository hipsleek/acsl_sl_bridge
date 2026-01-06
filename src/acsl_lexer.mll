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

  | "\\valid_read" { VALID_READ }
  | "\\valid"      { VALID }
  | "\\old"        { OLD }
  | "\\at"         { AT }

  | "\\true"  { TRUE }
  | "\\false" { FALSE }
  | "\\nothing" { NOTHING }

  | "\\forall" { FORALL }
  | "\\exists" { EXISTS }

  | "\\result" { RESULT }
  | "NULL"     { NULL }

  | "integer" { TYPE "integer" }
  | "size_t"  { TYPE "size_t" }
  | "int"     { TYPE "int" }
  | "char"    { TYPE "char" }
  | "bool"    { TYPE "bool" }
  | "void"    { TYPE "void" }
  | "long"    { TYPE "long" }
  | "short"   { TYPE "short" }
  | "float"   { TYPE "float" }
  | "double"  { TYPE "double" }

  | "<==>" { IFF }
  | "==>"  { IMPLIES }

  | "&&"   { AND }
  | "||"   { OR }

  | "=="   { EQEQ }
  | "!="   { NEQ }
  | ">="   { GTE }
  | ">"    { GT }
  | "<="   { LTE }
  | "<"    { LT }

  | ".."   { DOTDOT }

  | "+"    { PLUS }
  | "-"    { MINUS }
  | "*"    { STAR }
  | "/"    { DIV }
  | "!"    { NOT }

  | "."    { DOT }
  | ","    { COMMA }
  | ":"    { COLON }

  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | ";" { SEMICOLON }

  | digits as n { INT (int_of_string n) }
  | ident as s  { ID s }

  | eof { EOF }

  | _ as c
      { failwith (Printf.sprintf "Unexpected character: %c" c) }
