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

  | "req"  { REQ }
  | "ens"  { ENS }
  | "case" { CASE }

  | "int"    { TYPE "int" }
  | "char"   { TYPE "char" }
  | "bool"   { TYPE "bool" }
  | "void"   { TYPE "void" }
  | "long"   { TYPE "long" }
  | "short"  { TYPE "short" }
  | "float"  { TYPE "float" }
  | "double" { TYPE "double" }

  (* Allow the sugar used in loop_req: "... && Term[...]" *)
  | "&&" [' ' '\t' '\r' '\n']* "Term" { TERM_AND }
  | "Term" { TERM }

  (* ---------- Backslash keywords / atoms ---------- *)
  | "\\old"    { OLD }
  | "\\forall" { FORALL }
  | "\\exists" { EXISTS }
  | "\\return" { RETURN }
  (* IMPORTANT: treat \result as an ID so parser's expr rule can map it to EResult *)
  | "\\result" { ID "\\result" }

  (* Accept both implication spellings: => and ==> *)
  | "==>"  { IMPLIES }
  | "=>"   { IMPLIES }

  | "->"   { ARROW }
  | "/\\"  { SL_CONJ }

  | "&&"   { AND }
  | "||"   { OR }

  | "=="   { EQEQ }
  | "!="   { NEQ }
  | ">="   { GTE }
  | ">"    { GT }
  | "<="   { LTE }
  | "<"    { LT }

  | "+"    { PLUS }
  | "-"    { MINUS }
  | "*"    { STAR }
  | "/"    { DIV }

  | "'"    { PRIME }
  | "."    { DOT }
  | ","    { COMMA }

  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | ";" { SEMICOLON }

  | digits as n { INT (int_of_string n) }
  | ident as s { ID s }

  | eof { EOF }

  | _ as c
      { failwith (Printf.sprintf "Unexpected character: %c" c) }