{
open Sl_parser
}

let whitespace = [' ' '\t' '\r' '\n']+
let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let digits = ['0'-'9']+

rule token = parse
  | whitespace { token lexbuf }
  | "req" { REQ }
  | "ens" { ENS }
  | "case" { CASE }
  | "Term" { TERM }
  | "\\old" { OLD }
  | "->" { ARROW }
  | "=>" { IMPLIES }
  | "&&" { AND }
  | "/\\" { SL_CONJ }
  | "==" { EQEQ }
  | "!=" { NEQ }
  | ">=" { GTE }
  | "<=" { LTE }
  | "**" { STAR }          
  | ">" { GT }
  | "<" { LT }
  | '\'' { PRIME }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACK }
  | ']' { RBRACK }
  | ';' { SEMICOLON }
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }          
  | '/' { DIV }
  | "int" { TYPE "int" }
  | "char" { TYPE "char" }
  | digits as d { INT (int_of_string d) }
  | ident as s { ID s }
  | eof { EOF }
  | _ as c
      { failwith ("Unknown character: " ^ String.make 1 c) }
