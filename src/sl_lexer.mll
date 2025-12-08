{
open Sl_parser
}

let whitespace = [' ' '\t' '\r' '\n']+
let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | whitespace { token lexbuf }
  | "req" { REQ }
  | "ens" { ENS }
  | "case" {CASE}
  | "->" { ARROW }
  | "&&" { AND }
  | "==" { EQEQ }
  | "!=" { NEQ }
  | ">=" { GTE }
  | ">" { GT }
  | "<=" { LTE }
  | "<" { LT }
  | '\'' { PRIME }
  | "\\old" { OLD }
  | '*' { STAR }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' {LBRACE}
  | '}' {RBRACE}
  | "=>" {IMPLIES}
  | ';' { SEMICOLON }
  | "int" { TYPE "int" }
  | "char" { TYPE "char" } (*Is there better way to do this??*)
  | ident { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _  {failwith ("Unknown character: " ^ Lexing.lexeme lexbuf)}