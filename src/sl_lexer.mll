{
open Sl_parser
}

let whitespace = [' ' '\t' '\r' '\n']+
let ident      = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
  | whitespace { token lexbuf }
  | "req" { REQ }
  | "ens" { ENS }
  | "int" { INT }
  | "->" { ARROW }
  | "&&" { AND }
  | '*' { STAR }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ';' { SEMICOLON }
  | ident { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _  {failwith ("Unknown character: " ^ Lexing.lexeme lexbuf)}