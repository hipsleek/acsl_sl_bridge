%{
  open Ast
%}

%token REQ ENS /* req ens*/
%token ARROW /* -> */
%token INT /* int */
%token STAR /* * */
%token AND /* && */
%token LPAREN RPAREN /* (    ) */
%token SEMICOLON /* ; */
%token EOF
%token <string> ID /* a, u ,.. .*/

%start <Ast.spec> main

%%

main:
  | spec EOF { $1 }

spec:
  | REQ heap SEMICOLON ENS heap SEMICOLON
      { { pre = $2; post = $5 } }

heap:
  | atom
      { Atom $1 }
  | heap AND heap
      { Sep ($1, $3) }

atom:
  | ID ARROW INT STAR LPAREN ID RPAREN
      { PointTo ($1, $6) }

