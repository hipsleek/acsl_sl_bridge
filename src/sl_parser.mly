%{
  open Ast
%}

%token REQ ENS /* req ens*/
%token ARROW /* -> */
// %token INT /* int */
// %token CHAR /* char */ (*MORE WILL BE ADDED INCREMENTALLY IN FUTURE.*)
%token STAR /* * */
%token AND /* && */
%token LPAREN RPAREN /* (    ) */
%token SEMICOLON /* ; */
%token EOF
%token <string> ID /* a, u ,.. .*/
%token <string> TYPE /* int, char ,.. .*/

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
  | ID ARROW TYPE STAR LPAREN ID RPAREN
      { PointTo ($1, $3, $6) }

