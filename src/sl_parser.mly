%{
  open Ast
%}

%token REQ ENS /* req ens*/
%token ARROW /* -> */
// %token INT /* int */
// %token CHAR /* char */ (*MORE WILL BE ADDED INCREMENTALLY IN FUTURE.*)
%token STAR /* * */
%token AND /* && */
%token EQEQ /* == */
%token NEQ /* != */
%token GTE /* >= */
%token GT /* > */
%token LTE /* <= */
%token LT /* < */
%token PRIME /* ' */
%token OLD /*  \old */
%token LPAREN RPAREN /* (    ) */
%token CASE /* case */
%token LBRACE RBRACE /* {    } */
%token SEMICOLON /* ; */
%token IMPLIES /* => */
%token EOF
%token <string> ID /* a, u ,.. .*/
%token <string> TYPE /* int, char ,.. .*/

%start <Ast.spec> main

%%

main:
  | spec EOF { $1 }

spec:
  | REQ heap SEMICOLON ENS heap SEMICOLON
      { Simple { pre = $2; post = $5 } }
  | ENS sugar_prime SEMICOLON
      { Ast.spec_of_pointer_pairs $2 }
  | ENS sugar_old SEMICOLON
      { Ast.spec_of_pointer_pairs $2 }
  | CASE LBRACE case_list RBRACE
      { Case $3 }

heap:
  | atom
      { Atom $1 }
  | heap AND heap
      { Sep ($1, $3) }

atom:
  | ID ARROW TYPE STAR LPAREN ID RPAREN
      { PointTo ($1, $3, $6) }

sugar_prime:
  | sugar_atom_prime
      { [$1] }
  | sugar_atom_prime AND sugar_prime
      { $1 :: $3 }

sugar_atom_prime:
  | LPAREN STAR ID RPAREN PRIME EQEQ LPAREN STAR ID RPAREN
      { ($3, $9) }

sugar_old:
  | sugar_atom_old
      { [$1] }
  | sugar_atom_old AND sugar_old
      { $1 :: $3 }

sugar_atom_old:
  | LPAREN STAR ID RPAREN EQEQ OLD LPAREN STAR ID RPAREN
      { ($3, $9) }

conditional_expr:
  | ID
      { E_ptr $1 }
  | ID EQEQ ID
      { E_eq (E_ptr $1, E_ptr $3) }
  | ID NEQ ID
      { E_neq (E_ptr $1, E_ptr $3) }
      (*Add more to grammar here*)

case:
  | conditional_expr IMPLIES REQ heap SEMICOLON ENS heap SEMICOLON
      { { test = $1; pre = $4; post = $7 } }

case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }
