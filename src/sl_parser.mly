%{
  open Sl_ast
%}

%token REQ ENS CASE TERM/* req ens case term*/
%token ARROW /* -> */
%token STAR /* * */
%token AND /* && */
%token EQEQ NEQ GTE GT LTE LT /* == */
%token PRIME /* ' */
%token OLD /*  \old */
%token LPAREN RPAREN /* (    ) */
%token LBRACE RBRACE /* {    } */
%token LBRACK RBRACK /* [    ] */
%token SEMICOLON /* ; */
%token IMPLIES /* => */
%token EOF
%token <int> INT
%token <string> ID /* a, u ,.. .*/
%token <string> TYPE /* int, char ,.. .*/

%start <Sl_ast.spec> main

%%

main:
  | spec EOF { $1 }

spec:
  | REQ heap SEMICOLON ENS heap SEMICOLON
      { Simple { pre = $2; post = $5 } }
  | ENS sugar_prime SEMICOLON
      { Sl_ast.spec_of_pointer_pairs $2 }
  | ENS sugar_old SEMICOLON
      { Sl_ast.spec_of_pointer_pairs $2 }
  | CASE LBRACE case_list RBRACE SEMICOLON
      { Case $3 }
  | CASE LBRACE loop_case_list RBRACE SEMICOLON
      { Loop $3 }

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
  | ID EQEQ ID
      { E_eq (E_ptr $1, E_ptr $3) }
  | ID NEQ ID
      { E_neq (E_ptr $1, E_ptr $3) }
  | ID LTE ID
      { E_lte (E_ptr $1, E_ptr $3) }
  | ID LT ID
      { E_lt (E_ptr $1, E_ptr $3) }
  | ID GTE ID
      { E_gte (E_ptr $1, E_ptr $3) }
  | ID GT ID
      { E_gt (E_ptr $1, E_ptr $3) }

case:
  | conditional_expr IMPLIES REQ heap SEMICOLON ENS heap SEMICOLON
      { { test = $1; pre = $4; post = $7 } }

case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }



loop_int_expr:
  | ID { Lvar $1 }
  | INT { Lconst $1 }

loop_conditional_expr:
  | loop_int_expr EQEQ loop_int_expr
      { L_eq ($1, $3) }
  | loop_int_expr NEQ loop_int_expr
      { L_neq ($1, $3) }
  | loop_int_expr LTE loop_int_expr
      { L_lte ($1, $3) }
  | loop_int_expr LT loop_int_expr
      { L_lt ($1, $3) }
  | loop_int_expr GTE loop_int_expr
      { L_gte ($1, $3) }
  | loop_int_expr GT loop_int_expr
      { L_gt ($1, $3) }

term_expression:
  | TERM LBRACK loop_int_expr RBRACK
      { Terminate_expr $3 }
  | TERM LBRACK RBRACK
      { Terminate_empty }


loop_case:
  | loop_conditional_expr IMPLIES REQ term_expression SEMICOLON ENS loop_conditional_expr SEMICOLON
      { { loop_test = $1; loop_requirement = $4; loop_gurantee = $7; } }

loop_case_list:
  | loop_case 
      { [$1] }
  | loop_case loop_case_list 
      { $1 :: $2 }
