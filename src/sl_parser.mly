%{
  open Sl_ast
%}

%token REQ ENS CASE TERM /* req ens case Term */
%token ARROW /* -> */
%token STAR/* * */
%token AND SL_CONJ   /* &&      /\ */
%token EQEQ NEQ GTE GT LTE LT /* == != >= > <= <   */
%token PRIME   /* '  */
%token OLD  /* \old */
%token LPAREN RPAREN  /* ( ) */
%token LBRACE RBRACE /* { } */
%token LBRACK RBRACK  /* [ ] */
%token SEMICOLON   /* ; */
%token IMPLIES /* => */
%token EOF
%token <int>    INT
%token <string> ID  /* a, u, i, ... */
%token <string> TYPE  /* int, char, ... */
%token MINUS   /* -  */

%start <Sl_ast.spec> main

%left AND
%left MINUS

%%

main:
  | spec EOF { $1 }

spec:
  | REQ heap SEMICOLON ENS heap SEMICOLON
      { Simple { pre = $2; post = $5 } }
  | ENS sugar_prime SEMICOLON
      { Sugar_prime $2 }
  | ENS sugar_old SEMICOLON
      { Sugar_old $2 }
  | CASE LBRACE case_list RBRACE SEMICOLON
      { Case $3 }
  | loop_clause SL_CONJ loop_clause_list
      { Case ($1 :: $3) }


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


arith_expr:
  | ID
      { A_var $1 }
  | ID PRIME
      { A_post_var $1 }
  | OLD LPAREN arith_expr RPAREN
      { A_old $3 }
  | INT
      { A_int $1 }
  | arith_expr MINUS arith_expr
      { A_sub ($1, $3) }
  | LPAREN arith_expr RPAREN
      { $2 }

conditional_expr:
  | arith_expr EQEQ arith_expr
      { E_eq ($1, $3) }
  | arith_expr NEQ arith_expr
      { E_neq ($1, $3) }
  | arith_expr LTE arith_expr
      { E_lte ($1, $3) }
  | arith_expr LT arith_expr
      { E_lt ($1, $3) }
  | arith_expr GTE arith_expr
      { E_gte ($1, $3) }
  | arith_expr GT arith_expr
      { E_gt ($1, $3) }


post_kind:
  | heap
      { Post_heap $1 }
  | conditional_expr
      { Post_expr $1 }


case:
  | conditional_expr IMPLIES
      REQ heap SEMICOLON
      ENS post_kind SEMICOLON
      {
        {
          test = $1;
          term = None;
          pre  = $4;
          post = $7;
        }
      }

  | conditional_expr IMPLIES
      REQ TERM LBRACK arith_expr RBRACK SEMICOLON
      ENS post_kind SEMICOLON
      {
        {
          test = $1;
          term = Some (Term $6);
          pre  = Atom (PointTo ("_", "int", "_"));
          post = $10;
        }
      }

  | conditional_expr IMPLIES
      REQ TERM LBRACK RBRACK SEMICOLON
      ENS post_kind SEMICOLON
      {
        {
          test = $1;
          term = Some Term_none;
          pre  = Atom (PointTo ("_", "int", "_"));
          post = $9;
        }
      }

case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }

loop_req:
  | conditional_expr AND TERM LBRACK arith_expr RBRACK
      { ($1, Some (Term $5)) }
  | conditional_expr AND TERM LBRACK RBRACK
      { ($1, Some Term_none) }

loop_clause:
  | REQ loop_req SEMICOLON ENS conditional_expr SEMICOLON
      {
        let (cond, term_opt) = $2 in
        {
          test = cond;
          term = term_opt;
          pre  = Atom (PointTo ("_", "int", "_"));
          post = Post_expr $5;
        }
      }

loop_clause_list:
  | loop_clause
      { [$1] }
  | loop_clause SL_CONJ loop_clause_list
      { $1 :: $3 }