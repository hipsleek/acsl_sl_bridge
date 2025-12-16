%{
  open Sl_ast
%}

%token REQ ENS CASE TERM
%token ARROW
%token STAR
%token AND SL_CONJ
%token EQEQ NEQ GTE GT LTE LT
%token PLUS MINUS TIMES DIV
%token PRIME
%token OLD
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LBRACK RBRACK
%token SEMICOLON
%token IMPLIES
%token EOF

%token <int>    INT
%token <string> ID
%token <string> TYPE

%start <Sl_ast.spec> main

(* precedence (lowest to highest) *)
%right IMPLIES
%left AND
%left STAR
%left PLUS MINUS
%left TIMES DIV

%%

main:
  | spec EOF { $1 }

spec:
  | REQ assertion SEMICOLON ENS assertion SEMICOLON
      { Simple { pre = $2; post = $5 } }

  (* NEW: top-level ensures-only spec *)
  | ENS assertion SEMICOLON
      { Ens $2 }

  | CASE LBRACE case_list RBRACE SEMICOLON
      { Case $3 }

  (* allow a single loop req/ens pair to desugar into a singleton Case *)
  | loop_clause
      { Case [ $1 ] }

  (* allow multiple loop clauses joined by /\ to desugar into Case list *)
  | loop_clause SL_CONJ loop_clause_list
      { Case ($1 :: $3) }

(* ------------------ Assertions ------------------ *)

assertion:
  | assertion IMPLIES assertion
      { A_implies ($1, $3) }
  | assertion AND assertion
      { A_and ($1, $3) }
  | assertion STAR assertion
      { A_sep ($1, $3) }
  | assertion_atom
      { $1 }

assertion_atom:
  | heap_atom
      { A_heap_atom $1 }
  | pure_atom
      { A_pure $1 }
  | sugar_prime_assertion
      { $1 }
  | sugar_old_assertion
      { $1 }
  | ID
      {
        (* lightweight 'emp' without adding a new token *)
        if $1 = "emp" then A_emp
        else
          failwith ("Unexpected bare identifier in assertion: " ^ $1)
      }
  | LPAREN assertion RPAREN
      { $2 }

(* ------------------ Heap atoms ------------------ *)

heap_atom:
  | ID ARROW TYPE STAR LPAREN ID RPAREN
      { PointTo ($1, $3, $6) }

(* ------------------ Pure atoms ------------------ *)

pure_atom:
  | arith_expr EQEQ arith_expr { P_eq ($1, $3) }
  | arith_expr NEQ  arith_expr { P_neq ($1, $3) }
  | arith_expr LTE  arith_expr { P_lte ($1, $3) }
  | arith_expr LT   arith_expr { P_lt ($1, $3) }
  | arith_expr GTE  arith_expr { P_gte ($1, $3) }
  | arith_expr GT   arith_expr { P_gt ($1, $3) }

arith_expr:
  | ID
      { A_var $1 }
  | ID PRIME
      { A_post_var $1 }
  | OLD LPAREN arith_expr RPAREN
      { A_old $3 }
  | INT
      { A_int $1 }
  | arith_expr PLUS  arith_expr
      { A_add ($1, $3) }
  | arith_expr MINUS arith_expr
      { A_sub ($1, $3) }
  | arith_expr TIMES arith_expr
      { A_mul ($1, $3) }
  | arith_expr DIV   arith_expr
      { A_div ($1, $3) }
  | LPAREN arith_expr RPAREN
      { $2 }

(* ------------------ Sugar assertions ------------------ *)

sugar_prime_assertion:
  | sugar_prime
      { A_sugar_prime $1 }

sugar_prime:
  | sugar_atom_prime
      { [$1] }
  | sugar_atom_prime AND sugar_prime
      { $1 :: $3 }

sugar_atom_prime:
  | LPAREN STAR ID RPAREN PRIME EQEQ LPAREN STAR ID RPAREN
      { ($3, $9) }

sugar_old_assertion:
  | sugar_old
      { A_sugar_old $1 }

sugar_old:
  | sugar_atom_old
      { [$1] }
  | sugar_atom_old AND sugar_old
      { $1 :: $3 }

sugar_atom_old:
  | LPAREN STAR ID RPAREN EQEQ OLD LPAREN STAR ID RPAREN
      { ($3, $9) }

(* ------------------ Case clauses ------------------ *)

case:
  (* Normal case: guard => req <assertion>; ens <assertion>; *)
  | assertion IMPLIES
      REQ assertion SEMICOLON
      ENS assertion SEMICOLON
      {
        {
          test = $1;
          term = None;
          pre  = $4;
          post = $7;
        }
      }

  (* Variant-only req: guard => req Term[e]; ens <assertion>; *)
  | assertion IMPLIES
      REQ TERM LBRACK arith_expr RBRACK SEMICOLON
      ENS assertion SEMICOLON
      {
        {
          test = $1;
          term = Some (Term $6);
          pre  = A_emp;
          post = $10;
        }
      }

  (* Variant-none req: guard => req Term[]; ens <assertion>; *)
  | assertion IMPLIES
      REQ TERM LBRACK RBRACK SEMICOLON
      ENS assertion SEMICOLON
      {
        {
          test = $1;
          term = Some Term_none;
          pre  = A_emp;
          post = $9;
        }
      }

case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }

(* ------------------ Loop sugar into Case ------------------ *)

loop_req:
  | pure_atom AND TERM LBRACK arith_expr RBRACK
      { (A_pure $1, Some (Term $5)) }
  | pure_atom AND TERM LBRACK RBRACK
      { (A_pure $1, Some Term_none) }

loop_clause:
  | REQ loop_req SEMICOLON ENS assertion SEMICOLON
      {
        let (cond_as_assertion, term_opt) = $2 in
        {
          test = cond_as_assertion;
          term = term_opt;
          pre  = A_emp;
          post = $5;
        }
      }

loop_clause_list:
  | loop_clause
      { [$1] }
  | loop_clause SL_CONJ loop_clause_list
      { $1 :: $3 }
