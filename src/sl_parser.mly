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

  | ens_clause
      { Ens $1 }

  | CASE LBRACE case_list RBRACE SEMICOLON
      { Case $3 }

  | loop_clause
      { Case [ $1 ] }

  | loop_clause SL_CONJ loop_clause_list
      { Case ($1 :: $3) }

(* ---------- Ens clause ---------- *)

ens_clause:
  | ENS assertion SEMICOLON
      { { ret = None; post = $2 } }

  | ENS LBRACK ID RBRACK assertion SEMICOLON
      { { ret = Some $3; post = $5 } }

(* ---------- Assertions ---------- *)

assertion:
  | assertion IMPLIES assertion
      { AImplies ($1, $3) }

  | assertion AND assertion
      { AAnd ($1, $3) }

  | assertion STAR assertion
      { ASep ($1, $3) }

  | assertion_atom
      { $1 }

assertion_atom:
  | heap_atom
      { AHeapAtom $1 }

  | chain_cmp
      { $1 }

  | pure_atom
      { APure $1 }

  | sugar_prime_assertion
      { $1 }

  | sugar_old_assertion
      { $1 }

  | ID
      {
        if $1 = "emp" then AEmp
        else failwith ("Unexpected bare identifier in assertion: " ^ $1)
      }

  | LPAREN assertion RPAREN
      { $2 }

(* ---------- Heap atoms ---------- *)

heap_atom:
  | ID ARROW TYPE STAR LPAREN ID RPAREN
      { PointTo ($1, $3, $6) }

(* ---------- Chained comparisons ---------- *)

chain_cmp:
  | arith_expr LT  arith_expr LT  arith_expr
      { AAnd (APure (PLt  ($1, $3)), APure (PLt  ($3, $5))) }

  | arith_expr LT  arith_expr LTE arith_expr
      { AAnd (APure (PLt  ($1, $3)), APure (PLte ($3, $5))) }

  | arith_expr LTE arith_expr LT  arith_expr
      { AAnd (APure (PLte ($1, $3)), APure (PLt  ($3, $5))) }

  | arith_expr LTE arith_expr LTE arith_expr
      { AAnd (APure (PLte ($1, $3)), APure (PLte ($3, $5))) }

  | arith_expr GT  arith_expr GT  arith_expr
      { AAnd (APure (PGt  ($1, $3)), APure (PGt  ($3, $5))) }

  | arith_expr GT  arith_expr GTE arith_expr
      { AAnd (APure (PGt  ($1, $3)), APure (PGte ($3, $5))) }

  | arith_expr GTE arith_expr GT  arith_expr
      { AAnd (APure (PGte ($1, $3)), APure (PGt  ($3, $5))) }

  | arith_expr GTE arith_expr GTE arith_expr
      { AAnd (APure (PGte ($1, $3)), APure (PGte ($3, $5))) }

(* ---------- Pure atoms ---------- *)

pure_atom:
  | arith_expr EQEQ arith_expr { PEq  ($1, $3) }
  | arith_expr NEQ  arith_expr { PNeq ($1, $3) }
  | arith_expr LTE  arith_expr { PLte ($1, $3) }
  | arith_expr LT   arith_expr { PLt  ($1, $3) }
  | arith_expr GTE  arith_expr { PGte ($1, $3) }
  | arith_expr GT   arith_expr { PGt  ($1, $3) }

(* ---------- Arithmetic ---------- *)

arith_expr:
  | ID
      { AVar $1 }

  | ID PRIME
      { APostVar $1 }

  | OLD LPAREN arith_expr RPAREN
      { AOld $3 }

  | INT
      { AInt $1 }

  | arith_expr PLUS  arith_expr
      { AAdd ($1, $3) }

  | arith_expr MINUS arith_expr
      { ASub ($1, $3) }

  | arith_expr TIMES arith_expr
      { AMul ($1, $3) }

  | arith_expr DIV   arith_expr
      { ADiv ($1, $3) }

  | LPAREN arith_expr RPAREN
      { $2 }

(* ---------- Sugar assertions ---------- *)

sugar_prime_assertion:
  | sugar_prime
      { ASugarPrime $1 }

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
      { ASugarOld $1 }

sugar_old:
  | sugar_atom_old
      { [$1] }
  | sugar_atom_old AND sugar_old
      { $1 :: $3 }

sugar_atom_old:
  | LPAREN STAR ID RPAREN EQEQ OLD LPAREN STAR ID RPAREN
      { ($3, $9) }

(* ---------- Case clauses ---------- *)

case:
  | assertion IMPLIES
      REQ assertion SEMICOLON
      ens_clause
      {
        {
          test = $1;
          term = None;
          pre  = $4;
          post = $6.post;
        }
      }

  | assertion IMPLIES
      REQ TERM LBRACK arith_expr RBRACK SEMICOLON
      ens_clause
      {
        {
          test = $1;
          term = Some (Term $6);
          pre  = AEmp;
          post = $9.post;
        }
      }

  | assertion IMPLIES
      REQ TERM LBRACK RBRACK SEMICOLON
      ens_clause
      {
        {
          test = $1;
          term = Some TermNone;
          pre  = AEmp;
          post = $8.post;
        }
      }

case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }

(* ---------- Loop sugar ---------- *)

loop_req:
  | pure_atom AND TERM LBRACK arith_expr RBRACK
      { (APure $1, Some (Term $5)) }

  | pure_atom AND TERM LBRACK RBRACK
      { (APure $1, Some TermNone) }

loop_clause:
  | REQ loop_req SEMICOLON ens_clause
      {
        let (cond, term_opt) = $2 in
        {
          test = cond;
          term = term_opt;
          pre  = AEmp;
          post = $4.post;
        }
      }

loop_clause_list:
  | loop_clause
      { [$1] }
  | loop_clause SL_CONJ loop_clause_list
      { $1 :: $3 }
