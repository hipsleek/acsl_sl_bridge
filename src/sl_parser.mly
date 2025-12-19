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

%token <int> INT
%token <string> ID
%token <string> TYPE

%start <Sl_ast.spec> main
 %right IMPLIES
%left AND
%left STAR
%left PLUS MINUS
%left TIMES DIV
%%

main:
  | spec EOF { $1 }
 spec:
  
  | REQ sl SEMICOLON ENS sl SEMICOLON
      {
        {
          ret = None;
          behaviors = [
            { name = None; assumes = STrue; body = [ CReq $2; CEns $5 ] }
          ];
        }
      }

  
  | ens_clause
      {
        let (ret_opt, post) = $1 in
        {
          ret = ret_opt;
          behaviors = [
            { name = None; assumes = STrue; body = [ CEns post ] }
          ];
        }
      }

  
  | CASE LBRACE case_list RBRACE SEMICOLON
      { { ret = None; behaviors = $3 } }

  
  | loop_clause
      { { ret = None; behaviors = [ $1 ] } }

  | loop_clause SL_CONJ loop_clause_list
      { { ret = None; behaviors = $1 :: $3 } }
 ens_clause:
  | ENS sl SEMICOLON
      { (None, $2) }

  | ENS LBRACK ID RBRACK sl SEMICOLON
      { (Some $3, $5) }
 sl:
  | sl IMPLIES sl
      { SImplies ($1, $3) }

  | sl AND sl
      { SAnd [$1; $3] }

  | sl STAR sl
      { SSep [$1; $3] }

  | sl_atom
      { $1 }

sl_atom:
  | heap_atom
      { SHeap $1 }

  | cmp_sl { $1 }

  | sugar_prime_sl
      { $1 }

  | sugar_old_sl
      { $1 }

  | ID
      {
        if $1 = "emp" then SEmp
        else failwith ("Unexpected bare identifier in sl: " ^ $1)
      }

  | LPAREN sl RPAREN
      { $2 }
 heap_atom:
  
  | ID ARROW TYPE STAR LPAREN ID RPAREN
      { HPt { loc = EVar $1; ty = $3; value = EVar $6 } }

  
  | ID ARROW TYPE STAR LPAREN expr RPAREN
      { HPt { loc = EVar $1; ty = $3; value = $6 } }
 cmp_sl:
  | expr cmp_op expr
      { SPure (EBinop ($2, $1, $3)) }

  | expr cmp_op expr cmp_op expr
      { SAnd [
          SPure (EBinop ($2, $1, $3));
          SPure (EBinop ($4, $3, $5));
        ]
      }

cmp_op:
  | EQEQ { BEq }
  | NEQ { BNeq }
  | LT { BLt }
  | LTE { BLe }
  | GT { BGt }
  | GTE { BGe }
 expr:
  | ID
      {
        if $1 = "\\result" then EResult else EVar $1
      }

  | ID PRIME
      { EPost (EVar $1) }

  | OLD LPAREN expr RPAREN
      { EOld $3 }

  | INT
      { EConstInt $1 }

  | expr PLUS expr
      { EBinop (BAdd, $1, $3) }

  | expr MINUS expr
      { EBinop (BSub, $1, $3) }

  | expr TIMES expr
      { EBinop (BMul, $1, $3) }

  | expr DIV expr
      { EBinop (BDiv, $1, $3) }

  | LPAREN expr RPAREN
      { $2 }
 sugar_prime_sl:
  | sugar_prime
      {
        
        match $1 with
        | [] -> STrue
        | [p] -> p
        | ps -> SAnd ps
      }

sugar_prime:
  | sugar_atom_prime
      { [$1] }
  | sugar_atom_prime AND sugar_prime
      { $1 :: $3 }

sugar_atom_prime:
  | LPAREN STAR ID RPAREN PRIME EQEQ LPAREN TIMES ID RPAREN
      {
        let lhs = EPost (EDeref (EVar $3)) in
        let rhs = EDeref (EVar $9) in
        SPure (EBinop (BEq, lhs, rhs))
      }

sugar_old_sl:
  | sugar_old
      {
        match $1 with
        | [] -> STrue
        | [p] -> p
        | ps -> SAnd ps
      }

sugar_old:
  | sugar_atom_old
      { [$1] }
  | sugar_atom_old AND sugar_old
      { $1 :: $3 }

sugar_atom_old:
  | LPAREN STAR ID RPAREN EQEQ OLD LPAREN TIMES ID RPAREN
      {
        let lhs = EDeref (EVar $3) in
        let rhs = EOld (EDeref (EVar $9)) in
        SPure (EBinop (BEq, lhs, rhs))
      }
 case:
  
  | sl IMPLIES REQ sl SEMICOLON ens_clause
      {
        let (_ret_opt, post) = $6 in
        { name = None; assumes = $1; body = [ CReq $4; CEns post ] }
      }

  
  | sl IMPLIES REQ TERM LBRACK expr RBRACK SEMICOLON ens_clause
      {
        (* RHS symbols:
           1:sl 2:IMPLIES 3:REQ 4:TERM 5:LBRACK 6:expr 7:RBRACK 8:SEMICOLON 9:ens_clause *)
        let (_ret_opt, post) = $9 in
        { name = None; assumes = $1; body = [ CVar (Some $6); CEns post ] }
      }

  
  | sl IMPLIES REQ TERM LBRACK RBRACK SEMICOLON ens_clause
      {
        (* RHS symbols:
           1:sl 2:IMPLIES 3:REQ 4:TERM 5:LBRACK 6:RBRACK 7:SEMICOLON 8:ens_clause *)
        let (_ret_opt, post) = $8 in
        { name = None; assumes = $1; body = [ CVar None; CEns post ] }
      }
 case_list:
  | case
      { [$1] }
  | case case_list
      { $1 :: $2 }
 loop_req:
  | cmp_expr AND TERM LBRACK expr RBRACK
      { (SPure $1, Some $5) }
  | cmp_expr AND TERM LBRACK RBRACK
      { (SPure $1, None) }

cmp_expr:
  | expr cmp_op expr
      { EBinop ($2, $1, $3) }
 loop_clause:
  | REQ loop_req SEMICOLON ens_clause
      {
        let (assumes_sl, var_opt) = $2 in
        let (_ret_opt, post) = $4 in
        { name = None; assumes = assumes_sl; body = [ CVar var_opt; CEns post ] }
      }

loop_clause_list:
  | loop_clause
      { [$1] }
  | loop_clause SL_CONJ loop_clause_list
      { $1 :: $3 }
