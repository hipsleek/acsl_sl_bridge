%{
  open Acsl_ast
%}

%token ANNOT_START ANNOT_END

%token REQUIRES ASSIGNS ENSURES
%token BEHAVIOR ASSUMES COMPLETE DISJOINT BEHAVIORS

%token LOOP INVARIANT VARIANT

%token VALID VALID_READ OLD AT
%token TRUE FALSE NOTHING RESULT NULL

%token FORALL EXISTS

%token EQEQ NEQ GTE GT LTE LT
%token PLUS MINUS DIV
%token NOT
%token STAR

%token AND OR
%token IMPLIES
%token IFF

%token DOTDOT
%token DOT COMMA COLON
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LBRACK RBRACK
%token SEMICOLON
%token EOF

%token <int> INT
%token <string> ID
%token <string> TYPE

%start <Acsl_ast.spec> main

%right IFF
%right IMPLIES
%left OR
%left AND
%left EQEQ NEQ LT LTE GT GTE
%left PLUS MINUS
%left STAR DIV
%right NOT
%right UMINUS USTAR

%%

main:
  | ANNOT_START top ANNOT_END EOF { $2 }

top:
  | function_spec { $1 }
  | loop_spec { $1 }

function_spec:
  | requires_opt assigns_clause fun_body
      { mk_fun_spec ~requires:$1 ~assigns:$2 ~body:$3 }

requires_opt:
  | REQUIRES pred SEMICOLON { Some $2 }
  | { None }

assigns_clause:
  | ASSIGNS assigns SEMICOLON { $2 }

fun_body:
  | ENSURES pred SEMICOLON
      { FunEnsures $2 }

  | behavior_list complete_disjoint_opt
      { FunBehaviors ($1, $2) }

complete_disjoint_opt:
  | COMPLETE BEHAVIORS SEMICOLON DISJOINT BEHAVIORS SEMICOLON { (true, true) }
  | COMPLETE BEHAVIORS SEMICOLON { (true, false) }
  | DISJOINT BEHAVIORS SEMICOLON { (false, true) }
  | { (false, false) }

behavior_list:
  | behavior { [$1] }
  | behavior behavior_list { $1 :: $2 }

behavior:
  | BEHAVIOR ID COLON behavior_body
      { mk_behavior ~name:$2 ~body:$4 }

behavior_body:
  | assumes_clause ensures_clause
      { ($1, $2) }

assumes_clause:
  | ASSUMES pred SEMICOLON { $2 }

ensures_clause:
  | ENSURES pred SEMICOLON { $2 }

loop_spec:
  | loop_inv_list loop_assigns_clause loop_variant_clause
      { mk_loop_spec ~invariants:$1 ~assigns:$2 ~variant:$3 }

loop_inv_list:
  | loop_invariant { [$1] }
  | loop_invariant loop_inv_list { $1 :: $2 }

loop_invariant:
  | LOOP INVARIANT pred SEMICOLON { $3 }

loop_assigns_clause:
  | LOOP ASSIGNS assigns SEMICOLON { $3 }

loop_variant_clause:
  | LOOP VARIANT expr SEMICOLON { $3 }

assigns:
  | NOTHING { AssignNothing }
  | assign_item_list { AssignItems $1 }

assign_item_list:
  | assign_item { [$1] }
  | assign_item COMMA assign_item_list { $1 :: $3 }

assign_item:
  | STAR expr %prec USTAR
      { AWrite (ADeref $2) }

  | ID
      { AWrite (AVar $1) }

  | ID LBRACK LPAREN expr DOTDOT expr RPAREN RBRACK
      { AWrite (ARange (EVar $1, $4, $6)) }

pred:
  | TRUE { PTrue }
  | FALSE { PFalse }
  | LPAREN pred RPAREN { $2 }

  | pred IFF pred
      { PAnd [PImplies ($1, $3); PImplies ($3, $1)] }

  | pred IMPLIES pred
      { PImplies ($1, $3) }

  | pred OR pred
      { POr [$1; $3] }

  | pred AND pred
      { PAnd [$1; $3] }

  | NOT pred
      { PNot $2 }

  | FORALL binder SEMICOLON pred
      { PForall ([$2], $4) }

  | EXISTS binder SEMICOLON pred
      { PExists ([$2], $4) }

  | VALID LPAREN expr RPAREN
      { PValid $3 }

  | VALID_READ LPAREN expr RPAREN
      { PValidRead $3 }

  | expr cmp_op expr
      { PCmp ($2, $1, $3) }

  | expr cmp_op expr cmp_op expr
      { PAnd [PCmp ($2, $1, $3); PCmp ($4, $3, $5)] }

binder:
  | TYPE ID { ($2, Some (TUser $1)) }
  | ID { ($1, None) }

cmp_op:
  | EQEQ { CEq }
  | NEQ { CNeq }
  | LT { CLt }
  | LTE { CLe }
  | GT { CGt }
  | GTE { CGe }

expr:
  | RESULT { EResult }
  | NULL { ENull }
  | INT { EConstInt $1 }
  | ID { EVar $1 }
  | LPAREN expr RPAREN   { $2 }

  | OLD LPAREN expr RPAREN
      { EOld $3 }

  | AT LPAREN expr COMMA ID RPAREN
      { EAt ($3, $5) }

  | STAR expr %prec USTAR
      { EDeref $2 }

  | MINUS expr %prec UMINUS
      { EUnop (UNeg, $2) }

  | expr PLUS expr
      { EBinop (BAdd, $1, $3) }

  | expr MINUS expr
      { EBinop (BSub, $1, $3) }

  | expr STAR expr
      { EBinop (BMul, $1, $3) }

  | expr DIV expr
      { EBinop (BDiv, $1, $3) }

  | expr LBRACK expr RBRACK
      { EIndex ($1, $3) }
