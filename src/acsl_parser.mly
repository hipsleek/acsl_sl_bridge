%{
  open Acsl_ast

  let sort_of_type (s : string) : sort =
    match s with
    | "int" | "integer" -> SInt
    | "bool" | "boolean" -> SBool
    | "ptr" -> SPtr
    | other -> SUser other
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
  | function_spec { FunSpec $1 }
  | loop_spec     { LoopSpec $1 }

function_spec:
  | requires_opt assigns_clause fun_body
      {
        let (behaviors, ensures_opt, complete_behaviors, disjoint_behaviors) = $3 in
        {
          requires = $1;
          assigns = $2;
          behaviors;
          ensures = ensures_opt;
          complete_behaviors;
          disjoint_behaviors;
        }
      }

requires_opt:
  | REQUIRES pred SEMICOLON { Some $2 }
  |                         { None }

assigns_clause:
  | ASSIGNS assigns SEMICOLON { $2 }

fun_body:
  | ENSURES pred SEMICOLON
      { ([], Some $2, false, false) }

  | behavior_list complete_disjoint_opt
      { ($1, None, fst $2, snd $2) }

complete_disjoint_opt:
  | COMPLETE BEHAVIORS SEMICOLON DISJOINT BEHAVIORS SEMICOLON { (true, true) }
  | COMPLETE BEHAVIORS SEMICOLON                              { (true, false) }
  | DISJOINT BEHAVIORS SEMICOLON                              { (false, true) }
  |                                                          { (false, false) }

behavior_list:
  | behavior                { [$1] }
  | behavior behavior_list  { $1 :: $2 }

behavior:
  | BEHAVIOR ID COLON behavior_body
      {
        let (assumes, ensures) = $4 in
        { name = Some $2; assumes; ensures }
      }

behavior_body:
  | assumes_clause ensures_clause { ($1, $2) }

assumes_clause:
  | ASSUMES pred SEMICOLON { $2 }

ensures_clause:
  | ENSURES pred SEMICOLON { $2 }

loop_spec:
  | loop_items
      {
        let (invs, assigns_opt, variant_opt) = $1 in
        {
          invariants = List.rev invs;
          assigns = (match assigns_opt with None -> ANothing | Some a -> a);
          variant = variant_opt;
        }
      }

loop_items:
  | loop_item loop_items
      {
        let (invs, aopt, vopt) = $2 in
        match $1 with
        | `Inv p   -> (p :: invs, aopt, vopt)
        | `Assign a -> (invs, Some a, vopt)
        | `Var e   -> (invs, aopt, Some e)
      }
  | loop_item
      {
        match $1 with
        | `Inv p    -> ([p], None, None)
        | `Assign a -> ([], Some a, None)
        | `Var e    -> ([], None, Some e)
      }

loop_item:
  | LOOP INVARIANT pred SEMICOLON { `Inv $3 }
  | LOOP ASSIGNS assigns SEMICOLON { `Assign $3 }
  | LOOP VARIANT expr SEMICOLON { `Var $3 }

loop_label:
  | ID
      {
        match $1 with
        | "LoopEntry" -> LoopEntry
        | "LoopCurrent" -> LoopCurrent
        | s -> UserLabel s
      }

assigns:
  | NOTHING          { ANothing }
  | assign_item_list { AItems $1 }

assign_item_list:
  | assign_item                        { [$1] }
  | assign_item COMMA assign_item_list  { $1 :: $3 }

assign_item:
  | STAR expr %prec USTAR
      { ADeref $2 }

  | ID
      { AVar $1 }

  | ID LBRACK LPAREN expr DOTDOT expr RPAREN RBRACK
      { ARange (EVar $1, $4, $6) }

pred:
  | TRUE                 { PTrue }
  | FALSE                { PFalse }
  | LPAREN pred RPAREN   { $2 }

  | pred IFF pred
      { PIff ($1, $3) }

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
      { PAnd [ PCmp ($2, $1, $3); PCmp ($4, $3, $5) ] }

binder:
  | TYPE ID { ($2, Some (sort_of_type $1)) }
  | ID      { ($1, None) }

cmp_op:
  | EQEQ { BEq }
  | NEQ  { BNeq }
  | LT   { BLt }
  | LTE  { BLe }
  | GT   { BGt }
  | GTE  { BGe }

expr:
  | RESULT               { EResult }
  | NULL                 { ENull }
  | INT                  { EConstInt $1 }
  | ID                   { EVar $1 }
  | LPAREN expr RPAREN   { $2 }

  | OLD LPAREN expr RPAREN
      { EOld $3 }

  | AT LPAREN expr COMMA loop_label RPAREN
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

  | LPAREN expr DOTDOT expr RPAREN
      { ERange ($2, $4) }

  | ID LPAREN expr_list_opt RPAREN
      { EApp ($1, $3) }

expr_list_opt:
  |                         { [] }
  | expr_list               { $1 }

expr_list:
  | expr                     { [$1] }
  | expr COMMA expr_list      { $1 :: $3 }
