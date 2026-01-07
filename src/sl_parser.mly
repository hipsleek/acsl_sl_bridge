%{
  open Sl_ast
%}

%token REQ ENS CASE TERM
%token TERM_AND
%token ARROW
%token STAR
%token SEPSTAR
%token AND OR SL_CONJ
%token EQEQ NEQ GTE GT LTE LT
%token PLUS MINUS DIV
%token NOT
%token PRIME
%token OLD
%token RETURN
%token RETURN_HASH
%token FORALL EXISTS
%token DOT COMMA COLON AT_I
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LBRACK RBRACK
%token SEMICOLON
%token IMPLIES
%token IFF
%token EOF

%token <int> INT
%token <string> ID
%token <string> TYPE

%start <Sl_ast.spec> main

%right IFF
%right IMPLIES
%left SEPSTAR
%left OR
%left AND SL_CONJ
%left STAR
%left PLUS MINUS
%left DIV

%%

main:
  | spec EOF { $1 }

req_head:
  | sl
      { $1 }
  | sl TERM_AND LBRACK RBRACK
      { $1 }
spec:
  | REQ req_head SEMICOLON ens_clause
    {
      let (ret_opt, post) = $4 in
      {
        ret = ret_opt;
        behaviors = [
          { name = None; assumes = STrue; body = [ CReq $2; CEns post ] }
        ];
      }
    }

  | REQ req_head SEMICOLON CASE LBRACE case_list RBRACE SEMICOLON
    {
      let cases = $6 in
      let ret_opt =
        cases |> List.find_map (fun (_b, r) -> r)
      in
      let global_req = $2 in

      let behaviors =
        cases
        |> List.map (fun ((b : Sl_ast.behavior), r) ->
             let b' = { b with body = (CReq global_req) :: b.body } in
             (b', r))
        |> List.map fst
      in
      { ret = ret_opt; behaviors }
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
    {
      let cases = $3 in
      let ret_opt =
        cases
        |> List.find_map (fun (_b, r) -> r)
      in
      let behaviors = cases |> List.map fst in
      { ret = ret_opt; behaviors }
    }


  | loop_clause_list
      { { ret = None; behaviors = $1 } }

ens_clause:
  | ENS sl SEMICOLON
      { (None, $2) }

  | ENS LBRACK ID RBRACK sl SEMICOLON
      { (Some $3, $5) }


sl:
  | sl IFF sl { SAnd [SImplies($1,$3); SImplies($3,$1)] }
  | sl IMPLIES sl { SImplies ($1, $3) }
  | sl OR sl { SOr [$1; $3] }
  | sl SL_CONJ sl { SAnd [$1; $3] }
  | sl AND sl { SAnd [$1; $3] }
  | sl STAR sl { SSep [$1; $3] }
  | sl SEPSTAR sl { SSep [$1; $3] }
  | sl_atom { $1 }

binder:
  | ID COLON ID
      { ($1, Some (SUser $3)) }

  | ID ID
      { ($2, Some (SUser $1)) }

sl_atom:
  | NOT sl_atom
      { SNot $2 }

  | heap_atom { SHeap $1 }
  | cmp_sl { $1 }

  | ID
      {
        if $1 = "emp" then SEmp
        else failwith ("Unexpected bare identifier in sl: " ^ $1)
      }

  | LPAREN sl RPAREN { $2 }

  | FORALL binder DOT sl
      { SForall ([$2], $4) }

  | EXISTS binder DOT sl
      { SExists ([$2], $4) }

  | RETURN expr
      { SPure (EBinop (BEq, EResult, $2)) }
      
  | RETURN_HASH LPAREN expr RPAREN
    { SPure (EBinop (BEq, EResult, $3)) }


heap_mode_opt:
  | AT_I { In }
  | { Default }

heap_atom:
  | ID ARROW TYPE STAR LPAREN expr RPAREN heap_mode_opt
      { HPt { loc = EVar $1; ty = $3; value = $6; mode = $8 } }

  | ID ARROW TYPE STAR LPAREN expr COMMA expr RPAREN heap_mode_opt
      { HRange { loc = EVar $1; ty = $3; lo = $6; hi = $8; mode = $10 } }

cmp_sl:
  | expr cmp_op expr
      { SPure (EBinop ($2, $1, $3)) }

  | expr cmp_op expr cmp_op expr
      {
        SAnd [
          SPure (EBinop ($2, $1, $3));
          SPure (EBinop ($4, $3, $5));
        ]
      }

cmp_op:
  | EQEQ { BEq }
  | NEQ  { BNeq }
  | LT   { BLt }
  | LTE  { BLe }
  | GT   { BGt }
  | GTE  { BGe }

expr:
  | ID
      { if $1 = "\\result" then EResult else EVar $1 }

  | expr PRIME
      { EPost $1 }

  | OLD LPAREN expr RPAREN
      { EOld $3 }

  | STAR expr
      { EDeref $2 }

  | INT
      { EConstInt $1 }

  | expr PLUS expr
      { EBinop (BAdd, $1, $3) }

  | expr MINUS expr
      { EBinop (BSub, $1, $3) }

  | expr DIV expr
      { EBinop (BDiv, $1, $3) }

  | expr LBRACK expr RBRACK
      { EDeref (EBinop (BAdd, $1, $3)) }

  | LPAREN expr RPAREN
      { $2 }
      
  | MINUS expr
      { EUnop (UNeg, $2) }


case:
  | sl IMPLIES ens_clause
      {
        let (ret_opt, post) = $3 in
        ( { name = None; assumes = $1; body = [ CEns post ] }
        , ret_opt )
      }

  | sl IMPLIES REQ sl SEMICOLON ens_clause
      {
        let (ret_opt, post) = $6 in
        ( { name = None; assumes = $1; body = [ CReq $4; CEns post ] }
        , ret_opt )
      }

  | sl IMPLIES REQ TERM LBRACK expr RBRACK SEMICOLON ens_clause
      {
        let (ret_opt, post) = $9 in
        ( { name = None; assumes = $1; body = [ CVar (Some $6); CEns post ] }
        , ret_opt )
      }

  | sl IMPLIES REQ TERM LBRACK RBRACK SEMICOLON ens_clause
      {
        let (ret_opt, post) = $8 in
        ( { name = None; assumes = $1; body = [ CVar None; CEns post ] }
        , ret_opt )
      }

case_list:
  | case                  { [$1] }
  | case case_list        { $1 :: $2 }


loop_clause_list:
  | loop_clause                   { [$1] }
  | loop_clause SL_CONJ loop_clause_list
      { $1 :: $3 }

loop_clause:
  | REQ loop_req SEMICOLON ens_clause
      {
        let (assumes_sl, var_opt) = $2 in
        let (_ret_opt, post) = $4 in
        { name = None; assumes = assumes_sl; body = [ CVar var_opt; CEns post ] }
      }

loop_req:
  | sl TERM_AND LBRACK expr RBRACK
      { ($1, Some $4) }

  | sl TERM_AND LBRACK expr RBRACK AND sl
      { (SAnd [$1; $7], Some $4) }

  | sl TERM_AND LBRACK RBRACK
      { ($1, None) }

  | sl TERM_AND LBRACK RBRACK AND sl
      { (SAnd [$1; $6], None) }
