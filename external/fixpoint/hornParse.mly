
%{
module A  = Ast
module So = A.Sort
module Sy = A.Symbol
module E  = A.Expression
module P  = A.Predicate
module H  = A.Horn
module Su = A.Subst
module C  = FixConstraint

let parse_error msg =
  Errorline.error (symbol_start ()) msg

%}

%token <string> Var
%token <string> Id
%token <int> Num
%token BEXP
%token TRUE FALSE
%token LPAREN  RPAREN LB RB LC RC
%token EQ NE GT GE LT LE
%token AND OR NOT IMPL FORALL SEMI COMMA COLON DOT
%token EOF
%token PLUS
%token MINUS
%token TIMES 
%token DIV
%token HC 

%right PLUS 
%right MINUS
%right TIMES 
%right DIV 


%start horns 

%type <A.pred list>                          preds, predsne
%type <A.pred>                               pred
%type <A.expr list>                          exprs, exprsne
%type <A.expr>                               expr
%type <A.brel>                               brel 
%type <A.bop>                                bop 

%type <H.pr>                                 pr
%type <H.gd>                                 guard
%type <H.gd list>                            guards, guardsne
%type <Ast.Horn.t>                           hc
%type <Ast.Horn.t list>                      horns 

%%
preds:
    LB RB                               { [] }
  | LB predsne RB                       { $2 }
  ;

predsne:
    pred                                { [$1] }
  | pred SEMI predsne                   { $1 :: $3 }
;

pred:
    TRUE				{ A.pTrue }
  | FALSE				{ A.pFalse }
  | BEXP expr                           { A.pBexp $2 }
  | AND preds   			{ A.pAnd ($2) }
  | OR  preds 	        		{ A.pOr  ($2) }
  | NOT pred				{ A.pNot ($2) }
  | pred IMPL pred			{ A.pImp ($1, $3) }
  | expr brel expr                      { A.pAtom ($1, $2, $3) }
  | LPAREN pred RPAREN			{ $2 }
  ;

exprs:
    LB RB                               { [] }
  | LB exprsne RB                       { $2 }
  ;

exprsne:
    expr                                { [$1] }
  | expr SEMI exprsne                   { $1 :: $3 }
  ;

expr:
    Id				        { A.eVar (Sy.of_string $1) }
  | Num 				{ A.eCon (A.Constant.Int $1) }
  | MINUS Num 				{ A.eCon (A.Constant.Int (-1 * $2)) }
  | MINUS LPAREN expr RPAREN 	        { A.eBin (A.zero, A.Minus, $3) }
  | expr bop expr                       { A.eBin ($1, $2, $3) }
  | Id LPAREN  exprs RPAREN             { A.eApp ((Sy.of_string $1), $3) }
  | LPAREN expr RPAREN                  { $2 }
  ;

brel:
    EQ                                  { A.Eq }
  | NE                                  { A.Ne }
  | GT                                  { A.Gt }
  | GE                                  { A.Ge }
  | LT                                  { A.Lt }
  | LE                                  { A.Le }
  ;

bop:
    PLUS                                { A.Plus }
  | MINUS                               { A.Minus }
  | TIMES                               { A.Times }
  | DIV                                 { A.Div }
  ;


idsne:
    Id                                  { [$1] }
  | Id COMMA idsne                      { $1 :: $3 }
  ;

pr: 
    Var LPAREN RPAREN                    { ($1, []) }
  | Var LPAREN idsne RPAREN              { ($1, $3) }
  | Var                                  { ($1, []) }
  ;

guard:
    pr                                  { H.K ($1) }
  | pred                                { H.C ($1) }
  ;

guards:
    LB RB                               { [] }
  | LB guardsne RB                      { $2 }
  ;

guardsne:
    guard                               { [$1] }
  | guard COMMA guardsne                { $1 :: $3 }
  ;

hc: 
  HC LPAREN pr COMMA guards RPAREN DOT {($3, $5)}
  ;


horns:
                                        { [] }
  | hc horns                            { $1 :: $2 } 

