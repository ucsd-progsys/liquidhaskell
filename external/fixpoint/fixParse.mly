
%{
module A  = Ast
module So = A.Sort
module Sy = A.Symbol
module E  = A.Expression
module P  = A.Predicate
module H  = A.Horn
module Su = A.Subst
module C  = FixConstraint

(* 
 *
  %token <string> Tycon
  | (capital)letdig*    { Tycon (Lexing.lexeme lexbuf) }          
  | Tycon                               { So.t_app (So.tycon $1) [] }
  | Tycon tyconargsne                   { So.t_app (So.tycon $1) $2 }
   *)
  (*  | Id                                  { So.t_ptr (So.Loc $1) }

(*
pExprs:
    LPAREN RPAREN                       { []   }
  | LPAREN expr RPAREN                  { [$2] }
  | LPAREN exprsCommaNe RPAREN          { $2   }
  ;

exprsCommaNe:
    expr                                { [$1] }
  | expr COMMA exprsCommaNe             { $1 :: $3 }
  ; 
  *)

*)
let parse_error msg =
  Errorline.error (symbol_start ()) msg

let create_qual name vv = Qualifier.create (Sy.of_string name) (Sy.of_string vv) 

%}

%token <string> Id
%token <int> Num
%token TVAR 
%token TAG ID 
%token BEXP
%token TRUE FALSE
%token LPAREN  RPAREN LB RB LC RC
%token EQ NE GT GE LT LE
%token AND OR NOT NOTWORD IMPL IFF IFFWORD FORALL SEMI COMMA COLON MID
%token EOF
%token MOD 
%token PLUS
%token MINUS
%token TIMES 
%token DIV 
%token QM DOT ASGN
%token OBJ INT NUM PTR LFUN BOOL UNINT FUNC
%token SRT AXM CON CST WF SOL QUL ADP DDP
%token ENV GRD LHS RHS REF

%right IFF IFFWORD
%right IMPL
%left PLUS
%left MINUS
%left DIV
%left TIMES
%left DOT
%right NOT

%start defs 
%start sols
%start reft 

%type <FixConfig.deft list>     defs
%type <FixConfig.deft>          def
%type <FixConfig.solbind list>  sols
%type <So.t list>               sorts, sortsne 
%type <So.t>                    sort
%type <(Sy.t * So.t) list>      binds, bindsne 
%type <A.pred list>             preds, predsne
%type <A.pred>                  pred
%type <A.expr list>             exprs, exprsne
%type <A.expr>                  expr
%type <C.t>                     cstr
%type <C.envt>                  env
%type <FixConstraint.reft>      reft
%type <C.refa list>             refas, refasne
%type <C.refa>                  refa
%type <Su.t>                    subs

%%
defs:
                                        { [] } 
  | def defs                            { $1 :: $2 }
  ;



qual:
    Id LPAREN Id COLON sort RPAREN COLON pred            { create_qual $1 $3 $5 [] $8 }
  | Id LPAREN Id RPAREN COLON pred                       { create_qual $1 $3 So.t_int [] $6 }
  | Id LPAREN Id COLON sort qbindsne RPAREN COLON pred   { create_qual $1 $3 $5 $6 $9 }
  ;

qbindsne:
    COMMA bind                          { [$2] }
  | COMMA bind qbindsne                 { $2 :: $3 }
  ;

def:
    SRT COLON sort                      { FixConfig.Srt $3 }
  | AXM COLON pred                      { FixConfig.Axm $3 }
  | CST COLON cstr                      { FixConfig.Cst $3 }
  | CON Id COLON sort                   { FixConfig.Con (Sy.of_string $2, $4) }
  | WF  COLON wf                        { FixConfig.Wfc $3 }
  | sol                                 { FixConfig.Sol $1 } 
  | QUL qual                            { FixConfig.Qul $2 }
  | dep                                 { FixConfig.Dep $1 }
  ;

sorts:
    LB RB                               { [] }
  | LB sortsne RB                       { $2 }
  ;

sortsne:
    sort                                { [$1] }
  | sort SEMI sortsne                   { $1 :: $3 }
  ;

tyconargsne: 
  | bsort                               { [$1] }
  | bsort tyconargsne                   { $1 :: $2 }
  ;

sort:
  | bsort                               { $1 }
  | Id tyconargsne                      { So.t_app (So.tycon $1) $2 }
  | LB sort RB                          { So.t_app (So.tycon "List") [$2] }
 
  ;

bsort:
  | INT                                 { So.t_int }
  | BOOL                                { So.t_bool }
  | PTR                                 { So.t_ptr (So.Lvar 0) }
  | PTR LPAREN LFUN RPAREN              { So.t_ptr (So.LFun) }
  | PTR LPAREN Num RPAREN               { So.t_ptr (So.Lvar $3) }
  | PTR LPAREN Id RPAREN                { So.t_ptr (So.Loc $3) }
  | OBJ                                 { So.t_obj } 
  | NUM                                 { So.t_num } 
  | TVAR LPAREN Num RPAREN              { So.t_generic $3 }
  | FUNC LPAREN sorts RPAREN            { So.t_func 0 $3  }
  | FUNC LPAREN Num COMMA sorts RPAREN  { So.t_func $3 $5 }
  | Id                                  { So.t_ptr (So.Loc $1) }
  | LPAREN sort RPAREN                  { $2 }
  ; 


binds:
    LB RB                               { [] }
  | LB bindsne RB                       { $2 }
  ;

bindsne:
    bind                                { [$1] }
  | bind SEMI bindsne                   { $1::$3 }
  ;


bind:
  Id COLON sort                         { ((Sy.of_string $1), $3) }
  ;

rels:
    LB RB                               { [] }
  | LB relsne RB                        { $2 }
  ;

relsne: 
    rel                                 { [$1]}
  | rel SEMI relsne                     { $1 :: $3}
  ;

rel:
   EQ                                   { A.Eq }
 | NE                                   { A.Ne }    
 | GT                                   { A.Gt }
 | GE                                   { A.Ge }
 | LT                                   { A.Lt }
 | LE                                   { A.Le }
 ;


preds:
    LB RB                               { [] }
  | LB predsne RB                       { $2 }
  ;

predsne:
    pred                                { [$1] }
  | pred SEMI predsne                   { $1 :: $3 }
;

pred:
    TRUE				                { A.pTrue }
  | FALSE				                { A.pFalse }
  | BEXP expr                           { A.pBexp $2 }
  | QM expr                             { A.pBexp $2 }
  | Id LPAREN argsne RPAREN             { A.pBexp (A.eApp ((Sy.of_string $1), $3)) }
  | AND preds   			            { A.pAnd ($2) }
  | OR  preds 	        		        { A.pOr  ($2) }
  | NOT pred				            { A.pNot ($2) }
  | NOTWORD pred				        { A.pNot ($2) }
  | LPAREN pred AND pred RPAREN         { A.pAnd [$2; $4] }
  | LPAREN pred OR  pred RPAREN         { A.pOr  [$2; $4] }
  | expr rel expr                       { A.pAtom  ($1, $2, $3) }
  | expr rels expr                      { A.pMAtom ($1, $2, $3) }
  | FORALL binds DOT pred               { A.pForall ($2, $4) }
  | pred IMPL pred                      { A.pImp ($1, $3) }
  | pred IFF pred                       { A.pIff ($1, $3) }
  | pred IFFWORD pred                   { A.pIff ($1, $3) }
  | LPAREN pred RPAREN			        { $2 }
  ;

argsne:
    expr                                { [$1] } 
  | expr COMMA argsne                   { $1::$3 }
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
    Id                                    { A.eVar (Sy.of_string $1) }
  | con                                   { A.eCon $1  }
  | exprs                                 { A.eMExp $1 } 
  | LPAREN expr MOD Num RPAREN            { A.eMod ($2, $4) }
  | expr PLUS expr                        { A.eBin ($1, A.Plus, $3) }
  | expr MINUS expr                       { A.eBin ($1, A.Minus, $3) }
  | expr TIMES expr                       { A.eBin ($1, A.Times, $3) }
  | expr DIV expr                         { A.eBin ($1, A.Div, $3) }
  | expr ops expr                         { A.eMBin ($1, $2, $3) }
  | Id LPAREN exprs RPAREN                { A.eApp ((Sy.of_string $1), $3) }
  | Id Id                                 { A.eApp ((Sy.of_string $1), [A.eVar (Sy.of_string $2)]) }
  | LPAREN pred QM expr COLON expr RPAREN { A.eIte ($2,$4,$6) }
  | expr DOT Id                           { A.eFld ((Sy.of_string $3), $1) }
  | LPAREN expr COLON sort RPAREN         { A.eCst ($2, $4) }
  | LPAREN expr RPAREN                    { $2 }
  ;

op:
  | PLUS                                  { A.Plus  }
  | MINUS                                 { A.Minus }
  | TIMES                                 { A.Times }
  | DIV                                   { A.Div   }
  ; 

ops:
    LB RB                                 { [] }
  | LB opsne RB                           { $2 }
  ; 

opsne:
    op                                    { [$1] }
  | op SEMI opsne                         { $1 :: $3 }
  ;



con:
  | Num                                   { (A.Constant.Int $1) }
  | MINUS Num                             { (A.Constant.Int (-1 * $2)) }
  ;

cons:
    LB RB                                 { [] }
  | LB consne RB                          { $2 }
  ;

consne:
    con                                   { [$1] }
  | con SEMI consne                       { $1 :: $3 }
  ;

wf:
    ENV env REF reft                              { C.make_wf $2 $4 None }
  | ENV env REF reft ID Num                       { C.make_wf $2 $4 (Some $6) }
  ;

tagsne:
  Num                                             { [$1] }
  | Num SEMI tagsne                               { $1 :: $3 }
  ;

tag: 
  | LB tagsne RB                                  { ($2, "") }
  ;

dep:
  | ADP COLON tag IMPL tag                     {C.make_dep true (Some $3) (Some $5) }
  | DDP COLON tag IMPL tag                     {C.make_dep false (Some $3) (Some $5) }
  | DDP COLON TIMES IMPL tag                   {C.make_dep false None (Some $5) }
  | DDP COLON tag IMPL TIMES                   {C.make_dep false (Some $3) None }
  ;

info:
  ID Num                                        { ((Some $2), ([],"")) }
  | TAG tag                                     { (None     , $2)} 
  | ID Num TAG tag                              { ((Some $2), $4) }
  ;

cstr:
    ENV env GRD pred LHS reft RHS reft          { C.make_t $2 $4 $6 $8 None ([],"") }
  | ENV env GRD pred LHS reft RHS reft info     { C.make_t $2 $4 $6 $8 (fst $9) (snd $9)}
  ;


env:
  LB RB                                 { C.env_of_bindings [] }
  | LB envne RB                         { C.env_of_bindings $2 }
  ;

envne:
    rbind                               { [$1] }
  | rbind SEMI envne                    { $1 :: $3 }
  ;

rbind: 
  Id COLON reft                         { (Sy.of_string $1, $3) }
  ;

reft: 
  LC Id COLON sort MID refas RC         { ((Sy.of_string $2), $4, $6) }
  ;

refas:
    LB RB                               { [] }
  | LB refasne RB                       { $2 }
  ;

refasne:
    refa                                { [$1] }
  | refa SEMI refasne                   { $1 :: $3 }
  ;
  
refa:
    Id subs                             { C.Kvar ($2, (Sy.of_string $1)) }
  | pred                                { C.Conc $1 }
  ;

subs:
                                        { Su.empty }
  | LB Id ASGN expr RB subs             { Su.extend $6 ((Sy.of_string $2), $4) } 
  ;

npred: 
  LPAREN pred COMMA Id LPAREN argsne RPAREN RPAREN      { ((* $2, *) (Sy.of_string $4, $6)) }
  ;

npreds:
    LB RB                                { [] }
  | LB npredsne RB                       { $2 }
  ;

npredsne:
    npred                                { [$1] }
  | npred SEMI npredsne                  { $1 :: $3 }
;

sol:
    SOL COLON Id ASGN npreds            { ((Sy.of_string $3), $5) }

sols:
             { [] }
  | sol sols { $1 :: $2 }

