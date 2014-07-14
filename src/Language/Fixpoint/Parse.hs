{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections #-}

module Language.Fixpoint.Parse (
  
  -- * Top Level Class for Parseable Values  
    Inputable (..)
  
  -- * Top Level Class for Parseable Values  
  , Parser

  -- * Lexer to add new tokens
  , lexer 

  -- * Some Important keyword and parsers
  , reserved, reservedOp
  , parens  , brackets, angles, braces
  , semi    , comma     
  , colon   , dcolon 
  , whiteSpace
  , blanks

  -- * Parsing basic entities
  , fTyConP     -- Type constructors
  , lowerIdP    -- Lower-case identifiers
  , upperIdP    -- Upper-case identifiers
  , symbolP     -- Arbitrary Symbols
  , constantP   -- (Integer) Constants
  , integer     -- Integer
  , bindP       -- Binder (lowerIdP <* colon)

  -- * Parsing recursive entities
  , exprP       -- Expressions
  , predP       -- Refinement Predicates
  , funAppP     -- Function Applications
  , qualifierP  -- Qualifiers
  , refP        -- (Sorted) Refinements
  , refDefP     -- (Sorted) Refinements with default binder
  , refBindP    -- (Sorted) Refinements with configurable sub-parsers

  -- * Some Combinators
  , condIdP     -- condIdP  :: [Char] -> (String -> Bool) -> Parser String

  -- * Add a Location to a parsed value
  , locParserP
  , locLowerIdP
  , locUpperIdP

  -- * Getting a Fresh Integer while parsing
  , freshIntP

  -- * Parsing Function
  , doParse' 
  , parseFromFile
  , remainderP 
  ) where

import Control.Applicative ((<*>), (<$>), (<*))
import Control.Monad
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Pos
import Text.Parsec.Language
import Text.Parsec.String hiding (Parser, parseFromFile)
import Text.Printf  (printf)
import qualified Text.Parsec.Token as Token
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

import Data.Char (isLower, toUpper)
import Language.Fixpoint.Misc hiding (dcolon)
import Language.Fixpoint.Types
import Language.Fixpoint.Errors
import Language.Fixpoint.SmtLib2

import Data.Maybe(maybe, fromJust)

import Data.Monoid (mempty)

type Parser = Parsec String Integer 

--------------------------------------------------------------------

languageDef =
  emptyDef { Token.commentStart    = "/* "
           , Token.commentEnd      = " */"
           , Token.commentLine     = "--"
           , Token.identStart      = satisfy (\_ -> False) 
           , Token.identLetter     = satisfy (\_ -> False)
           , Token.reservedNames   = [ "SAT"
                                     , "UNSAT"
                                     , "true"
                                     , "false"
                                     , "mod"
                                     , "data"
                                     , "Bexp"
                                     , "forall"
                                     , "exists"
                                     , "assume"
                                     , "measure"
                                     , "module"
                                     , "spec"
                                     , "where"
                                     , "True"
                                     , "Int"
                                     , "import"
                                     , "_|_"
                                     , "|"
                                     , "if", "then", "else"
                                     ]
           , Token.reservedOpNames = [ "+", "-", "*", "/", "\\"
                                     , "<", ">", "<=", ">=", "=", "!=" , "/="
                                     , "mod", "and", "or" 
                                  --, "is"
                                     , "&&", "||"
                                     , "~", "=>", "<=>"
                                     , "->"
                                     , ":="
                                     , "&", "^", "<<", ">>", "--"
                                     , "?", "Bexp" -- , "'"
                                     ]
           }

lexer         = Token.makeTokenParser languageDef
reserved      = Token.reserved      lexer
reservedOp    = Token.reservedOp    lexer
parens        = Token.parens        lexer
brackets      = Token.brackets      lexer
angles        = Token.angles        lexer
semi          = Token.semi          lexer
colon         = Token.colon         lexer
comma         = Token.comma         lexer
whiteSpace    = Token.whiteSpace    lexer
stringLiteral = Token.stringLiteral lexer
braces        = Token.braces        lexer
double        = Token.float         lexer
-- integer       = Token.integer       lexer

-- identifier = Token.identifier lexer


blanks  = many (satisfy (`elem` [' ', '\t']))

integer = posInteger 
  
--  try (char '-' >> (negate <$> posInteger))
--       <|> posInteger

posInteger = toI <$> (many1 digit <* spaces)
  where
    toI :: String -> Integer 
    toI = read

----------------------------------------------------------------
------------------------- Expressions --------------------------
----------------------------------------------------------------

locParserP :: Parser a -> Parser (Located a)
locParserP p = liftM2 Loc getPosition p

condIdP  :: [Char] -> (String -> Bool) -> Parser String
condIdP chars f 
  = do c  <- letter
       cs <- many (satisfy (`elem` chars))
       blanks
       if f (c:cs) then return (c:cs) else parserZero

upperIdP :: Parser String
upperIdP = condIdP symChars (not . isLower . head)

lowerIdP :: Parser String
lowerIdP = condIdP symChars (isLower . head)

locLowerIdP = locParserP lowerIdP 
locUpperIdP = locParserP upperIdP

symbolP :: Parser Symbol
symbolP = liftM stringSymbol symCharsP 

constantP :: Parser Constant
constantP = try (liftM R double) <|> liftM I integer

symconstP :: Parser SymConst
symconstP = SL <$> stringLiteral 

expr0P :: Parser Expr
expr0P 
  =  try (liftM (EVar . stringSymbol) upperIdP)
 <|> liftM expr symbolP 
 <|> liftM ESym symconstP
 <|> try (liftM ECon constantP)
 <|> (reserved "_|_" >> return EBot)
 <|> try (parens exprP)
 <|> try (parens exprCastP)
 <|> try (parens $ condP EIte exprP)


expr1P :: Parser Expr
expr1P 
  =  try funAppP 
 <|> expr0P 

exprP :: Parser Expr 
exprP = buildExpressionParser bops expr1P

funAppP            =  (try exprFunSpacesP) <|> (try exprFunSemisP) <|> exprFunCommasP
  where 
    exprFunSpacesP = liftM2 EApp funSymbolP (sepBy1 expr0P spaces) 
    exprFunCommasP = liftM2 EApp funSymbolP (parens        $ sepBy exprP comma)
    exprFunSemisP  = liftM2 EApp funSymbolP (parenBrackets $ sepBy exprP semi)
    funSymbolP     = locParserP symbolP




-- ORIG exprP :: Parser Expr 
-- ORIG exprP =  expr2P <|> lexprP
-- 
-- ORIG lexprP :: Parser Expr 
-- ORIG lexprP   
-- ORIG   =  try (parens exprP)
-- ORIG  <|> try (parens exprCastP)
-- ORIG  <|> try (parens $ condP EIte exprP)
-- ORIG  <|> try exprFunP
-- ORIG  <|> try (liftM (EVar . stringSymbol) upperIdP)
-- ORIG  <|> liftM expr symbolP 
-- ORIG  <|> liftM ECon constantP
-- ORIG  <|> liftM ESym symconstP
-- ORIG  <|> (reserved "_|_" >> return EBot)
-- ORIG 
-- ORIG exprFunP           =  (try exprFunSpacesP) <|> (try exprFunSemisP) <|> exprFunCommasP
-- ORIG   where 
-- ORIG     exprFunSpacesP = parens $ liftM2 EApp funSymbolP (sepBy exprP spaces) 
-- ORIG     exprFunCommasP = liftM2 EApp funSymbolP (parens        $ sepBy exprP comma)
-- ORIG     exprFunSemisP  = liftM2 EApp funSymbolP (parenBrackets $ sepBy exprP semi)
-- ORIG     funSymbolP     = locParserP symbolP -- liftM stringSymbol lowerIdP

parenBrackets  = parens . brackets 

-- ORIG expr2P = buildExpressionParser bops lexprP

bops = [ [ Prefix (reservedOp "-"   >> return eMinus)]
       , [ Infix  (reservedOp "*"   >> return (EBin Times)) AssocLeft
         , Infix  (reservedOp "/"   >> return (EBin Div  )) AssocLeft
         ]
       , [ Infix  (reservedOp "-"   >> return (EBin Minus)) AssocLeft
         , Infix  (reservedOp "+"   >> return (EBin Plus )) AssocLeft
         ]
       , [Infix  (reservedOp "mod"  >> return (EBin Mod  )) AssocLeft]
       ]

eMinus = EBin Minus (expr (0 :: Integer)) 

myTest3 = "((((v >= 56320) && (v <= 57343)) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o ((i - o) - 1)))) && (((numchars a o (i - (o -1))) >= 0) && (((i - o) - 1) >= 0)))) && ((not (((v >= 56320) && (v <= 57343)))) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o (i - o)))) && ((numchars a o (i - o)) >= 0))))"



exprCastP
  = do e  <- exprP 
       ((try dcolon) <|> colon)
       so <- sortP
       return $ ECst e so

dcolon = string "::" <* spaces

sortP
  =   try (string "Integer" >>  return FInt)
  <|> try (string "Int"     >>  return FInt)
  <|> try (string "int"     >>  return FInt)
  <|> try (FObj . stringSymbol <$> lowerIdP)
  <|> (fApp <$> (Left <$> fTyConP) <*> many sortP)

symCharsP   = condIdP symChars (`notElem` keyWordSyms)

keyWordSyms = ["mod"]

---------------------------------------------------------------------
-------------------------- Predicates -------------------------------
---------------------------------------------------------------------

trueP  = reserved "true"  >> return PTrue
falseP = reserved "false" >> return PFalse

pred0P :: Parser Pred
pred0P =  try trueP 
      <|> try falseP 
      <|> try predrP 
      <|> try (reservedOp "&&" >> liftM PAnd predsP)
      <|> try (reservedOp "||" >> liftM POr  predsP)
      <|> (qmP >> liftM PBexp exprP)
      <|> try (liftM PBexp funAppP)
      <|> try (parens $ condP pIte predP)
      <|> parens predP 

predP  :: Parser Pred
predP  = buildExpressionParser lops pred0P


predsP = brackets $ sepBy predP semi

qmP    = reserved "?" <|> reserved "Bexp"

-- ORIG predP =  try (parens pred2P)
-- ORIG      <|> try (parens $ condP pIte predP)
-- ORIG      <|> try (reservedOp "not" >> liftM PNot predP)
-- ORIG      <|> try (reservedOp "&&" >> liftM PAnd predsP)
-- ORIG      <|> try (reservedOp "||" >> liftM POr  predsP)
-- ORIG      <|> (qmP >> liftM PBexp exprP)
-- ORIG      <|> trueP   --  (reserved "true"  >> return PTrue)
-- ORIG      <|> falseP  --  (reserved "false" >> return PFalse)
-- ORIG      <|> (try predrP)
-- ORIG      <|> (try (liftM PBexp exprFunP))


-- ORIG pred2P = buildExpressionParser lops predP 


lops = [ [Prefix (reservedOp "~"    >> return PNot)]
       , [Prefix (reservedOp "not " >> return PNot)]
       , [Infix  (reservedOp "&&"   >> return (\x y -> PAnd [x,y])) AssocRight]
       , [Infix  (reservedOp "||"   >> return (\x y -> POr  [x,y])) AssocRight]
       , [Infix  (reservedOp "=>"   >> return PImp) AssocRight]
       , [Infix  (reservedOp "<=>"  >> return PIff) AssocRight]]
       
predrP = do e1    <- exprP
            r     <- brelP
            e2    <- exprP 
            return $ r e1 e2

brelP ::  Parser (Expr -> Expr -> Pred)
brelP =  (reservedOp "==" >> return (PAtom Eq))
     <|> (reservedOp "="  >> return (PAtom Eq))
     <|> (reservedOp "~~" >> return (PAtom Ueq))
     <|> (reservedOp "!=" >> return (PAtom Ne))
     <|> (reservedOp "/=" >> return (PAtom Ne))
     <|> (reservedOp "!~" >> return (PAtom Une))
     <|> (reservedOp "<"  >> return (PAtom Lt))
     <|> (reservedOp "<=" >> return (PAtom Le))
     <|> (reservedOp ">"  >> return (PAtom Gt))
     <|> (reservedOp ">=" >> return (PAtom Ge))

condIteP f bodyP 
  = do reserved "if" 
       p <- predP
       reserved "then"
       b1 <- bodyP 
       reserved "else"
       b2 <- bodyP 
       return $ f p b1 b2

condQmP f bodyP 
  = do p  <- predP 
       reserved "?"
       b1 <- bodyP 
       colon
       b2 <- bodyP 
       return $ f p b1 b2

condP f bodyP 
   =   try (condIteP f bodyP)
   <|> (condQmP f bodyP)

----------------------------------------------------------------------------------
------------------------------------ BareTypes -----------------------------------
----------------------------------------------------------------------------------

fTyConP
  =   (reserved "int"  >> return intFTyCon)
  <|> (reserved "bool" >> return boolFTyCon)
  <|> (reserved "real" >> return realFTyCon)
  <|> (stringFTycon   <$> locUpperIdP)

refasP :: Parser [Refa]
refasP  =  (try (brackets $ sepBy (RConc <$> predP) semi)) 
       <|> liftM ((:[]) . RConc) predP

refBindP :: Parser Symbol -> Parser [Refa] -> Parser (Reft -> a) -> Parser a
refBindP bp rp kindP
  = braces $ do
      vv  <- bp
      t   <- kindP
      reserved "|"
      ras <- rp <* spaces
      return $ t (Reft (vv, ras))

bindP       = liftM stringSymbol (lowerIdP <* colon)
optBindP vv = try bindP <|> return vv

refP       = refBindP bindP refasP
refDefP vv = refBindP (optBindP vv)

---------------------------------------------------------------------
-- | Parsing Qualifiers ---------------------------------------------
---------------------------------------------------------------------

-- qualifierP = mkQual <$> upperIdP <*> parens $ sepBy1 sortBindP comma <*> predP

qualifierP = do n      <- upperIdP 
                params <- parens $ sepBy1 sortBindP comma
                _      <- colon
                body   <- predP
                return  $ mkQual n params body

sortBindP  = (,) <$> symbolP <* colon <*> sortP

mkQual n xts p = Q n ((vv, t) : yts) (subst su p)
  where 
    (vv,t):zts = xts
    yts        = mapFst mkParam <$> zts
    su         = mkSubst $ zipWith (\(z,_) (y,_) -> (z, eVar y)) zts yts 
                       
mkParam s      = stringSymbolRaw ('~' : toUpper c : cs) 
  where 
    (c:cs)     = symbolString s 

---------------------------------------------------------------------
-- | Parsing Constraints (.fq files) --------------------------------
---------------------------------------------------------------------

fInfoP :: Parser (FInfo ())
fInfoP = defsFInfo <$> many defP

defP :: Parser (Def ())
defP =  Srt   <$> (reserved "sort"        >> colon >> sortP)
    <|> Axm   <$> (reserved "axiom"       >> colon >> predP)
    <|> Cst   <$> (reserved "constraint"  >> colon >> subCP)
    <|> Wfc   <$> (reserved "wf"          >> colon >> wfCP)
    <|> Con   <$> (reserved "constant"    >> symbolP) <*> (colon >> sortP)
    <|> Qul   <$> (reserved "qualifier"   >> qualifierP)
    <|> Kut   <$> (reserved "cut"         >> symbolP)
    <|> IBind <$> (reserved "bind"        >> intP) <*> symbolP <*> (colon >> sortedReftP)

sortedReftP :: Parser SortedReft
sortedReftP = refP (RR <$> (sortP <* spaces)) 

wfCP :: Parser (WfC ())
wfCP = do reserved "env"
          env <- envP
          reserved "reft"
          r   <- sortedReftP
          return $ wfC env r Nothing ()

subCP :: Parser (SubC ())
subCP = do reserved "env" 
           env <- envP 
           reserved "grd"
           grd <- predP
           reserved "lhs"
           lhs <- sortedReftP 
           reserved "rhs"
           rhs <- sortedReftP 
           reserved "id"
           i   <- (integer <* spaces)
           tag <- tagP
           return $ safeHead "subCP" $ subC env grd lhs rhs (Just i) tag () 

tagP  :: Parser [Int]
tagP  =  try (reserved "tag" >> spaces >> (brackets $ sepBy intP semi))
     <|> (return [])

envP  :: Parser IBindEnv
envP  = do binds <- brackets $ sepBy (intP <* spaces) semi 
           return $ insertsIBindEnv binds emptyIBindEnv

intP :: Parser Int
intP = fromInteger <$> integer

defsFInfo :: [Def a] -> FInfo a
defsFInfo defs = FI cm ws bs gs lts kts qs
  where 
    cm     = M.fromList       [(cid c, c)       | Cst c       <- defs]
    ws     =                  [w                | Wfc w       <- defs]
    bs     = rawBindEnv       [(n, x, r)        | IBind n x r <- defs]
    gs     = fromListSEnv     [(x, RR t mempty) | Con x t     <- defs]
    lts    =                  [(x, t)           | Con x t     <- defs, notFun t]
    kts    = KS $ S.fromList  [k                | Kut k       <- defs]     
    qs     =                  [q                | Qul q       <- defs]
    cid    = fromJust . sid
    notFun = not . isFunctionSortedReft . (`RR` trueReft) 
---------------------------------------------------------------------
-- | Interacting with Fixpoint --------------------------------------
---------------------------------------------------------------------

fixResultP :: Parser a -> Parser (FixResult a)
fixResultP pp 
  =  (reserved "SAT"   >> return Safe)
 <|> (reserved "UNSAT" >> Unsafe <$> (brackets $ sepBy pp comma))  
 <|> (reserved "CRASH" >> crashP pp)

crashP pp
  = do i   <- pp
       msg <- many anyChar
       return $ Crash [i] msg

predSolP 
  = parens $ (predP  <* (comma >> iQualP)) 
    

iQualP
  = upperIdP >> (parens $ sepBy symbolP comma)

solution1P
  = do reserved "solution:" 
       k  <- symbolP 
       reserved ":=" 
       ps <- brackets $ sepBy predSolP semi
       return (k, simplify $ PAnd ps)

solutionP :: Parser (M.HashMap Symbol Pred)
solutionP 
  = M.fromList <$> sepBy solution1P whiteSpace

solutionFileP 
  = liftM2 (,) (fixResultP integer) solutionP

------------------------------------------------------------------------

remainderP p  
  = do res <- p
       str <- stateInput <$> getParserState
       pos <- getPosition 
       return (res, str, pos) 

doParse' parser f s
  = case runParser (remainderP (whiteSpace >> parser)) 0 f s of
      Left e            -> die $ err (errorSpan e) $ printf "parseError %s\n when parsing from %s\n" (show e) f 
      Right (r, "", _)  -> r
      Right (_, rem, l) -> die $ err (SS l l) $ printf "doParse has leftover when parsing: %s\nfrom file %s\n" rem f
    
errorSpan e = SS l l where l = errorPos e

parseFromFile :: Parser b -> SourceName -> IO b
parseFromFile p f = doParse' p f <$> readFile f

freshIntP :: Parser Integer
freshIntP = do n <- stateUser <$> getParserState
               updateState (+ 1)
               return n

---------------------------------------------------------------------
-- Standalone SMTLIB2 commands --------------------------------------
---------------------------------------------------------------------

commandsP = sepBy commandP semi

commandP 
  =  (reserved "var"      >> cmdVarP)
 <|> (reserved "push"     >> return Push)
 <|> (reserved "pop"      >> return Pop)
 <|> (reserved "check"    >> return CheckSat)
 <|> (reserved "assert"   >> (Assert Nothing <$> predP))
 <|> (reserved "distinct" >> (Distinct <$> (brackets $ sepBy exprP comma)))

cmdVarP 
  = do x <- bindP 
       t <- sortP
       return $ Declare x [] t


---------------------------------------------------------------------
-- Bundling Parsers into a Typeclass --------------------------------
---------------------------------------------------------------------

class Inputable a where
  rr  :: String -> a
  rr' :: String -> String -> a
  rr' = \_ -> rr
  rr  = rr' "" 

instance Inputable Symbol where
  rr' = doParse' symbolP

instance Inputable Constant where
  rr' = doParse' constantP 

instance Inputable Pred where
  rr' = doParse' predP 

instance Inputable Expr where
  rr' = doParse' exprP 

instance Inputable [Refa] where
  rr' = doParse' refasP

instance Inputable (FixResult Integer) where
  rr' = doParse' $ fixResultP integer

instance Inputable (FixResult Integer, FixSolution) where
  rr' = doParse' solutionFileP 

instance Inputable (FInfo ()) where
  rr' = doParse' fInfoP

instance Inputable Command where
  rr' = doParse' commandP 

instance Inputable [Command] where
  rr' = doParse' commandsP

{-
---------------------------------------------------------------
--------------------------- Testing ---------------------------
---------------------------------------------------------------

sa  = "0"
sb  = "x"
sc  = "(x0 + y0 + z0) "
sd  = "(x+ y * 1)"
se  = "_|_ "
sf  = "(1 + x + _|_)"
sg  = "f(x,y,z)"
sh  = "(f((x+1), (y * a * b - 1), _|_))"
si  = "(2 + f((x+1), (y * a * b - 1), _|_))"

s0  = "true"
s1  = "false"
s2  = "v > 0"
s3  = "(0 < v && v < 100)"
s4  = "(x < v && v < y+10 && v < z)"
s6  = "[(v > 0)]"
s6' = "x"
s7' = "(x <=> y)"
s8' = "(x <=> a = b)"
s9' = "(x <=> (a <= b && b < c))"

s7  = "{ v: Int | [(v > 0)] }"
s8  = "x:{ v: Int | v > 0 } -> {v : Int | v >= x}"
s9  = "v = x+y"
s10 = "{v: Int | v = x + y}"

s11 = "x:{v:Int | true } -> {v:Int | true }" 
s12 = "y : {v:Int | true } -> {v:Int | v = x }"
s13 = "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
s14 = "x:{v:a  | true} -> y:{v:b | true } -> {v:a | (x < v && v < y) }"
s15 = "x:Int -> Bool"
s16 = "x:Int -> y:Int -> {v:Int | v = x + y}"
s17 = "a"
s18 = "x:a -> Bool"
s20 = "forall a . x:Int -> Bool"

s21 = "x:{v : GHC.Prim.Int# | true } -> {v : Int | true }" 

r0  = (rr s0) :: Pred
r0' = (rr s0) :: [Refa]
r1  = (rr s1) :: [Refa]


e1, e2  :: Expr  
e1  = rr "(k_1 + k_2)"
e2  = rr "k_1" 

o1, o2, o3 :: FixResult Integer
o1  = rr "SAT " 
o2  = rr "UNSAT [1, 2, 9,10]"
o3  = rr "UNSAT []" 

-- sol1 = doParse solution1P "solution: k_5 := [0 <= VV_int]"
-- sol2 = doParse solution1P "solution: k_4 := [(0 <= VV_int)]" 

b0, b1, b2, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 :: BareType
b0  = rr "Int"
b1  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
b2  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}"
b4  = rr "forall a . x : a -> Bool"
b5  = rr "Int -> Int -> Int"
b6  = rr "(Int -> Int) -> Int"
b7  = rr "({v: Int | v > 10} -> Int) -> Int"
b8  = rr "(x:Int -> {v: Int | v > x}) -> {v: Int | v > 10}"
b9  = rr "x:Int -> {v: Int | v > x} -> {v: Int | v > 10}"
b10 = rr "[Int]"
b11 = rr "x:[Int] -> {v: Int | v > 10}"
b12 = rr "[Int] -> String"
b13 = rr "x:(Int, [Bool]) -> [(String, String)]"

-- b3 :: BareType
-- b3  = rr "x:Int -> y:Int -> {v:Bool | ((v is True) <=> x = y)}"

m1 = ["len :: [a] -> Int", "len (Nil) = 0", "len (Cons x xs) = 1 + len(xs)"]
m2 = ["tog :: LL a -> Int", "tog (Nil) = 100", "tog (Cons y ys) = 200"]

me1, me2 :: Measure.Measure BareType Symbol 
me1 = (rr $ intercalate "\n" m1) 
me2 = (rr $ intercalate "\n" m2)
-}
