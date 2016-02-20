{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE OverloadedStrings         #-}

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
  , pairP

  -- * Parsing basic entities

  --   fTyConP  -- Type constructors
  , lowerIdP    -- Lower-case identifiers
  , upperIdP    -- Upper-case identifiers
  , symbolP     -- Arbitrary Symbols
  , constantP   -- (Integer) Constants
  , integer     -- Integer
  , bindP       -- Binder (lowerIdP <* colon)
  , sortP       -- Sort
  , mkQual      -- constructing qualifiers

  -- * Parsing recursive entities
  , exprP       -- Expressions
  , predP       -- Refinement Predicates
  , funAppP     -- Function Applications
  , qualifierP  -- Qualifiers
  , refaP       -- Refa
  , refP        -- (Sorted) Refinements
  , refDefP     -- (Sorted) Refinements with default binder
  , refBindP    -- (Sorted) Refinements with configurable sub-parsers
  , bvSortP     -- Bit-Vector Sort

  -- * Some Combinators
  , condIdP     -- condIdP  :: [Char] -> (Text -> Bool) -> Parser Text

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

  -- * Utilities
  , isSmall
  ) where

import qualified Data.HashMap.Strict         as M
import qualified Data.HashSet                as S
import qualified Data.Text                   as T
import           Data.Maybe                  (fromJust)
import           Text.Parsec
import           Text.Parsec.Expr
import           Text.Parsec.Language        (emptyDef)
import qualified Text.Parsec.Token           as Token
-- import           Text.Printf                 (printf)
import           GHC.Generics                (Generic)

import           Data.Char                   (isLower)
import           Language.Fixpoint.Smt.Bitvector
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Misc      (tshow, sortNub, thd3)
import           Language.Fixpoint.Smt.Types
--import           Language.Fixpoint.Types.Names     (headSym)
import           Language.Fixpoint.Types.Visitor   (foldSort, mapSort)
import           Language.Fixpoint.Types hiding    (mapSort)
import           Text.PrettyPrint.HughesPJ         (text, nest, vcat, (<+>))
type Parser = Parsec String Integer

--------------------------------------------------------------------

languageDef =
  emptyDef { Token.commentStart    = "/* "
           , Token.commentEnd      = " */"
           , Token.commentLine     = "//"
           , Token.identStart      = satisfy (const False)
           , Token.identLetter     = satisfy (const False)
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
           , Token.reservedOpNames = [ "+", "-", "*", "/", "\\", ":"
                                     , "<", ">", "<=", ">=", "=", "!=" , "/="
                                     , "mod", "and", "or"
                                  --, "is"
                                     , "&&", "||"
                                     , "~", "=>", "==>", "<=>"
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
locParserP p = do l1 <- getPosition
                  x  <- p
                  l2 <- getPosition
                  return $ Loc l1 l2 x


-- FIXME: we (LH) rely on this parser being dumb and *not* consuming trailing
-- whitespace, in order to avoid some parsers spanning multiple lines..
condIdP  :: S.HashSet Char -> (String -> Bool) -> Parser Symbol
condIdP chars f
  = do c  <- letter <|> char '_'
       cs <- many (satisfy (`S.member` chars))
       blanks
       if f (c:cs) then return (symbol $ c:cs) else parserZero

upperIdP :: Parser Symbol
upperIdP = condIdP symChars (not . isSmall . head)

lowerIdP :: Parser Symbol
lowerIdP = condIdP symChars (isSmall . head)

isSmall :: Char -> Bool
isSmall c = isLower c || c == '_'

symCharsP :: Parser Symbol
symCharsP = condIdP symChars (`notElem` keyWordSyms)

locLowerIdP = locParserP lowerIdP
locUpperIdP = locParserP upperIdP

symbolP :: Parser Symbol
symbolP = symbol <$> symCharsP

constantP :: Parser Constant
constantP =  try (R <$> double)
         <|> I <$> integer

symconstP :: Parser SymConst
symconstP = SL . T.pack <$> stringLiteral

expr0P :: Parser Expr
expr0P
  =  (fastIfP EIte exprP)
 <|> (ESym <$> symconstP)
 <|> (ECon <$> constantP)
 <|> (reserved "_|_" >> return EBot)
 <|> lamP
 <|> try (parens  exprP)
 <|> try (parens  exprCastP)
 <|> (charsExpr <$> symCharsP)

charsExpr cs
  | isSmall (headSym cs) = expr cs
  | otherwise            = EVar cs

fastIfP f bodyP
  = do reserved "if"
       p <- predP
       reserved "then"
       b1 <- bodyP
       reserved "else"
       b2 <- bodyP
       return $ f p b1 b2

{-
qmIfP f bodyP
  = parens $ do
      p  <- predP
      reserved "?"
      b1 <- bodyP
      colon
      b2 <- bodyP
      return $ f p b1 b2
-}

expr1P :: Parser Expr
expr1P
  =  try funAppP
 <|> expr0P

exprP :: Parser Expr
exprP = buildExpressionParser bops expr1P

funAppP            =  (try litP) <|> (try exprFunSpacesP) <|> (try exprFunSemisP) <|> exprFunCommasP <|> simpleAppP
  where
    exprFunSpacesP = mkEApp <$> funSymbolP <*> sepBy1 expr0P blanks
    exprFunCommasP = mkEApp <$> funSymbolP <*> parens        (sepBy exprP comma)
    exprFunSemisP  = mkEApp <$> funSymbolP <*> parenBrackets (sepBy exprP semi)
    simpleAppP     = EApp <$> (parens exprP) <*> (parens exprP)
    funSymbolP     = locParserP symbolP


-- | BitVector literal: lit "#x00000001" (BitVec (Size32 obj))
litP = do reserved "lit"
          l <- stringLiteral
          t <- sortP
          return $ ECon $ L (T.pack l) t

parenBrackets  = parens . brackets

bops = [ [ Prefix (reservedOp "-"   >> return ENeg)]
       , [ Infix  (reservedOp "*"   >> return (EBin Times)) AssocLeft
         , Infix  (reservedOp "/"   >> return (EBin Div  )) AssocLeft
         ]
       , [ Infix  (reservedOp "-"   >> return (EBin Minus)) AssocLeft
         , Infix  (reservedOp "+"   >> return (EBin Plus )) AssocLeft
         ]
       , [ Infix  (reservedOp "mod"  >> return (EBin Mod  )) AssocLeft]
       ]

-- eMinus     = EBin Minus (expr (0 :: Integer))
-- eCons x xs = EApp (dummyLoc consName) [x, xs]
-- eNil       = EVar nilName

exprCastP
  = do e  <- exprP
       (try dcolon) <|> colon
       so <- sortP
       return $ ECst e so


lamP
  = do reserved "\\"
       x <- symbolP
       colon
       t <- sortP
       reserved "->"
       e  <- exprP
       return $ ELam (x, t) e


dcolon = string "::" <* spaces

varSortP  = FVar  <$> parens intP
funcSortP = parens $ mkFFunc <$> intP <* comma <*> sortsP

sortsP = brackets $ sepBy sortP semi

sortP    :: Parser Sort
sortP    = sortP' (sepBy sortArgP blanks)

sortArgP :: Parser Sort
sortArgP = sortP' (return [])

{-
sortFunP :: Parser Sort
sortFunP
   =  try (string "@" >> varSortP)
  <|> (fTyconSort <$> fTyConP)
-}

sortP' :: Parser [Sort] -> Parser Sort
sortP' appArgsP
   =  try (parens sortP)
  <|> try (string "func" >> funcSortP)
  <|> try (fAppTC listFTyCon . single <$> brackets sortP)
  <|> try bvSortP
  <|> try (fAppTC <$> fTyConP <*> appArgsP)
  <|> try (fApp   <$> tvarP   <*> appArgsP)

single x = [x]

tvarP :: Parser Sort
tvarP
   =  try (string "@" >> varSortP)
  <|> (FObj . symbol <$> lowerIdP)


fTyConP :: Parser FTycon
fTyConP
  =   (reserved "int"     >> return intFTyCon)
  <|> (reserved "Integer" >> return intFTyCon)
  <|> (reserved "Int"     >> return intFTyCon)
  <|> (reserved "int"     >> return intFTyCon)
  <|> (reserved "real"    >> return realFTyCon)
  <|> (reserved "bool"    >> return boolFTyCon)
  <|> (reserved "num"     >> return numFTyCon)
  <|> (symbolFTycon      <$> locUpperIdP)

bvSortP
  = mkSort <$> (bvSizeP "Size32" S32 <|> bvSizeP "Size64" S64)

bvSizeP ss s = do
  parens (reserved "BitVec" >> reserved ss)
  return s

keyWordSyms = ["if", "then", "else", "mod"]

--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

pred0P :: Parser Expr
pred0P =  trueP
      <|> falseP
      <|> try (reserved "??" >> return PGrad)
      <|> try kvarPredP
      <|> try (fastIfP pIte predP)
      <|> try predrP
      <|> try (parens predP)
      <|> try (reserved "?" *> exprP)
      <|> try funAppP
      <|> try (reservedOp "&&" >> PAnd <$> predsP)
      <|> try (reservedOp "||" >> POr  <$> predsP)

-- qmP    = reserved "?" <|> reserved "Bexp"

trueP, falseP :: Parser Expr
trueP  = reserved "true"  >> return PTrue
falseP = reserved "false" >> return PFalse

kvarPredP :: Parser Expr
kvarPredP = PKVar <$> kvarP <*> substP

kvarP :: Parser KVar
kvarP = KV <$> (char '$' *> symbolP <* spaces)

substP :: Parser Subst
substP = mkSubst <$> many (brackets $ pairP symbolP aP exprP)
  where
    aP = reserved ":="

predP  :: Parser Expr
predP  = buildExpressionParser lops pred0P


predsP = brackets $ sepBy predP semi


lops = [ [Prefix (reservedOp "~"    >> return PNot)]
       , [Prefix (reservedOp "not " >> return PNot)]
       , [Infix  (reservedOp "&&"   >> return (\x y -> PAnd [x,y])) AssocRight]
       , [Infix  (reservedOp "||"   >> return (\x y -> POr  [x,y])) AssocRight]
       , [Infix  (reservedOp "=>"   >> return PImp) AssocRight]
       , [Infix  (reservedOp "==>"  >> return PImp) AssocRight]
       , [Infix  (reservedOp "<=>"  >> return PIff) AssocRight]]

predrP = do e1    <- exprP
            r     <- brelP
            e2    <- exprP
            return $ r e1 e2

brelP ::  Parser (Expr -> Expr -> Expr)
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

----------------------------------------------------------------------------------
------------------------------------ BareTypes -----------------------------------
----------------------------------------------------------------------------------

refaP :: Parser Expr
refaP =  try (pAnd <$> brackets (sepBy predP semi))
     <|> predP



refBindP :: Parser Symbol -> Parser Expr -> Parser (Reft -> a) -> Parser a
refBindP bp rp kindP
  = braces $ do
      x  <- bp
      t  <- kindP
      reserved "|"
      ra <- rp <* spaces
      return $ t (Reft (x, ra))

-- bindP      = symbol    <$> (lowerIdP <* colon)
bindP      = symbolP <* colon
optBindP x = try bindP <|> return x

refP       = refBindP bindP refaP
refDefP x  = refBindP (optBindP x)

---------------------------------------------------------------------
-- | Parsing Qualifiers ---------------------------------------------
---------------------------------------------------------------------

qualifierP tP = do
  pos    <- getPosition
  n      <- upperIdP
  params <- parens $ sepBy1 (sortBindP tP) comma
  _      <- colon
  body   <- predP
  return  $ mkQual n params body pos

sortBindP = pairP symbolP colon

pairP :: Parser a -> Parser z -> Parser b -> Parser (a, b)
pairP xP sepP yP = (,) <$> xP <* sepP <*> yP

mkQual :: Symbol -> [(Symbol, Sort)] -> Expr -> SourcePos -> Qualifier
mkQual n xts p = Q n ((v, t) : yts) (subst su p)
  where
    (v, t):zts = gSorts xts
    -- yts        = first mkParam <$> zts
    yts        = zts
    su         = mkSubst $ zipWith (\(z,_) (y,_) -> (z, eVar y)) zts yts

-- mkParam :: Symbol -> Symbol
-- mkParam s       = unsafeTextSymbol ('~' `T.cons` toUpper c `T.cons` cs)
--  where
--    Just (c,cs) = T.uncons $ symbolSafeText s

gSorts :: [(a, Sort)] -> [(a, Sort)]
gSorts xts     = [(x, substVars su t) | (x, t) <- xts]
  where
    su         = (`zip` [0..]) . sortNub . concatMap (sortVars . snd) $ xts

substVars :: [(Symbol, Int)] -> Sort -> Sort
substVars su = mapSort tx
  where
    tx (FObj x)
      | Just i <- lookup x su = FVar i
    tx t                      = t

sortVars :: Sort -> [Symbol]
sortVars = foldSort go []
  where
    go b (FObj x) = x : b
    go b _        = b


---------------------------------------------------------------------
-- | Parsing Constraints (.fq files) --------------------------------
---------------------------------------------------------------------

-- Entities in Query File
data Def a
  = Srt Sort
  | Axm Expr
  | Cst (SubC a)
  | Wfc (WfC a)
  | Con Symbol Sort
  | Qul Qualifier
  | Kut KVar
  | IBind Int Symbol SortedReft
  deriving (Show, Generic)
  --  Sol of solbind
  --  Dep of FixConstraint.dep

fInfoP :: Parser (FInfo ())
fInfoP = defsFInfo <$> {-# SCC "many-defP" #-} many defP

defP :: Parser (Def ())
defP =  Srt   <$> (reserved "sort"       >> colon >> sortP)
    <|> Axm   <$> (reserved "axiom"      >> colon >> predP)
    <|> Cst   <$> (reserved "constraint" >> colon >> {-# SCC "subCP" #-} subCP)
    <|> Wfc   <$> (reserved "wf"         >> colon >> {-# SCC "wfCP"  #-} wfCP)
    <|> Con   <$> (reserved "constant"   >> symbolP) <*> (colon >> sortP)
    <|> Qul   <$> (reserved "qualif"     >> qualifierP sortP)
    <|> Kut   <$> (reserved "cut"        >> kvarP)
    <|> IBind <$> (reserved "bind"       >> intP) <*> symbolP <*> (colon >> {-# SCC "sortedReftP" #-} sortedReftP)

sortedReftP :: Parser SortedReft
sortedReftP = refP (RR <$> (sortP <* spaces))

wfCP :: Parser (WfC ())
wfCP = do reserved "env"
          env <- envP
          reserved "reft"
          r   <- sortedReftP
          let [w] = wfC env r ()
          return w

subCP :: Parser (SubC ())
subCP = do pos <- getPosition
           reserved "env"
           env <- envP
           reserved "lhs"
           lhs <- sortedReftP
           reserved "rhs"
           rhs <- sortedReftP
           reserved "id"
           i   <- integer <* spaces
           tag <- tagP
           pos' <- getPosition
           return $ subC' env lhs rhs i tag pos pos'

subC' env lhs rhs i tag l l'
  = case cs of
      [c] -> c
      _   -> die $ err sp $ "RHS without single conjunct at" <+> pprint l'
    where
       cs = subC env lhs rhs (Just i) tag ()
       sp = SS l l'


tagP  :: Parser [Int]
tagP  = reserved "tag" >> spaces >> brackets (sepBy intP semi)

envP  :: Parser IBindEnv
envP  = do binds <- brackets $ sepBy (intP <* spaces) semi
           return $ insertsIBindEnv binds emptyIBindEnv

intP :: Parser Int
intP = fromInteger <$> integer

defsFInfo :: [Def a] -> FInfo a
defsFInfo defs = {-# SCC "defsFI" #-} FI cm ws bs lts kts qs mempty mempty False 
  where
    cm     = M.fromList       [(cid c, c)       | Cst c       <- defs]
    ws     = M.fromList       [(thd3 $ wrft w, w) | Wfc w     <- defs]
    bs     = bindEnvFromList  [(n, x, r)        | IBind n x r <- defs]
    lts    = fromListSEnv     [(x, t)           | Con x t     <- defs]
    kts    = KS $ S.fromList  [k                | Kut k       <- defs]
    qs     =                  [q                | Qul q       <- defs]
    cid    = fromJust . sid
    -- msg    = show $ "#Lits = " ++ (show $ length consts)

---------------------------------------------------------------------
-- | Interacting with Fixpoint --------------------------------------
---------------------------------------------------------------------

fixResultP :: Parser a -> Parser (FixResult a)
fixResultP pp
  =  (reserved "SAT"   >> return Safe)
 <|> (reserved "UNSAT" >> Unsafe <$> brackets (sepBy pp comma))
 <|> (reserved "CRASH" >> crashP pp)

crashP pp
  = do i   <- pp
       msg <- many anyChar
       return $ Crash [i] msg

predSolP
  = parens (predP  <* (comma >> iQualP))


iQualP
  = upperIdP >> parens (sepBy symbolP comma)

solution1P
  = do reserved "solution:"
       k  <- kvP
       reserved ":="
       ps <- brackets $ sepBy predSolP semi
       return (k, simplify $ PAnd ps)
    where
      kvP = try kvarP <|> (KV <$> symbolP)

solutionP :: Parser (M.HashMap KVar Expr)
solutionP
  = M.fromList <$> sepBy solution1P whiteSpace

solutionFileP
  = (,) <$> fixResultP integer <*> solutionP

------------------------------------------------------------------------

remainderP p
  = do res <- p
       str <- getInput
       pos <- getPosition
       return (res, str, pos)

doParse' parser f s
  = case runParser (remainderP (whiteSpace >> parser)) 0 f s of
      Left e            -> die $ err (errorSpan e) (dErr e)
      Right (r, "", _)  -> r
      Right (_, r, l)   -> die $ err (SS l l) (dRem r)
    where
      dErr e = vcat [ "parseError"        <+> tshow e
                    , "when parsing from" <+> text f ]
      dRem r = vcat [ "doParse has leftover"
                    , nest 4 (text r)
                    , "when parsing from" <+> text f ]

errorSpan e = SS l l where l = errorPos e

parseFromFile :: Parser b -> SourceName -> IO b
parseFromFile p f = doParse' p f <$> readFile f

freshIntP :: Parser Integer
freshIntP = do n <- getState
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
 <|> (reserved "distinct" >> (Distinct <$> brackets (sepBy exprP comma)))

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
  rr' _ = rr
  rr    = rr' ""

instance Inputable Symbol where
  rr' = doParse' symbolP

instance Inputable Constant where
  rr' = doParse' constantP

instance Inputable Expr where
  rr' = doParse' exprP

instance Inputable (FixResult Integer) where
  rr' = doParse' $ fixResultP integer

instance Inputable (FixResult Integer, FixSolution) where
  rr' = doParse' solutionFileP

instance Inputable (FInfo ()) where
  rr' = {-# SCC "fInfoP" #-} doParse' fInfoP

instance Inputable Command where
  rr' = doParse' commandP

instance Inputable [Command] where
  rr' = doParse' commandsP

{-
---------------------------------------------------------------
--------------------------- Testing ---------------------------
---------------------------------------------------------------

-- A few tricky predicates for parsing
-- myTest1 = "((((v >= 56320) && (v <= 57343)) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o ((i - o) - 1)))) && (((numchars a o (i - (o -1))) >= 0) && (((i - o) - 1) >= 0)))) && ((not (((v >= 56320) && (v <= 57343)))) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o (i - o)))) && ((numchars a o (i - o)) >= 0))))"
--
-- myTest2 = "len x = len y - 1"
-- myTest3 = "len x y z = len a b c - 1"
-- myTest4 = "len x y z = len a b (c - 1)"
-- myTest5 = "x >= -1"
-- myTest6 = "(bLength v) = if n > 0 then n else 0"
-- myTest7 = "(bLength v) = (if n > 0 then n else 0)"
-- myTest8 = "(bLength v) = (n > 0 ? n : 0)"


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
