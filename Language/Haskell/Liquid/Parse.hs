{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections #-}

module Language.Haskell.Liquid.Parse (
  Inputable (..)
, hsSpecificationP
) where

-- import TysWiredIn   (eqDataConId, ltDataConId, gtDataConId)
import Control.Monad
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Printf  (printf)
import qualified Text.Parsec.Token as Token
import qualified Data.HashMap.Strict as M

import Control.Applicative ((<$>), (<*))
import Data.Char (toLower, isLower, isSpace)

import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Measure
import Outputable (showPpr)
import Language.Haskell.Liquid.FileNames (boolConName, listConName, tupConName)

--------------------------------------------------------------------

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
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
                                     ]
           , Token.reservedOpNames = [ "+", "-", "*", "/" 
                                     , "<", ">", "<=", ">=", "=", "!="
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

lexer      = Token.makeTokenParser languageDef
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
brackets   = Token.brackets   lexer
braces     = Token.braces     lexer
angles     = Token.angles     lexer
semi       = Token.semi       lexer
colon      = Token.colon      lexer
comma      = Token.comma      lexer
dot        = Token.dot        lexer
whiteSpace = Token.whiteSpace lexer
-- identifier = Token.identifier lexer


blanks  = many (satisfy (`elem` [' ', '\t']))

integer =   try (liftM toInt is) 
       <|>  liftM (negate . toInt) (char '-' >> is)
  where is      = liftM2 (\is _ -> is) (many1 digit) blanks 
        toInt s = (read s) :: Integer 

----------------------------------------------------------------
------------------------- Expressions --------------------------
----------------------------------------------------------------

condIdP  :: [Char] -> (String -> Bool) -> Parser String
condIdP chars f 
  = do c  <- letter
       cs <- many (satisfy (`elem` chars))
       blanks
       if f (c:cs) then return (c:cs) else parserZero

tyVarIdP :: Parser String
tyVarIdP = condIdP alphanums (isLower . head) 
           where alphanums = ['a'..'z'] ++ ['0'..'9']

lowerIdP :: Parser String
lowerIdP = condIdP symChars (isLower . head)

upperIdP :: Parser String
upperIdP = condIdP symChars (not . isLower . head)

symbolP :: Parser Symbol
symbolP = liftM stringSymbol symCharsP 


constantP :: Parser Constant
constantP = liftM I integer

exprP :: Parser Expr 
exprP =  expr2P <|> lexprP

lexprP :: Parser Expr 
lexprP   
  =  try (parens exprP)
 <|> try (parens exprCastP)
 <|> try (parens $ condP EIte exprP)
 <|> try exprFunP
--  <|> try (liftM makeEDat upperIdP)
 <|> try (liftM (EVar . stringSymbol) upperIdP)
 <|> liftM EVar symbolP
 <|> liftM ECon constantP
 <|> (reserved "_|_" >> return EBot)

-- RJ: Removing EDat 
-- makeEDat s = wiredEDat $ lookup s wiredSorts
--   where wiredEDat (Just wInfo) = EDat (fst wInfo) (snd wInfo)
--         wiredEDat _            = EVar $ stringSymbol s 
-- 
-- EQ :: Ordering
-- LT :: Ordering
-- GT :: Ordering

-- wiredSorts = [] 
-- [ ("EQ", (varSymbol eqDataConId, primOrderingSort))
-- , ("LT", (varSymbol ltDataConId, primOrderingSort))
-- , ("GT", (varSymbol gtDataConId, primOrderingSort))
-- ]




exprFunP       =  (try exprFunSpacesP) <|> (try exprFunSemisP) <|> exprFunCommasP

exprFunSpacesP = parens $ liftM2 EApp symbolP (sepBy exprP spaces) 
exprFunCommasP = liftM2 EApp symbolP (parens        $ sepBy exprP comma)
exprFunSemisP  = liftM2 EApp symbolP (parenBrackets $ sepBy exprP semi)

parenBrackets  = parens . brackets 

-- exprFunP       =  (try exprFunSpacesP) <|> exprFunCommasP
--exprFunCommasP = liftM2 EApp symbolP argsP
--  where argsP  =  try (parens $ brackets esP) 
--              <|> parens esP
--        esP    = sepBy exprP comma 

expr2P = buildExpressionParser bops lexprP

bops = [ [Infix  (reservedOp "*"   >> return (EBin Times)) AssocLeft]
       , [Infix  (reservedOp "/"   >> return (EBin Div  )) AssocLeft]
       , [Infix  (reservedOp "+"   >> return (EBin Plus )) AssocLeft]
       , [Infix  (reservedOp "-"   >> return (EBin Minus)) AssocLeft]
       , [Infix  (reservedOp "mod" >> return (EBin Mod  )) AssocLeft]
       ]

exprCastP
  = do e  <- exprP 
       ((try dcolon) <|> colon)
       so <- sortP
       return $ ECst e so

sortP
  =   try (string "Integer" >> return FInt)
  <|> try (string "Int"     >> return FInt)
  <|> try (string "int"     >> return FInt)
  <|> try (string "Bool"    >> return FBool)
--   <|> (symCharsP >>= return . FPtr . FLoc . stringSymbol) 


symCharsP = (condIdP symChars (\_ -> True))

---------------------------------------------------------------------
-------------------------- Predicates -------------------------------
---------------------------------------------------------------------

predP :: Parser Pred
predP =  try (parens pred2P)
     <|> try (parens $ condP pIte predP)
     <|> try (reservedOp "&&" >> liftM PAnd predsP)
     <|> try (reservedOp "||" >> liftM POr  predsP)
     <|> (qmP >> liftM PBexp exprP)
     <|> (reserved "true"  >> return PTrue)
     <|> (reserved "false" >> return PFalse)
     <|> (try predrP)
     <|> (try (liftM PBexp exprFunP))

qmP    = reserved "?" <|> reserved "Bexp"

pred2P = buildExpressionParser lops predP 

predsP = brackets $ sepBy predP semi

lops = [ [Prefix (reservedOp "~"   >> return PNot)]
       , [Infix  (reservedOp "&&"  >> return (\x y -> PAnd [x,y])) AssocRight]
       , [Infix  (reservedOp "||"  >> return (\x y -> POr  [x,y])) AssocRight]
       , [Infix  (reservedOp "=>"  >> return PImp) AssocRight]
       , [Infix  (reservedOp "<=>" >> return PIff) AssocRight]]
       
predrP = do e1    <- expr2P
            r     <- brelP
            e2    <- expr2P 
            return $ r e1 e2

brelP ::  Parser (Expr -> Expr -> Pred)
brelP =  (reservedOp "="  >> return (PAtom Eq))
     <|> (reservedOp "!=" >> return (PAtom Ne))
     <|> (reservedOp "<"  >> return (PAtom Lt))
     <|> (reservedOp "<=" >> return (PAtom Le))
     <|> (reservedOp ">"  >> return (PAtom Gt))
     <|> (reservedOp ">=" >> return (PAtom Ge))

condP f bodyP 
  = do p  <- predP 
       reserved "?"
       b1 <- bodyP 
       colon
       b2 <- bodyP 
       return $ f p b1 b2

----------------------------------------------------------------------------------
------------------------------------ BareTypes -----------------------------------
----------------------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType 

bareTypeP   
  =  try bareFunP
 <|> bareAllP
 <|> bareExistsP
 <|> bareAtomP 
 
bareArgP 
  =  bareAtomP  
 <|> parens bareTypeP

bareAtomP 
  =  refP bbaseP 
 <|> try (dummyP (bbaseP <* spaces))

bbaseP :: Parser (Reft -> BareType)
bbaseP 
  =  liftM2 bLst (brackets bareTypeP) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM2 bRVar lowerIdP monoPredicateP)
 <|> liftM3 bCon upperIdP predicatesP (sepBy bareTyArgP blanks)

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  liftM2 bLst (brackets bareTypeP) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM3 bCon upperIdP predicatesP (return []))
 <|> liftM2 bRVar lowerIdP monoPredicateP 


bareTyArgP 
  =  bareAtomNoAppP
 <|> parens bareTypeP

bareAtomNoAppP 
  =  refP bbaseNoAppP 
 <|> try (dummyP (bbaseNoAppP <* spaces))




bareExistsP 
  = do reserved "exists"
       zs <- brackets $ sepBy1 exBindP comma 
       dot
       t  <- bareTypeP
       return $ foldr (uncurry REx) t zs
     
exBindP 
  = xyP binderP colon bareTypeP 
  

bareAllP 
  = do reserved "forall"
       as <- many tyVarIdP -- sepBy1 tyVarIdP comma
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ foldr RAllT (foldr RAllP t ps) as

predVarDefsP 
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP
  = liftM3 bPVar predVarIdP dcolon predVarTypeP

predVarIdP 
  = stringSymbol <$> tyVarIdP 

bPVar p _ xts  = PV p τ τxs 
  where (_, τ) = last xts
        τxs    = [ (τ, x, x) | (x, τ) <- init xts ]

predVarTypeP :: Parser [(Symbol, BSort)]
predVarTypeP = do t <- bareTypeP
                  let (xs, ts, t') = bkArrow $ thd3 $ bkUniv $ t
                  if isBoolBareType t' 
                    then return $ zip xs (toRSort <$> ts) 
                    else parserFail $ "Predicate Variable with non-Bool output sort: " ++ showPpr t

-- predVarTypeP 
--   =  try ((liftM (: []) predVarArgP) <* reserved "->" <* reserved boolConName)
--  <|> liftM2 (:) predVarArgP (reserved "->" >> predVarTypeP)

-- predVarArgP = xyP argP spaces bareSortP {- PREDARGS tyVarIdP -}
--   where argP  = stringSymbol <$> argP'
--         argP' = try (lowerIdP <* colon) <|> positionNameP
        
-- bareSortP :: Parser BSort
-- bareSortP = toRSort <$> bareTypeP

xyP lP sepP rP
  = liftM3 (\x _ y -> (x, y)) lP (spaces >> sepP) rP

data ArrowSym = ArrowFun | ArrowPred

arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

-- bareFun2P
--   = do t1 <- bareArgP 
--        a  <- arrowP
--        t2 <- bareTypeP
--        return $ bareArrow dummyBind t1 a t2 

positionNameP = dummyNamePos <$> getPosition
  
dummyNamePos pos  = "dummy." ++ name ++ ['.'] ++ line ++ ['.'] ++ col
    where name    = san <$> sourceName pos
          line    = show $ sourceLine pos  
          col     = show $ sourceColumn pos  
          san '/' = '.'
          san c   = toLower c

bareFunP  
  = do b  <- try bindP <|> dummyBindP 
       t1 <- bareArgP 
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow b t1 a t2 

dummyBindP 
  = stringSymbol <$> positionNameP -- (return dummyBind) -- (positionNameP)

bbindP = lowerIdP <* dcolon 

bindP  = liftM stringSymbol (lowerIdP <* colon)

dcolon = string "::" <* spaces

bareArrow b t1 ArrowFun t2
  = rFun b t1 t2
bareArrow _ t1 ArrowPred t2
  = foldr (rFun dummySymbol) t2 (getClasses t1)

isBoolBareType (RApp tc [] _ _) = tc == boolConName
isBoolBareType _                = False

getClasses (RApp tc ts _ _) 
  | isTuple tc
  = getClass `fmap` ts 
getClasses t 
  = [getClass t]
getClass (RApp c ts _ _)
  = RCls c ts
getClass t
  = errorstar $ "Cannot convert " ++ (show t) ++ " to Class"

dummyP ::  Monad m => m (Reft -> b) -> m b
dummyP fm 
  = fm `ap` return dummyReft 

refP :: Parser (Reft -> a) -> Parser a
refP kindP 
  = braces $ do
      v   <- symbolP 
      colon
      t   <- kindP
      reserved "|"
      ras <- refasP 
      return $ t (Reft (v, ras))

refasP :: Parser [Refa]
refasP  =  (try (brackets $ sepBy (RConc <$> predP) semi)) 
       <|> liftM ((:[]) . RConc) predP

predicatesP 
   =  try (angles $ sepBy1 predicate1P comma) 
  <|> return []

predicate1P 
   =  try (liftM RPoly (refP bbaseP))
  <|> liftM (RMono . predUReft) monoPredicate1P

monoPredicateP 
   = try (angles monoPredicate1P) 
  <|> return pdTrue

monoPredicate1P
   =  try (reserved "True" >> return pdTrue)
  <|> try (liftM pdVar (parens predVarUseP))
  <|> liftM pdVar predVarUseP 

predVarUseP 
 = do p  <- predVarIdP
      xs <- sepBy predVarIdP spaces
      return $ PV p dummyTyId [ (dummyTyId, dummySymbol, x) | x <- xs ]


------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bLst t rs r    = RApp listConName [t] rs (reftUReft r) 
bTup [t] _ _   = t
bTup ts rs r   = RApp tupConName ts rs (reftUReft r)
bRVar α p r    = RVar α (U r p)

bCon b [RMono r1] [] r = RApp b [] [] (r1 `meet` (reftUReft r)) 
bCon b rs ts r         = RApp b ts rs (reftUReft r)




reftUReft      = (`U` pdTrue)
predUReft      = (U dummyReft) 
dummyReft      = Reft (dummySymbol, [])
dummyTyId      = ""

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty bndr 
  = Meas (Measure.Measure ty bndr) 
  | Assm (bndr, ty) 
  | Impt  Symbol
  | DDecl DataDecl
  | Incl  FilePath
  | Invt  ty
  | Alias (RTAlias String BareType)
  | Embed (String, FTycon)

mkSpec name xs         = Measure.qualifySpec name $ Measure.Spec 
  { Measure.measures   = [m | Meas  m <- xs]
  , Measure.sigs       = [a | Assm  a <- xs]
  , Measure.invariants = [t | Invt  t <- xs] 
  , Measure.imports    = [i | Impt  i <- xs]
  , Measure.dataDecls  = [d | DDecl d <- xs]
  , Measure.includes   = [q | Incl  q <- xs]
  , Measure.aliases    = [a | Alias a <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  }

specificationP 
  = do reserved "module"
       reserved "spec"
       S name <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace) --(liftM2 const specP whiteSpace)
       return $ mkSpec name xs 


specP 
  = try (reserved "assume"    >> liftM Assm  tyBindP)
    <|> (reserved "assert"    >> liftM Assm  tyBindP)
    <|> (reserved "measure"   >> liftM Meas  measureP) 
    <|> (reserved "import"    >> liftM Impt  symbolP)
    <|> (reserved "data"      >> liftM DDecl dataDeclP)
    <|> (reserved "include"   >> liftM Incl  filePathP)
    <|> (reserved "invariant" >> liftM Invt  genBareTypeP)
    <|> (reserved "type"      >> liftM Alias aliasP)
    <|> (reserved "embed"     >> liftM Embed embedP)
    <|> ({- DEFAULT -}           liftM Assm  tyBindP)

filePathP :: Parser FilePath
filePathP = angles $ many1 pathCharP
  where pathCharP = choice $ char <$> pathChars 
        pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

tyBindP 
  = xyP binderP dcolon genBareTypeP

genBareTypeP
  = liftM generalize bareTypeP 

embedP 
  = xyP upperIdP (reserved "as") fTyConP

fTyConP
  =   (reserved "int"  >> return intFTyCon)
  <|> (reserved "bool" >> return boolFTyCon)
  <|> (stringFTycon   <$> upperIdP)



aliasP 
  = do name <- upperIdP
       spaces
       args <- sepBy tyVarIdP spaces
       whiteSpace >> reservedOp "=" >> whiteSpace
       body <- bareTypeP
       return $ RTA name args body

measureP 
  = do (x, ty) <- tyBindP  
       whiteSpace
       eqns    <- grabs $ measureDefP $ (rawBodyP <|> tyBodyP ty)
       return   $ Measure.mkM x ty eqns   

rawBodyP 
  = braces $ do
      v <- symbolP 
      reserved "|"
      p <- predP
      return $ Measure.R v p

-- tyBodyP :: BareType -> Parser Measure.Body
tyBodyP ty 
  = case outTy ty of
      Just bt | isBoolBareType bt -> Measure.P <$> predP 
      _                           -> Measure.E <$> exprP
    where outTy (RAllT _ t)    = outTy t
          outTy (RAllP _ t)    = outTy t
          outTy (RFun _ _ t _) = Just t
          outTy _              = Nothing



binderP :: Parser Symbol
binderP =  try $ liftM stringSymbol (idP badc)
       <|> liftM pwr (parens (idP bad))
       where -- idP    = many1 (satisfy (not . bad))
             -- idcP   = many1 (satisfy (not . badc))
             idP p  = many1 (satisfy (not . p))
             badc c = (c == ':') ||  bad c
             bad c  = isSpace c || c `elem` "()"
             pwr s  = stringSymbol $ "(" ++ s ++ ")" 
             
grabs p = try (liftM2 (:) p (grabs p)) 
       <|> return []

measureDefP :: Parser Measure.Body -> Parser (Measure.Def Symbol)
measureDefP bodyP
  = do mname   <- symbolP
       (c, xs) <- parens $ measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP 
       whiteSpace
       return   $ Measure.Def mname (stringSymbol c) (stringSymbol <$> xs) body

measurePatP :: Parser (String, [String])
measurePatP
  =  try (liftM2 (,)   upperIdP (sepBy lowerIdP whiteSpace))
 <|> try (liftM3 (\x c y -> (c, [x,y])) lowerIdP colon lowerIdP)
 <|> (brackets whiteSpace  >> return ("[]",[])) 

{- len (Cons x1 x2 ...) = e -}


-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP 
  =   braces $ sepBy predTypeDDP comma 
  <|> sepBy (parens predTypeDDP) spaces

predTypeDDP 
  = {- parens $ -} liftM2 (,) bbindP bareTypeP

dataConP
  = do x <- upperIdP
       spaces
       xts <- dataConFieldsP -- sepBy predTypeDDP spaces
       return (x, xts)



dataDeclP
  = do x   <- upperIdP
       spaces
       ts  <- sepBy tyVarIdP spaces
       ps  <- predVarDefsP
       whiteSpace >> reservedOp "=" >> whiteSpace
       dcs <- sepBy dataConP (reserved "|")
       whiteSpace
       -- spaces
       -- reservedOp "--"
       return $ D x ts ps dcs

---------------------------------------------------------------------
------------ Interacting with Fixpoint ------------------------------
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
    
--iQualP 
--  = upperIdP >> many bracketsWithStuffP
--
--bracketsWithStuffP
--  = (brackets $ many (satisfy $ not . (`elem` "[]"))) >> return ()

iQualP
  = upperIdP >> (parens $ sepBy symbolP comma)

solution1P
  = do reserved "solution:" 
       k  <- symbolP 
       reserved ":=" 
       ps <- brackets $ sepBy predSolP semi
       return (k, simplify $ PAnd ps)

solutionP 
  = M.fromList <$> sepBy solution1P whiteSpace

solutionFileP 
  = liftM2 (,) (fixResultP integer) solutionP

------------------------------------------------------------------------

remainderP p  
  = do res <- p
       str <- stateInput <$> getParserState
       return (res, str) 

doParse' parser f s
  = case parse (remainderP p) f s of
      Left e         -> errorstar $ printf "parseError %s\n when parsing %s\nfrom %s\n" 
                                      (show e) s f 
      Right (r, "")  -> r
      Right (_, rem) -> errorstar $ printf "doParse has leftover when parsing: %s\nfrom file %s\n"
                                      rem f
  where p = whiteSpace >> parser

grabUpto p  
  =  try (lookAhead p >>= return . Just)
 <|> try (eof         >> return Nothing)
 <|> (anyChar >> grabUpto p)

betweenMany leftP rightP p 
  = do z <- grabUpto leftP
       case z of
         Just _  -> liftM2 (:) (between leftP rightP p) (betweenMany leftP rightP p)
         Nothing -> return []

-- specWrap  = between     (string "{-@" >> spaces) (spaces >> string "@-}")
specWraps = betweenMany (string "{-@" >> spaces) (spaces >> string "@-}")

----------------------------------------------------------------------------------------
------------------------ Bundling Parsers into a Typeclass -----------------------------
----------------------------------------------------------------------------------------

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

instance Inputable BareType where
  rr' = doParse' bareTypeP 

instance Inputable (Measure.Measure BareType Symbol) where
  rr' = doParse' measureP

instance Inputable (Measure.Spec BareType Symbol) where
  rr' = doParse' specificationP

hsSpecificationP name 
  = doParse' $ liftM (mkSpec name) $ specWraps specP

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
