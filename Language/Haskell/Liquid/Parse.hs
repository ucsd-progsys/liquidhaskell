{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections #-}

module Language.Haskell.Liquid.Parse (
  hsSpecificationP
) where

import Control.Monad
import Text.Parsec
import qualified Text.Parsec.Token as Token
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Control.Applicative ((<$>), (<*), (<*>))
import Data.Char (toLower, isLower, isSpace, isAlpha)
import Data.List (partition)
import Data.Monoid (mempty)

import Language.Fixpoint.Types

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Measure
import Language.Fixpoint.Names (listConName, propConName, tupConName)
import Language.Fixpoint.Misc hiding (dcolon, dot)
import Language.Fixpoint.Parse 

dot        = Token.dot        lexer
braces     = Token.braces     lexer
angles     = Token.angles     lexer

----------------------------------------------------------------------------------
------------------------------------ BareTypes -----------------------------------
----------------------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType 

bareTypeP   
  =  try bareFunP
 <|> bareAllP
 <|> bareAllExprP
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
 <|> try (liftM2 bAppTy lowerIdP bareTyArgP)
 <|> try (liftM2 bRVar lowerIdP monoPredicateP)
 <|> liftM3 bCon upperIdP predicatesP (sepBy bareTyArgP blanks)

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  liftM2 bLst (brackets bareTypeP) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM3 bCon upperIdP predicatesP (return []))
 <|> liftM2 bRVar lowerIdP monoPredicateP 

bareTyArgP 
  =  try (braces $ liftM RExprArg exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)

bareAtomNoAppP 
  =  refP bbaseNoAppP 
 <|> try (dummyP (bbaseNoAppP <* spaces))

bareAllExprP 
  = do reserved "forall"
       zs <- brackets $ sepBy1 exBindP comma 
       dot
       t  <- bareTypeP
       return $ foldr (uncurry RAllE) t zs
 
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

tyVarIdP :: Parser String
tyVarIdP = condIdP alphanums (isLower . head) 
           where alphanums = ['a'..'z'] ++ ['0'..'9']

predVarDefsP 
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP
  = liftM3 bPVar predVarIdP dcolon predVarTypeP

predVarIdP 
  = stringSymbol <$> tyVarIdP

bPVar p _ xts  = PV p τ τxs 
  where (_, τ) = safeLast "bPVar last" xts
        τxs    = [ (τ, x, EVar x) | (x, τ) <- init xts ]

predVarTypeP :: Parser [(Symbol, BSort)]
predVarTypeP = do t <- bareTypeP
                  let (xs, ts, t') = bkArrow $ thd3 $ bkUniv $ t
                  if isPropBareType t' 
                    then return $ zip xs (toRSort <$> ts) 
                    else parserFail $ "Predicate Variable with non-Prop output sort: " ++ showpp t


xyP lP sepP rP
  = liftM3 (\x _ y -> (x, y)) lP (spaces >> sepP) rP

data ArrowSym = ArrowFun | ArrowPred

arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

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
  = tempSymbol "db" <$> freshIntP

  -- = stringSymbol <$> positionNameP 




bbindP = lowerIdP <* dcolon 

bindP  = liftM stringSymbol (lowerIdP <* colon)

bareArrow b t1 ArrowFun t2
  = rFun b t1 t2
bareArrow _ t1 ArrowPred t2
  = foldr (rFun dummySymbol) t2 (getClasses t1)


isPropBareType (RApp tc [] _ _) = tc == propConName
isPropBareType _                = False


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

symsP
  = do reserved "\\"
       ss <- sepBy symbolP spaces
       reserved "->"
       return $ (, dummyRSort) <$> ss
 <|> return []

refasP :: Parser [Refa]
refasP  =  (try (brackets $ sepBy (RConc <$> predP) semi)) 
       <|> liftM ((:[]) . RConc) predP

predicatesP 
   =  try (angles $ sepBy1 predicate1P comma) 
  <|> return []

predicate1P 
   =  try (liftM2 RPoly symsP (refP bbaseP))
  <|> liftM (RMono [] . predUReft) monoPredicate1P
  <|> (braces $ liftM2 bRPoly symsP refasP)

monoPredicateP 
   = try (angles monoPredicate1P) 
  <|> return mempty

monoPredicate1P
   =  try (reserved "True" >> return mempty)
  <|> try (liftM pdVar (parens predVarUseP))
  <|> liftM pdVar predVarUseP 

predVarUseP 
 = do p  <- predVarIdP
      xs <- sepBy exprP spaces
      return $ PV p dummyTyId [ (dummyTyId, dummySymbol, x) | x <- xs ]


------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRPoly []    _    = errorstar "Parse.bRPoly empty list"
bRPoly syms expr = RPoly ss $ bRVar dummyName top $ Reft(v, expr)
  where (ss, (v, _)) = (init syms, last syms)

bRVar α p r               = RVar α (U r p)
bLst t rs r               = RApp listConName [t] rs (reftUReft r) 

bTup [t] _ r | isTauto r  = t
             | otherwise  = t `strengthen` (reftUReft r) 
bTup ts rs r              = RApp tupConName ts rs (reftUReft r)

bCon b [RMono _ r1] [] r  = RApp b [] [] (r1 `meet` (reftUReft r)) 
bCon b rs ts r            = RApp b ts rs (reftUReft r)

bAppTy v t r              = RAppTy (RVar v top) t (reftUReft r)




reftUReft      = (`U` mempty)
predUReft      = (U dummyReft) 
dummyReft      = top
dummyTyId      = ""
dummyRSort     = ROth "dummy"

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty ctor 
  = Meas    (Measure.Measure ty ctor) 
  | Assm    (LocSymbol, ty) 
  | Assms   ([LocSymbol], ty)
  | Impt    Symbol
  | DDecl   DataDecl
  | Incl    FilePath
  | Invt    (Located ty)
  | Alias   (RTAlias String BareType)
  | PAlias  (RTAlias Symbol Pred)
  | Embed   (Located String, FTycon)
  | Qualif  Qualifier
  | Decr    (Symbol, [Int])
  | Strict  Symbol

-- mkSpec                 ::  String -> [Pspec ty LocSymbol] -> Measure.Spec ty LocSymbol
mkSpec name xs         = Measure.qualifySpec name $ Measure.Spec 
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.sigs       = [a | Assm   a <- xs] 
                      ++ [(y, t) | Assms (ys, t) <- xs, y <- ys]
  , Measure.invariants = [t | Invt   t <- xs] 
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.paliases   = [p | PAlias p <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.decr       = [d | Decr d   <- xs]
  , Measure.strict     = S.fromList [s | Strict s <- xs]
  }

type BareSpec = (Measure.Spec BareType Symbol)

specificationP :: Parser BareSpec 
specificationP 
  = do reserved "module"
       reserved "spec"
       S name <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace)
       return $ mkSpec name xs 


specP :: Parser (Pspec BareType Symbol)
specP 
  = try (reserved "assume"    >> liftM Assm   tyBindP   )
    <|> (reserved "assert"    >> liftM Assm   tyBindP   )
    <|> (reserved "measure"   >> liftM Meas   measureP  ) 
    <|> (reserved "import"    >> liftM Impt   symbolP   )
    <|> (reserved "data"      >> liftM DDecl  dataDeclP )
    <|> (reserved "include"   >> liftM Incl   filePathP )
    <|> (reserved "invariant" >> liftM Invt   invariantP)
    <|> (reserved "type"      >> liftM Alias  aliasP    )
    <|> (reserved "predicate" >> liftM PAlias paliasP   )
    <|> (reserved "embed"     >> liftM Embed  embedP    )
    <|> (reserved "qualif"    >> liftM Qualif qualifierP)
    <|> (reserved "Decrease"  >> liftM Decr   decreaseP )
    <|> (reserved "Strict"    >> liftM Strict strictP   )
    <|> ({- DEFAULT -}           liftM Assms  tyBindsP  )

strictP :: Parser Symbol
strictP = binderP

decreaseP :: Parser (Symbol, [Int])
decreaseP = mapSnd f <$> liftM2 (,) binderP (spaces >> (many integer))
  where f = ((\n -> fromInteger n - 1) <$>)
filePathP :: Parser FilePath
filePathP = angles $ many1 pathCharP
  where pathCharP = choice $ char <$> pathChars 
        pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

tyBindsP    :: Parser ([LocSymbol], BareType)
tyBindsP = xyP (sepBy (locParserP binderP) comma) dcolon genBareTypeP

tyBindP    :: Parser (LocSymbol, BareType)
tyBindP    = xyP (locParserP binderP) dcolon genBareTypeP

locParserP :: Parser a -> Parser (Located a)
locParserP p = liftM2 Loc getPosition p

invariantP   = locParserP genBareTypeP 

genBareTypeP
  = bareTypeP -- liftM generalize bareTypeP 

embedP 
  = xyP (locParserP upperIdP) (reserved "as") fTyConP


aliasP  = rtAliasP id           bareTypeP
paliasP = rtAliasP stringSymbol predP

rtAliasP f bodyP
  = do pos  <- getPosition
       name <- upperIdP
       spaces
       args <- sepBy aliasIdP spaces
       whiteSpace >> reservedOp "=" >> whiteSpace
       body <- bodyP 
       let (tArgs, vArgs) = partition (isLower . head) args
       return $ RTA name (f <$> tArgs) (f <$> vArgs) body pos

aliasIdP :: Parser String
aliasIdP = condIdP (['A' .. 'Z'] ++ ['a'..'z'] ++ ['0'..'9']) (isAlpha . head) 

measureP :: Parser (Measure.Measure BareType Symbol)
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
      Just bt | isPropBareType bt -> Measure.P <$> predP 
      _                           -> Measure.E <$> exprP
    where outTy (RAllT _ t)    = outTy t
          outTy (RAllP _ t)    = outTy t
          outTy (RFun _ _ t _) = Just t
          outTy _              = Nothing

binderP :: Parser Symbol
binderP =  try $ liftM stringSymbol (idP badc)
       <|> liftM pwr (parens (idP bad))
       where idP p  = many1 (satisfy (not . p))
             badc c = (c == ':') || (c == ',') || bad c
             bad c  = isSpace c || c `elem` "(,)"
             pwr s  = stringSymbol $ "(" ++ s ++ ")" 
             
grabs p = try (liftM2 (:) p (grabs p)) 
       <|> return []

measureDefP :: Parser Measure.Body -> Parser (Measure.Def Symbol)
measureDefP bodyP
  = do mname   <- locParserP symbolP
       (c, xs) <- {- ORIGINAL parens $ -} measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP 
       whiteSpace
       let xs'  = (stringSymbol . val) <$> xs
       return   $ Measure.Def mname (stringSymbol c) xs' body

-- ORIGINAL
-- measurePatP :: Parser (String, [LocString])
-- measurePatP
--   =  try (liftM2 (,)   upperIdP (sepBy locLowerIdP whiteSpace))
--  <|> try (liftM3 (\x c y -> (c, [x,y])) locLowerIdP colon locLowerIdP)
--  <|> (brackets whiteSpace  >> return ("[]",[])) 

measurePatP :: Parser (String, [LocString])
measurePatP 
  =  try tupPatP 
 <|> try (parens conPatP)
 <|> try (parens consPatP)
 <|>     (parens nilPatP)

tupPatP  = mkTupPat  <$> (parens       $  sepBy locLowerIdP comma)
conPatP  = (,)       <$> dataConNameP <*> sepBy locLowerIdP whiteSpace 
consPatP = mkConsPat <$> locLowerIdP  <*> colon <*> locLowerIdP
nilPatP  = mkNilPat  <$> brackets whiteSpace 

mkTupPat zs     = (tupDataCon (length zs), zs)
mkNilPat _      = ("[]", []    )
mkConsPat x c y = (":" , [x, y]) 

tupDataCon n    = "(" ++ replicate (n - 1) ',' ++ ")"
locLowerIdP = locParserP lowerIdP 

{- len (Cons x1 x2 ...) = e -}


-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP 
  =   (braces $ sepBy predTypeDDP comma)
  <|> (sepBy (parens predTypeDDP) spaces)

predTypeDDP 
  = liftM2 (,) bbindP bareTypeP

dataConP
  = do x   <- dataConNameP 
       spaces
       xts <- dataConFieldsP
       return (x, xts)

-- dataConNameP = symbolString <$> binderP -- upperIdP
dataConNameP 
  =  try upperIdP 
 <|> pwr <$> parens (idP bad)
  where 
     idP p  = many1 (satisfy (not . p))
     bad c  = isSpace c || c `elem` "(,)"
     pwr s  = "(" ++ s ++ ")" 

dataSizeP 
  = (brackets $ (Just . mkFun) <$> lowerIdP)
  <|> return Nothing
  where mkFun s = \x -> EApp (stringSymbol s) [EVar x] 

dataDeclP
  = do pos <- getPosition
       x   <- upperIdP
       spaces
       fsize <- dataSizeP
       spaces
       ts  <- sepBy tyVarIdP spaces
       ps  <- predVarDefsP
       whiteSpace >> reservedOp "=" >> whiteSpace
       dcs <- sepBy dataConP (reserved "|")
       whiteSpace
       -- spaces
       -- reservedOp "--"
       return $ D x ts ps dcs pos fsize

---------------------------------------------------------------------
------------ Interacting with Fixpoint ------------------------------
---------------------------------------------------------------------

-- remainderP p  
--   = do res <- p
--        str <- stateInput <$> getParserState
--        return (res, str) 
-- 
-- doParse' parser f s
--   = case parse (remainderP p) f s of
--       Left e         -> errorstar $ printf "parseError %s\n when parsing from %s\n" 
--                                       (show e) f 
--       Right (r, "")  -> r
--       Right (_, rem) -> errorstar $ printf "doParse has leftover when parsing: %s\nfrom file %s\n"
--                                       rem f
--   where p = whiteSpace >> parser

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

instance Inputable BareType where
  rr' = doParse' bareTypeP 

instance Inputable (Measure.Measure BareType Symbol) where
  rr' = doParse' measureP

instance Inputable BareSpec where
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
