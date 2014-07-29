{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections, OverloadedStrings #-}

module Language.Haskell.Liquid.Parse
  (hsSpecificationP, lhsSpecificationP, specSpecificationP)
  where

import Control.Monad
import Text.Parsec
import Text.Parsec.Error ( messageString 
                         , errorMessages
                         , newErrorMessage
                         , errorPos
                         , Message (..)) 
import Text.Parsec.Pos   (newPos) 

import qualified Text.Parsec.Token as Token
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import Data.Interned

import Control.Applicative ((<$>), (<*), (<*>))
import Data.Char (toLower, isLower, isSpace, isAlpha)
import Data.List (foldl', partition)
import Data.Monoid (mempty)

import GHC (mkModuleName, ModuleName)
import Text.PrettyPrint.HughesPJ    (text)

import Language.Preprocessor.Unlit (unlit)

import Language.Fixpoint.Types hiding (Def, R)

import Language.Haskell.Liquid.GhcMisc
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Measure
import Language.Fixpoint.Names (listConName, hpropConName, propConName, tupConName, headSym)
import Language.Fixpoint.Misc hiding (dcolon, dot)
import Language.Fixpoint.Parse hiding (angles)

----------------------------------------------------------------------------
-- Top Level Parsing API ---------------------------------------------------
----------------------------------------------------------------------------

-------------------------------------------------------------------------------
hsSpecificationP :: SourceName -> String -> Either Error (ModName, Measure.BareSpec)
-------------------------------------------------------------------------------

hsSpecificationP = parseWithError $ do
    name <-  try (lookAhead $ skipMany (commentP >> spaces)
                           >> reserved "module" >> symbolP)
         <|> return "Main"
    liftM (mkSpec (ModName SrcImport $ mkModuleName $ symbolString name)) $ specWraps specP

-------------------------------------------------------------------------------
lhsSpecificationP :: SourceName -> String -> Either Error (ModName, Measure.BareSpec)
-------------------------------------------------------------------------------

lhsSpecificationP sn s = hsSpecificationP sn $ unlit sn s

commentP =  simpleComment (string "{-") (string "-}")
        <|> simpleComment (string "--") newlineP
        <|> simpleComment (string "\\") newlineP
        <|> simpleComment (string "#")  newlineP

simpleComment open close = open >> manyTill anyChar (try close)

newlineP = try (string "\r\n") <|> string "\n" <|> string "\r"


-- | Used to parse .spec files

--------------------------------------------------------------------------
specSpecificationP  :: SourceName -> String -> Either Error (ModName, Measure.BareSpec)
--------------------------------------------------------------------------
specSpecificationP  = parseWithError specificationP 

specificationP :: Parser (ModName, Measure.BareSpec)
specificationP 
  = do reserved "module"
       reserved "spec"
       name   <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace)
       return $ mkSpec (ModName SpecImport $ mkModuleName $ symbolString name) xs

---------------------------------------------------------------------------
parseWithError :: Parser a -> SourceName -> String -> Either Error a 
---------------------------------------------------------------------------
parseWithError parser f s
  = case runParser (remainderP (whiteSpace >> parser)) 0 f s of
      Left e            -> Left  $ parseErrorError f e
      Right (r, "", _)  -> Right $ r
      Right (_, rem, _) -> Left  $ parseErrorError f $ remParseError f s rem 

---------------------------------------------------------------------------
parseErrorError     :: SourceName -> ParseError -> Error
---------------------------------------------------------------------------
parseErrorError f e = ErrParse sp msg lpe
  where 
    pos             = errorPos e
    sp              = sourcePosSrcSpan pos 
    msg             = text $ "Error Parsing Specification from: " ++ f
    lpe             = LPE pos (eMsgs e)
    eMsgs           = fmap messageString . errorMessages 

---------------------------------------------------------------------------
remParseError       :: SourceName -> String -> String -> ParseError 
---------------------------------------------------------------------------
remParseError f s r = newErrorMessage msg $ newPos f line col
  where 
    msg             = Message "Leftover while parsing"
    (line, col)     = remLineCol s r 

remLineCol          :: String -> String -> (Int, Int)
remLineCol src rem = (line, col)
  where 
    line           = 1 + srcLine - remLine
    srcLine        = length srcLines 
    remLine        = length remLines
    col            = srcCol - remCol  
    srcCol         = length $ srcLines !! (line - 1) 
    remCol         = length $ remLines !! 0 
    srcLines       = lines  $ src
    remLines       = lines  $ rem



----------------------------------------------------------------------------------
-- Lexer Tokens ------------------------------------------------------------------
----------------------------------------------------------------------------------

dot           = Token.dot           lexer
angles        = Token.angles        lexer
stringLiteral = Token.stringLiteral lexer

----------------------------------------------------------------------------------
-- BareTypes ---------------------------------------------------------------------
----------------------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType 

bareTypeP
  =  try bareAllP
 <|> bareAllS
 <|> bareAllExprP
 <|> bareExistsP
 <|> try bareFunP
 <|> bareAtomP (refBindP bindP)
 <|> try (angles (do t <- parens $ bareTypeP
                     p <- monoPredicateP
                     return $ t `strengthen` (U mempty p mempty)))

bareArgP vv
  =  bareAtomP (refDefP vv)
 <|> parens bareTypeP

bareAtomP ref
  =  ref refasHoleP bbaseP
 <|> holeP
 <|> try (dummyP (bbaseP <* spaces))

holeP       = reserved "_" >> spaces >> return (RHole $ uTop $ Reft ("VV", [hole]))
holeRefP    = reserved "_" >> spaces >> return (RHole . uTop)
refasHoleP  = refasP <|> (reserved "_" >> return [hole])

bbaseP :: Parser (Reft -> BareType)
bbaseP 
  =  holeRefP
 <|> liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM2 bAppTy lowerIdP (sepBy1 bareTyArgP blanks))
 <|> try (liftM3 bRVar lowerIdP stratumP monoPredicateP)
 <|> liftM4 bCon locUpperIdP stratumP predicatesP (sepBy bareTyArgP blanks)

stratumP :: Parser Strata
stratumP 
  = do reserved "^"
       bstratumP
 <|> return mempty

bstratumP
  = ((:[]) . SVar) <$> symbolP

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM4 bCon locUpperIdP stratumP predicatesP (return []))
 <|> liftM3 bRVar lowerIdP stratumP monoPredicateP 

maybeP p = liftM Just p <|> return Nothing

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
  = do b <- binderP <* colon
       t <- bareArgP b
       return (b,t)
  
bareAllS
  = do reserved "forall"
       ss <- (angles $ sepBy1 symbolP comma)
       dot
       t  <- bareTypeP
       return $ foldr RAllS t ss

bareAllP 
  = do reserved "forall"
       as <- many tyVarIdP
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ foldr RAllT (foldr RAllP t ps) as

tyVarIdP :: Parser Symbol
tyVarIdP = symbol <$> condIdP alphanums (isLower . head)
           where alphanums = ['a'..'z'] ++ ['0'..'9']

predVarDefsP 
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP
  = liftM3 bPVar predVarIdP dcolon predVarTypeP

predVarIdP 
  = symbol <$> tyVarIdP

bPVar p _ xts  = PV p τ dummySymbol τxs
  where (_, τ) = safeLast "bPVar last" xts
        τxs    = [ (τ, x, EVar x) | (x, τ) <- init xts ]

predVarTypeP :: Parser [(Symbol, BSort)]
predVarTypeP = bareTypeP >>= either parserFail return . mkPredVarType
      
mkPredVarType t
  | isOk      = Right $ zip xs ts
  | otherwise = Left err 
  where
    isOk      = isPropBareType tOut || isHPropBareType tOut
    tOut      = ty_res trep
    trep      = toRTypeRep t 
    xs        = ty_binds trep 
    ts        = toRSort <$> ty_args trep
    err       = "Predicate Variable with non-Prop output sort: " ++ showpp t

--   = do t <- bareTypeP
--        let trep = toRTypeRep t
--        if isPropBareType $ ty_res trep
--          then return $ zip (ty_binds trep) (toRSort <$> (ty_args trep)) 
--          else parserFail $ "Predicate Variable with non-Prop output sort: " ++ showpp t


xyP lP sepP rP
  = liftM3 (\x _ y -> (x, y)) lP (spaces >> sepP) rP

data ArrowSym = ArrowFun | ArrowPred

arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

positionNameP = dummyNamePos <$> getPosition

dummyNamePos pos = "dummy." ++ name ++ ['.'] ++ line ++ ['.'] ++ col
    where 
      name       = san <$> sourceName pos
      line       = show $ sourceLine pos  
      col        = show $ sourceColumn pos  
      san '/'    = '.'
      san c      = toLower c

bareFunP  
  = do b  <- try bindP <|> dummyBindP 
       t1 <- bareArgP b
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow b t1 a t2 

dummyBindP = tempSymbol "db" <$> freshIntP

bbindP     = lowerIdP <* dcolon 

bareArrow b t1 ArrowFun t2
  = rFun b t1 t2
bareArrow _ t1 ArrowPred t2
  = foldr (rFun dummySymbol) t2 (getClasses t1)


isPropBareType  = isPrimBareType propConName
isHPropBareType = isPrimBareType hpropConName
isPrimBareType n (RApp tc [] _ _) = val tc == n
isPrimBareType _ _                = False



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
   =  try (liftM2 RProp symsP (refP bbaseP))
  <|> liftM (RPropP [] . predUReft) monoPredicate1P
  <|> (braces $ liftM2 bRProp symsP' refasP)
   where 
    symsP'       = do ss    <- symsP
                      fs    <- mapM refreshSym (fst <$> ss)
                      return $ zip ss fs
    refreshSym s = liftM (intSymbol s) freshIntP

monoPredicateP 
   = try (angles monoPredicate1P) 
  <|> return mempty

monoPredicate1P
   =  try (reserved "True" >> return mempty)
  <|> try (liftM pdVar (parens predVarUseP))
  <|> liftM pdVar predVarUseP 

predVarUseP 
  = do (p, xs) <- funArgsP 
       return   $ PV p dummyTyId dummySymbol [ (dummyTyId, dummySymbol, x) | x <- xs ]

funArgsP  = try realP <|> empP
  where
    empP  = (,[]) <$> predVarIdP
    realP = do EApp lp xs <- funAppP
               return (val lp, xs) 

  

------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRProp []    _    = errorstar "Parse.bRProp empty list"
bRProp syms' expr = RProp ss $ bRVar dummyName mempty mempty r
  where (ss, (v, _)) = (init syms, last syms)
        syms = [(y, s) | ((_, s), y) <- syms']
        su   = mkSubst [(x, EVar y) | ((x, _), y) <- syms'] 
        r    = su `subst` Reft(v, expr)

bRVar α s p r             = RVar α (U r p s)
bLst (Just t) rs r        = RApp (dummyLoc listConName) [t] rs (reftUReft r)
bLst (Nothing) rs r       = RApp (dummyLoc listConName) []  rs (reftUReft r)

bTup [t] _ r | isTauto r  = t
             | otherwise  = t `strengthen` (reftUReft r) 
bTup ts rs r              = RApp (dummyLoc tupConName) ts rs (reftUReft r)


-- Temporarily restore this hack benchmarks/esop2013-submission/Array.hs fails
-- w/o it
-- TODO RApp Int [] [p] true should be syntactically different than RApp Int [] [] p
bCon b s [RPropP _ r1] [] r = RApp b [] [] (r1 `meet` (U r mempty s)) 
bCon b s rs ts r            = RApp b ts rs (U r mempty s)

-- bAppTy v t r             = RAppTy (RVar v top) t (reftUReft r)
bAppTy v ts r             = (foldl' (\a b -> RAppTy a b mempty) (RVar v mempty) ts) `strengthen` (reftUReft r)


reftUReft      = \r -> U r mempty mempty
predUReft      = \p -> U dummyReft p mempty
dummyReft      = mempty
dummyTyId      = ""
dummyRSort     = ROth "dummy"

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty ctor
  = Meas    (Measure ty ctor)
  | Assm    (LocSymbol, ty)
  | Asrt    (LocSymbol, ty)
  | LAsrt   (LocSymbol, ty)
  | Asrts   ([LocSymbol], (ty, Maybe [Expr]))
  | Impt    Symbol
  | DDecl   DataDecl
  | Incl    FilePath
  | Invt    (Located ty)
  | IAlias  (Located ty, Located ty)
  | Alias   (RTAlias Symbol BareType)
  | PAlias  (RTAlias Symbol Pred)
  | Embed   (LocSymbol, FTycon)
  | Qualif  Qualifier
  | Decr    (LocSymbol, [Int])
  | LVars   LocSymbol
  | Lazy    LocSymbol
  | Pragma  (Located String)
  | CMeas   (Measure ty ())
  | IMeas   (Measure ty ctor)
  | Class   (RClass ty)

-- | For debugging
instance Show (Pspec a b) where
  show (Meas   _) = "Meas"   
  show (Assm   _) = "Assm"   
  show (Asrt   _) = "Asrt"   
  show (LAsrt  _) = "LAsrt"  
  show (Asrts  _) = "Asrts"  
  show (Impt   _) = "Impt"   
  show (DDecl  _) = "DDecl"  
  show (Incl   _) = "Incl"   
  show (Invt   _) = "Invt"   
  show (IAlias _) = "IAlias" 
  show (Alias  _) = "Alias"  
  show (PAlias _) = "PAlias" 
  show (Embed  _) = "Embed"  
  show (Qualif _) = "Qualif" 
  show (Decr   _) = "Decr"   
  show (LVars  _) = "LVars"  
  show (Lazy   _) = "Lazy"   
  show (Pragma _) = "Pragma" 
  show (CMeas  _) = "CMeas"  
  show (IMeas  _) = "IMeas"  
  show (Class  _) = "Class" 



-- mkSpec                 ::  String -> [Pspec ty LocSymbol] -> Measure.Spec ty LocSymbol
mkSpec name xs         = (name,)
                       $ Measure.qualifySpec (symbol name)
                       $ Measure.Spec
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.asmSigs    = [a | Assm   a <- xs]
  , Measure.sigs       = [a | Asrt   a <- xs]
                      ++ [(y, t) | Asrts (ys, (t, _)) <- xs, y <- ys]
  , Measure.localSigs  = []
  , Measure.invariants = [t | Invt   t <- xs]
  , Measure.ialiases   = [t | IAlias t <- xs]
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.paliases   = [p | PAlias p <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.decr       = [d | Decr d   <- xs]
  , Measure.lvars      = [d | LVars d  <- xs]
  , Measure.lazy       = S.fromList [s | Lazy s <- xs]
  , Measure.pragmas    = [s | Pragma s <- xs]
  , Measure.cmeasures  = [m | CMeas  m <- xs]
  , Measure.imeasures  = [m | IMeas  m <- xs]
  , Measure.classes    = [c | Class  c <- xs]
  , Measure.termexprs  = [(y, es) | Asrts (ys, (_, Just es)) <- xs, y <- ys]
  }

specP :: Parser (Pspec BareType LocSymbol)
specP 
  = try (reserved "assume"    >> liftM Assm   tyBindP   )
    <|> (reserved "assert"    >> liftM Asrt   tyBindP   )
    <|> (reserved "Local"     >> liftM LAsrt  tyBindP   )
    <|> (reserved "measure"   >> liftM Meas   measureP  ) 
    <|> try (reserved "class" >> reserved "measure" >> liftM CMeas cMeasureP)
    <|> (reserved "instance"  >> reserved "measure" >> liftM IMeas iMeasureP)
    <|> (reserved "class"     >> liftM Class  classP    )
    <|> (reserved "import"    >> liftM Impt   symbolP   )
    <|> (reserved "data"      >> liftM DDecl  dataDeclP )
    <|> (reserved "include"   >> liftM Incl   filePathP )
    <|> (reserved "invariant" >> liftM Invt   invariantP)
    <|> (reserved "using"     >> liftM IAlias invaliasP )
    <|> (reserved "type"      >> liftM Alias  aliasP    )
    <|> (reserved "predicate" >> liftM PAlias paliasP   )
    <|> (reserved "embed"     >> liftM Embed  embedP    )
    <|> (reserved "qualif"    >> liftM Qualif qualifierP)
    <|> (reserved "Decrease"  >> liftM Decr   decreaseP )
    <|> (reserved "LAZYVAR"   >> liftM LVars  lazyVarP  )
    <|> (reserved "Strict"    >> liftM Lazy   lazyVarP  )
    <|> (reserved "Lazy"      >> liftM Lazy   lazyVarP  )
    <|> (reserved "LIQUID"    >> liftM Pragma pragmaP   )
    <|> ({- DEFAULT -}           liftM Asrts  tyBindsP  )

pragmaP :: Parser (Located String)
pragmaP = locParserP stringLiteral

lazyP :: Parser Symbol
lazyP = binderP

lazyVarP :: Parser LocSymbol
lazyVarP = locParserP binderP

decreaseP :: Parser (LocSymbol, [Int])
decreaseP = mapSnd f <$> liftM2 (,) (locParserP binderP) (spaces >> (many integer))
  where f = ((\n -> fromInteger n - 1) <$>)

filePathP     :: Parser FilePath
filePathP     = angles $ many1 pathCharP
  where 
    pathCharP = choice $ char <$> pathChars 
    pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

tyBindsP    :: Parser ([LocSymbol], (BareType, Maybe [Expr]))
tyBindsP = xyP (sepBy (locParserP binderP) comma) dcolon termBareTypeP

tyBindP    :: Parser (LocSymbol, BareType)
tyBindP    = xyP (locParserP binderP) dcolon genBareTypeP

termBareTypeP :: Parser (BareType, Maybe [Expr])
termBareTypeP
   = try termTypeP
  <|> (, Nothing) <$> genBareTypeP 

termTypeP 
  = do t <- genBareTypeP
       reserved "/"
       es <- brackets $ sepBy exprP comma
       return (t, Just es)

invariantP   = locParserP genBareTypeP 

invaliasP   
  = do t  <- locParserP genBareTypeP 
       reserved "as"
       ta <- locParserP genBareTypeP
       return (t, ta)

genBareTypeP
  = bareTypeP

embedP 
  = xyP locUpperIdP (reserved "as") fTyConP


aliasP  = rtAliasP id     bareTypeP
paliasP = rtAliasP symbol predP

rtAliasP :: (Symbol -> tv) -> Parser ty -> Parser (RTAlias tv ty) 
rtAliasP f bodyP
  = do pos  <- getPosition
       name <- upperIdP
       spaces
       args <- sepBy aliasIdP spaces
       whiteSpace >> reservedOp "=" >> whiteSpace
       body <- bodyP 
       let (tArgs, vArgs) = partition (isLower . headSym) args
       return $ RTA name (f <$> tArgs) (f <$> vArgs) body pos

aliasIdP :: Parser Symbol
aliasIdP = condIdP (['A' .. 'Z'] ++ ['a'..'z'] ++ ['0'..'9']) (isAlpha . head) 

measureP :: Parser (Measure BareType LocSymbol)
measureP 
  = do (x, ty) <- tyBindP  
       whiteSpace
       eqns    <- grabs $ measureDefP $ (rawBodyP <|> tyBodyP ty)
       return   $ Measure.mkM x ty eqns 

cMeasureP :: Parser (Measure BareType ())
cMeasureP
  = do (x, ty) <- tyBindP
       return $ Measure.mkM x ty []

iMeasureP :: Parser (Measure BareType LocSymbol)
iMeasureP = measureP
  -- = do m   <- locParserP symbolP
  --      ty  <- genBareTypeP
  --      reserved "="
  --      tgt <- symbolP
  --      return $ M m ty tgt

classP :: Parser (RClass BareType)
classP
  = do sups <- superP
       c <- locUpperIdP
       spaces
       tvs <- manyTill tyVarIdP (try $ reserved "where")
       ms <- grabs tyBindP
       spaces
       return $ RClass (fmap symbol c) (mb sups) tvs ms
  where
    mb Nothing   = []
    mb (Just xs) = xs
    superP = maybeP (parens ( liftM (toRCls <$>)  (bareTypeP `sepBy1` comma)) <* reserved "=>")
    toRCls (RApp c ts rs r) = RCls c ts
    toRCls t@(RCls _ _)     = t
    toRCls t                = errorstar $ "Parse.toRCls called with" ++ show t

rawBodyP 
  = braces $ do
      v <- symbolP 
      reserved "|"
      p <- predP <* spaces
      return $ R v p

tyBodyP :: BareType -> Parser Body
tyBodyP ty 
  = case outTy ty of
      Just bt | isPropBareType bt
                -> P <$> predP
      _         -> E <$> exprP
    where outTy (RAllT _ t)    = outTy t
          outTy (RAllP _ t)    = outTy t
          outTy (RFun _ _ t _) = Just t
          outTy _              = Nothing

binderP :: Parser Symbol
binderP    =  try $ symbol <$> idP badc
          <|> pwr <$> parens (idP bad)
  where 
    idP p  = many1 (satisfy (not . p))
    badc c = (c == ':') || (c == ',') || bad c
    bad c  = isSpace c || c `elem` "(,)"
    pwr s  = symbol $ "(" `mappend` s `mappend` ")"
             
grabs p = try (liftM2 (:) p (grabs p)) 
       <|> return []

measureDefP :: Parser Body -> Parser (Def LocSymbol)
measureDefP bodyP
  = do mname   <- locParserP symbolP
       (c, xs) <- {- ORIGINAL parens $ -} measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP 
       whiteSpace
       let xs'  = (symbol . val) <$> xs
       return   $ Def mname (symbol <$> c) xs' body

-- ORIGINAL
-- measurePatP :: Parser (String, [LocString])
-- measurePatP
--   =  try (liftM2 (,)   upperIdP (sepBy locLowerIdP whiteSpace))
--  <|> try (liftM3 (\x c y -> (c, [x,y])) locLowerIdP colon locLowerIdP)
--  <|> (brackets whiteSpace  >> return ("[]",[])) 

measurePatP :: Parser (LocSymbol, [LocSymbol])
measurePatP 
  =  try tupPatP 
 <|> try (parens conPatP)
 <|> try (parens consPatP)
 <|>     (parens nilPatP)

tupPatP  = mkTupPat  <$> (parens       $  sepBy locLowerIdP comma)
conPatP  = (,)       <$> locParserP dataConNameP <*> sepBy locLowerIdP whiteSpace
consPatP = mkConsPat <$> locLowerIdP  <*> colon <*> locLowerIdP
nilPatP  = mkNilPat  <$> brackets whiteSpace 

mkTupPat zs     = (tupDataCon (length zs), zs)
mkNilPat _      = (dummyLoc "[]", []    )
mkConsPat x c y = (dummyLoc ":" , [x, y])
tupDataCon n    = dummyLoc $ symbol $ "(" <> replicate (n - 1) ',' <> ")"


-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP 
  =   (braces $ sepBy predTypeDDP comma)
  <|> (sepBy (parens predTypeDDP) spaces)

predTypeDDP 
  = liftM2 (,) bbindP bareTypeP

dataConP
  = do x   <- locParserP dataConNameP
       spaces
       xts <- dataConFieldsP
       return (x, xts)

-- dataConNameP = symbolString <$> binderP -- upperIdP
dataConNameP 
  =  try upperIdP
 <|> pwr <$> parens (idP bad)
  where 
     idP p  = symbol <$> many1 (satisfy (not . p))
     bad c  = isSpace c || c `elem` "(,)"
     pwr s  = "(" <> s <> ")"

dataSizeP 
  = (brackets $ (Just . mkFun) <$> locLowerIdP)
  <|> return Nothing
  where mkFun s = \x -> EApp (symbol <$> s) [EVar x]

dataDeclP :: Parser DataDecl 
dataDeclP 
   =  try dataDeclFullP
  <|> dataDeclSizeP

dataDeclSizeP
  = do pos <- getPosition
       x   <- locUpperIdP
       spaces
       fsize <- dataSizeP
       return $ D x [] [] [] [] pos fsize

dataDeclFullP
  = do pos <- getPosition
       x   <- locUpperIdP
       spaces
       fsize <- dataSizeP
       spaces
       ts  <- sepBy tyVarIdP spaces
       ps  <- predVarDefsP
       whiteSpace >> reservedOp "=" >> whiteSpace
       dcs <- sepBy dataConP (reserved "|")
       whiteSpace
       return $ D x ts ps [] dcs pos fsize


---------------------------------------------------------------------
------------ Interacting with Fixpoint ------------------------------
---------------------------------------------------------------------

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

instance Inputable (Measure BareType LocSymbol) where
  rr' = doParse' measureP


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

me1, me2 :: Measure BareType Symbol 
me1 = (rr $ intercalate "\n" m1) 
me2 = (rr $ intercalate "\n" m2)
-}
