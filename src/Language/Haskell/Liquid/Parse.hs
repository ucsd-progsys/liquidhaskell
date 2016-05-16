{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}

module Language.Haskell.Liquid.Parse
  ( hsSpecificationP, specSpecificationP
  , parseSymbolToLogic
  )
  where

import           Control.Arrow                          (second)
import           Control.Monad
import           Data.String
import           Prelude                                hiding (error)
import           Text.Parsec
import           Text.Parsec.Error                      (newErrorMessage, Message (..))
import           Text.Parsec.Pos                        (newPos)

import qualified Text.Parsec.Token                      as Token
import qualified Data.Text                              as T
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import           Data.Monoid
import           Data.Char                              (isSpace, isAlpha, isUpper, isAlphaNum)
import           Data.List                              (foldl', partition)
import           Data.Either                            

import           GHC                                    (ModuleName, mkModuleName)
import           Text.PrettyPrint.HughesPJ              (text)

import           Language.Fixpoint.Types                hiding (Error, R, Predicate)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types          hiding (Axiom)
import           Language.Haskell.Liquid.Misc           (mapSnd)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure        as Measure
import           Language.Fixpoint.Parse                hiding (angles, refBindP, refP, refDefP)

-- import Debug.Trace

--------------------------------------------------------------------------------
-- | Top Level Parsing API -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Used to parse .hs and .lhs files (via ApiAnnotations)

-------------------------------------------------------------------------------
hsSpecificationP :: ModuleName
                 -> [(SourcePos, String)]
                 -> Either [Error] (ModName, Measure.BareSpec)
-------------------------------------------------------------------------------

hsSpecificationP modName specComments =
  case partitionEithers $ parseComment <$> specComments of
    ([], specs) -> Right $ mkSpec (ModName SrcImport modName) specs
    (errs, _)   -> Left errs
  where
    parseComment (pos, specComment) =
      parseWithError specP pos specComment

-- | Used to parse .spec files

--------------------------------------------------------------------------
specSpecificationP  :: SourceName -> String -> Either Error (ModName, Measure.BareSpec)
--------------------------------------------------------------------------
specSpecificationP f s = parseWithError specificationP (newPos f 1 1) s

specificationP :: Parser (ModName, Measure.BareSpec)
specificationP
  = do reserved "module"
       reserved "spec"
       name   <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace)
       return $ mkSpec (ModName SpecImport $ mkModuleName $ symbolString name) xs

---------------------------------------------------------------------------
parseWithError :: Parser a -> SourcePos -> String -> Either Error a
---------------------------------------------------------------------------
parseWithError parser p s =
  case runParser doParse 0 (sourceName p) s of
    Left e            -> Left  $ parseErrorError e
    Right (r, "", _)  -> Right r
    Right (_, rem, _) -> Left  $ parseErrorError $ remParseError p s rem
  where
    doParse =
      setPosition p >> remainderP (whiteSpace *> parser <* whiteSpace)


---------------------------------------------------------------------------
parseErrorError     :: ParseError -> Error
---------------------------------------------------------------------------
parseErrorError e = ErrParse sp msg e
  where
    pos             = errorPos e
    sp              = sourcePosSrcSpan pos
    msg             = text $ "Error Parsing Specification from: " ++ sourceName pos

---------------------------------------------------------------------------
remParseError       :: SourcePos -> String -> String -> ParseError
---------------------------------------------------------------------------
remParseError p s r = newErrorMessage msg $ newPos (sourceName p) line col
  where
    msg             = Message "Leftover while parsing"
    (line, col)     = remLineCol p s r

remLineCol             :: SourcePos -> String -> String -> (Int, Int)
remLineCol pos src rem = (line + offLine, col + offCol)
  where
    line               = 1 + srcLine - remLine
    srcLine            = length srcLines
    remLine            = length remLines
    offLine            = sourceLine pos - 1
    col                = 1 + srcCol - remCol
    srcCol             = length $ srcLines !! (line - 1)
    remCol             = length $ head remLines
    offCol             = if line == 1 then sourceColumn pos - 1 else 0
    srcLines           = lines  src
    remLines           = lines  rem



----------------------------------------------------------------------------------
-- Parse to Logic  ---------------------------------------------------------------
----------------------------------------------------------------------------------

parseSymbolToLogic :: SourceName -> String -> Either Error LogicMap
parseSymbolToLogic f = parseWithError toLogicP (newPos f 1 1)

toLogicP :: Parsec String Integer LogicMap
toLogicP
  = toLogicMap <$> many toLogicOneP

toLogicOneP :: Parsec String Integer (Symbol, [Symbol], Expr)
toLogicOneP
  = do reserved "define"
       (x:xs) <- many1 symbolP
       reserved "="
       e      <- exprP
       return (x, xs, e)


----------------------------------------------------------------------------------
-- Lexer Tokens ------------------------------------------------------------------
----------------------------------------------------------------------------------

dot :: Parsec String u String
dot           = Token.dot           lexer

angles :: Parsec String u a
       -> Parsec String u a
angles        = Token.angles        lexer

stringLiteral :: Parsec String u String
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
--  <|> bareAllExprP
--  <|> bareExistsP
 <|> try bareConstraintP
 <|> try bareFunP
 <|> bareAtomP (refBindP bindP)
 <|> try (angles (do t <- parens bareTypeP
                     p <- monoPredicateP
                     return $ t `strengthen` MkUReft mempty p mempty))

bareArgP :: Symbol
         -> Parser (RType LocSymbol Symbol (UReft Reft))
bareArgP vv
  =  bareAtomP (refDefP vv)
 <|> parens bareTypeP

bareAtomP :: (Parser Expr -> Parser (Reft -> BareType) -> Parser (RType LocSymbol Symbol (UReft Reft)))
          -> Parser (RType LocSymbol Symbol (UReft Reft))
bareAtomP ref
  =  ref refasHoleP bbaseP
 <|> holeP
 <|> try (dummyP (bbaseP <* spaces))


refBindP :: Parser Symbol 
         -> Parser Expr 
         -> Parser (Reft -> (RType LocSymbol Symbol (UReft Reft))) 
         -> Parser (RType LocSymbol Symbol (UReft Reft))
refBindP bp rp kindP
  = braces $ 
   try (do x  <- bp
           i  <- freshIntP
           t  <- kindP
           reserved "|"
           ra <- rp <* spaces
           let xi = intSymbol x i
           let su v = if v == x then xi else v
           return $ substa su $ t (Reft (x, ra)) )
  <|> (RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces)

refP :: Parser (Reft -> (RType LocSymbol Symbol (UReft Reft))) -> Parser (RType LocSymbol Symbol (UReft Reft))
refP       = refBindP bindP refaP

refDefP :: Symbol -> Parser Expr -> Parser (Reft -> (RType LocSymbol Symbol (UReft Reft))) -> Parser (RType LocSymbol Symbol (UReft Reft))
refDefP x  = refBindP (optBindP x)

optBindP :: Symbol
         -> Parser Symbol
optBindP x = try bindP <|> return x

holeP :: Parser (RType c tv (UReft Reft))
holeP       = reserved "_" >> spaces >> return (RHole $ uTop $ Reft ("VV", hole))

holeRefP :: Parser (r -> RType c tv (UReft r))
holeRefP    = reserved "_" >> spaces >> return (RHole . uTop)

refasHoleP :: Parser Expr
refasHoleP  = try refaP
           <|> (reserved "_" >> return hole)

-- FIXME: the use of `blanks = oneOf " \t"` here is a terrible and fragile hack
-- to avoid parsing:
--
--   foo :: a -> b
--   bar :: a
--
-- as `foo :: a -> b bar`..
bbaseP :: Parser (Reft -> BareType)
bbaseP
  =  holeRefP
 <|> liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM2 bAppTy lowerIdP (sepBy1 bareTyArgP blanks))
 <|> try (liftM3 bRVar lowerIdP stratumP monoPredicateP)
 <|> liftM5 bCon locUpperIdP stratumP predicatesP (sepBy bareTyArgP blanks) mmonoPredicateP

stratumP :: Parser Strata
stratumP
  = do reserved "^"
       bstratumP
 <|> return mempty

bstratumP :: Parser [Stratum]
bstratumP
  = ((:[]) . SVar) <$> symbolP

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  holeRefP
 <|> liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM5 bCon locUpperIdP stratumP predicatesP (return []) (return mempty))
 <|> liftM3 bRVar lowerIdP stratumP monoPredicateP

maybeP :: ParsecT s u m a -> ParsecT s u m (Maybe a)
maybeP p = liftM Just p <|> return Nothing

bareTyArgP :: Parser (RType LocSymbol Symbol RReft)
bareTyArgP
  =  -- try (RExprArg . expr <$> binderP) <|>
     try (RExprArg . fmap expr <$> locParserP integer)
 <|> try (braces $ RExprArg <$> locParserP exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)

bareAtomNoAppP :: Parser BareType
bareAtomNoAppP
  =  refP bbaseNoAppP
 <|> try (dummyP (bbaseNoAppP <* spaces))

bareConstraintP :: Parser (RType LocSymbol Symbol RReft)
bareConstraintP
  = do ct   <- braces constraintP
       t    <- bareTypeP
       return $ rrTy ct t

constraintP :: Parser (RType LocSymbol Symbol RReft)
constraintP
  = do xts <- constraintEnvP
       t1  <- bareTypeP
       reserved "<:"
       t2  <- bareTypeP
       return $ fromRTypeRep $ RTypeRep [] [] [] ((val . fst <$> xts) ++ [dummySymbol])
                                                 (replicate (length xts + 1) mempty)
                                                 ((snd <$> xts) ++ [t1]) t2

constraintEnvP :: Parser [(LocSymbol, BareType)]
constraintEnvP
   =  try (do xts <- sepBy tyBindNoLocP comma
              reserved "|-"
              return xts)
  <|> return []

rrTy :: Monoid r => RType c tv r -> RType c tv r -> RType c tv r
rrTy ct = RRTy (xts ++ [(dummySymbol, tr)]) mempty OCons
  where
    tr   = ty_res trep
    xts  = zip (ty_binds trep) (ty_args trep)
    trep = toRTypeRep ct

bareAllS :: Parser (RType LocSymbol Symbol RReft)
bareAllS
  = do reserved "forall"
       ss <- angles $ sepBy1 symbolP comma
       dot
       t  <- bareTypeP
       return $ foldr RAllS t ss

bareAllP :: Parser (RType LocSymbol Symbol RReft)
bareAllP
  = do reserved "forall"
       as <- many tyVarIdP
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ foldr RAllT (foldr RAllP t ps) as

tyVarIdP :: Parser Symbol
tyVarIdP = symbol <$> condIdP alphanums (isSmall . head)
           where
             alphanums = S.fromList $ ['a'..'z'] ++ ['0'..'9']

predVarDefsP :: Parser [PVar BSort]
predVarDefsP
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP :: Parser (PVar BSort)
predVarDefP
  = bPVar <$> predVarIdP <*> dcolon <*> predVarTypeP

predVarIdP :: Parser Symbol
predVarIdP
  = symbol <$> tyVarIdP

bPVar :: Symbol -> t -> [(Symbol, t1)] -> PVar t1
bPVar p _ xts  = PV p (PVProp τ) dummySymbol τxs
  where
    (_, τ) = safeLast "bPVar last" xts
    τxs    = [ (τ, x, EVar x) | (x, τ) <- init xts ]
    safeLast _ xs@(_:_) = last xs
    safeLast msg _      = panic Nothing $ "safeLast with empty list " ++ msg

predVarTypeP :: Parser [(Symbol, BSort)]
predVarTypeP = bareTypeP >>= either parserFail return . mkPredVarType

mkPredVarType :: BareType -> Either String [(Symbol, BSort)]
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

xyP :: Parser x -> Parser a -> Parser y -> Parser (x, y)
xyP lP sepP rP = (\x _ y -> (x, y)) <$> lP <*> (spaces >> sepP) <*> rP

data ArrowSym = ArrowFun | ArrowPred

arrowP :: Parser ArrowSym
arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

bareFunP :: Parser (RType LocSymbol Symbol (UReft Reft))
bareFunP
  = do b  <- try funBindP <|> dummyBindP
       t1 <- bareArgP b
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow b t1 a t2

funBindP :: Parser Symbol
funBindP = lowerIdP <* colon

dummyBindP :: Parser Symbol
dummyBindP = tempSymbol "db" <$> freshIntP

bbindP :: Parser Symbol
bbindP     = lowerIdP <* dcolon

bareArrow :: (Monoid r, TyConable c)
          => Symbol -> RType c tv r -> ArrowSym -> RType c tv r
          -> RType c tv r
bareArrow b t1 ArrowFun t2
  = rFun b t1 t2
bareArrow _ t1 ArrowPred t2
  = foldr (rFun dummySymbol) t2 (getClasses t1)


isPropBareType :: RType (Located Symbol) t t1 -> Bool
isPropBareType  = isPrimBareType propConName

isHPropBareType :: RType (Located Symbol) t t1 -> Bool
isHPropBareType = isPrimBareType hpropConName

isPrimBareType :: Eq a => a -> RType (Located a) t t1 -> Bool
isPrimBareType n (RApp tc [] _ _) = val tc == n
isPrimBareType _ _                = False

getClasses :: TyConable c => RType c t t1 -> [RType c t t1]
getClasses t@(RApp tc ts _ _)
  | isTuple tc
  = ts
  | otherwise
  = [t]
getClasses t
  = [t]

dummyP ::  Monad m => m (Reft -> b) -> m b
dummyP fm
  = fm `ap` return dummyReft

symsP :: (IsString tv, Monoid r)
      => Parser [(Symbol, RType c tv r)]
symsP
  = do reserved "\\"
       ss <- sepBy symbolP spaces
       reserved "->"
       return $ (, dummyRSort) <$> ss
 <|> return []

dummyRSort :: (IsString tv, Monoid r) => RType c tv r
dummyRSort
  = RVar "dummy" mempty

predicatesP :: (IsString tv, Monoid r)
            => Parser [Ref (RType c tv r) BareType]
predicatesP
   =  try (angles $ sepBy1 predicate1P comma)
  <|> return []

predicate1P :: (IsString tv, Monoid r)
            => Parser (Ref (RType c tv r) BareType)
predicate1P
   =  try (RProp <$> symsP <*> refP bbaseP)
  <|> (rPropP [] . predUReft <$> monoPredicate1P)
  <|> (braces $ bRProp <$> symsP' <*> refaP)
   where
    symsP'       = do ss    <- symsP
                      fs    <- mapM refreshSym (fst <$> ss)
                      return $ zip ss fs
    refreshSym s = intSymbol s <$> freshIntP

mmonoPredicateP :: Parser Predicate
mmonoPredicateP
   = try (angles $ angles monoPredicate1P)
  <|> return mempty

monoPredicateP :: Parser Predicate
monoPredicateP
   = try (angles monoPredicate1P)
  <|> return mempty

monoPredicate1P :: Parser Predicate
monoPredicate1P
   =  try (reserved "True" >> return mempty)
  <|> try (pdVar <$> parens predVarUseP)
  <|> (pdVar <$> predVarUseP)

predVarUseP :: IsString t
            => Parser (PVar t)
predVarUseP
  = do (p, xs) <- funArgsP
       return   $ PV p (PVProp dummyTyId) dummySymbol [ (dummyTyId, dummySymbol, x) | x <- xs ]

funArgsP :: Parser (Symbol, [Expr])
funArgsP  = try realP <|> empP
  where
    empP  = (,[]) <$> predVarIdP
    realP = do (EVar lp, xs) <- splitEApp <$> funAppP
               return (lp, xs)

boundP :: Parser (Bound (Located BareType) Expr)
boundP = do
  name   <- locParserP upperIdP
  reservedOp "="
  vs     <- bvsP
  params <- many (parens tyBindP)
  args   <- bargsP
  body   <- predP
  return $ Bound name vs params args body
 where
    bargsP = try ( do reservedOp "\\"
                      xs <- many (parens tyBindP)
                      reservedOp  "->"
                      return xs
                 )
           <|> return []
    bvsP   = try ( do reserved "forall"
                      xs <- many (locParserP symbolP)
                      reserved  "."
                      return (fmap (`RVar` mempty) <$> xs)
                 )
           <|> return []

------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRProp :: [((Symbol, τ), Symbol)]
       -> Expr -> Ref τ (RType c Symbol (UReft Reft))
bRProp []    _    = panic Nothing "Parse.bRProp empty list"
bRProp syms' expr = RProp ss $ bRVar dummyName mempty mempty r
  where
    (ss, (v, _))  = (init syms, last syms)
    syms          = [(y, s) | ((_, s), y) <- syms']
    su            = mkSubst [(x, EVar y) | ((x, _), y) <- syms']
    r             = su `subst` Reft (v, expr)

bRVar :: tv -> Strata -> Predicate -> r -> RType c tv (UReft r)
bRVar α s p r             = RVar α (MkUReft r p s)

bLst :: Maybe (RType (Located Symbol) tv (UReft r))
     -> [RTProp (Located Symbol) tv (UReft r)]
     -> r
     -> RType (Located Symbol) tv (UReft r)
bLst (Just t) rs r        = RApp (dummyLoc listConName) [t] rs (reftUReft r)
bLst (Nothing) rs r       = RApp (dummyLoc listConName) []  rs (reftUReft r)

bTup :: (PPrint r, Reftable r)
     => [RType (Located Symbol) tv (UReft r)]
     -> [RTProp (Located Symbol) tv (UReft r)]
     -> r
     -> RType (Located Symbol) tv (UReft r)
bTup [t] _ r | isTauto r  = t
             | otherwise  = t `strengthen` (reftUReft r)
bTup ts rs r              = RApp (dummyLoc tupConName) ts rs (reftUReft r)


-- Temporarily restore this hack benchmarks/esop2013-submission/Array.hs fails
-- w/o it
-- TODO RApp Int [] [p] true should be syntactically different than RApp Int [] [] p
-- bCon b s [RProp _ (RHole r1)] [] _ r = RApp b [] [] $ r1 `meet` (MkUReft r mempty s)
bCon :: c
     -> Strata
     -> [RTProp c tv (UReft r)]
     -> [RType c tv (UReft r)]
     -> Predicate
     -> r
     -> RType c tv (UReft r)
bCon b s rs            ts p r = RApp b ts rs $ MkUReft r p s

bAppTy :: (Foldable t, PPrint r, Reftable r)
       => tv -> t (RType c tv (UReft r)) -> r -> RType c tv (UReft r)
bAppTy v ts r  = ts' `strengthen` reftUReft r
  where
    ts'        = foldl' (\a b -> RAppTy a b mempty) (RVar v mempty) ts

reftUReft :: r -> UReft r
reftUReft r    = MkUReft r mempty mempty

predUReft :: Monoid r => Predicate -> UReft r
predUReft p    = MkUReft dummyReft p mempty

dummyReft :: Monoid a => a
dummyReft      = mempty

dummyTyId :: IsString a => a
dummyTyId      = ""

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty ctor
  = Meas    (Measure ty ctor)
  | Assm    (LocSymbol, ty)
  | Asrt    (LocSymbol, ty)
  | LAsrt   (LocSymbol, ty)
  | Asrts   ([LocSymbol], (ty, Maybe [Located Expr]))
  | Impt    Symbol
  | DDecl   DataDecl
  | Incl    FilePath
  | Invt    ty
  | IAlias  (ty, ty)
  | Alias   (RTAlias Symbol BareType)
  | EAlias  (RTAlias Symbol Expr)
  | Embed   (LocSymbol, FTycon)
  | Qualif  Qualifier
  | Decr    (LocSymbol, [Int])
  | LVars   LocSymbol
  | Lazy    LocSymbol
  | HMeas   LocSymbol
  | Axiom   LocSymbol
  | Inline  LocSymbol
  | ASize   LocSymbol
  | HBound  LocSymbol
  | PBound  (Bound ty Expr)
  | Pragma  (Located String)
  | CMeas   (Measure ty ())
  | IMeas   (Measure ty ctor)
  | Class   (RClass ty)
  | RInst   (RInstance ty)
  | Varia   (LocSymbol, [Variance])

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
  show (EAlias _) = "EAlias"
  show (Embed  _) = "Embed"
  show (Qualif _) = "Qualif"
  show (Decr   _) = "Decr"
  show (LVars  _) = "LVars"
  show (Lazy   _) = "Lazy"
  show (Axiom  _) = "Axiom"
  show (HMeas  _) = "HMeas"
  show (HBound _) = "HBound"
  show (Inline _) = "Inline"
  show (Pragma _) = "Pragma"
  show (CMeas  _) = "CMeas"
  show (IMeas  _) = "IMeas"
  show (Class  _) = "Class"
  show (Varia  _) = "Varia"
  show (PBound _) = "Bound"
  show (RInst  _) = "RInst"
  show (ASize  _) = "ASize"

mkSpec :: ModName -> [Pspec (Located BareType) LocSymbol] -> (ModName, Measure.Spec (Located BareType) LocSymbol)
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
  , Measure.ealiases   = [e | EAlias e <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.decr       = [d | Decr d   <- xs]
  , Measure.lvars      = [d | LVars d  <- xs]
  , Measure.lazy       = S.fromList [s | Lazy   s <- xs]
  , Measure.axioms     = S.fromList [s | Axiom  s <- xs]
  , Measure.hmeas      = S.fromList [s | HMeas  s <- xs]
  , Measure.inlines    = S.fromList [s | Inline s <- xs]
  , Measure.autosize   = S.fromList [s | ASize  s <- xs]
  , Measure.hbounds    = S.fromList [s | HBound s <- xs]
  , Measure.pragmas    = [s | Pragma s <- xs]
  , Measure.cmeasures  = [m | CMeas  m <- xs]
  , Measure.imeasures  = [m | IMeas  m <- xs]
  , Measure.classes    = [c | Class  c <- xs]
  , Measure.dvariance  = [v | Varia  v <- xs]
  , Measure.rinstance  = [i | RInst  i <- xs]
  , Measure.bounds     = M.fromList [(bname i, i) | PBound i <- xs]
  , Measure.termexprs  = [(y, es) | Asrts (ys, (_, Just es)) <- xs, y <- ys]
  }

specP :: Parser (Pspec (Located BareType) LocSymbol)
specP
  = try (reservedToken "assume"       >> liftM Assm   tyBindP   )
    <|> (reservedToken "assert"       >> liftM Asrt   tyBindP   )
    <|> (reservedToken "autosize"     >> liftM ASize  asizeP    )
    <|> (reservedToken "Local"        >> liftM LAsrt  tyBindP   )
    <|> (reservedToken "axiomatize"   >> liftM Axiom  axiomP    )
    <|> try (reservedToken "measure"  >> liftM Meas   measureP  )
    <|> (reservedToken "measure"      >> liftM HMeas  hmeasureP )
    <|> (reservedToken "inline"       >> liftM Inline  inlineP  )
    <|> try (reservedToken "bound"    >> liftM PBound  boundP   )
    <|> (reservedToken "bound"        >> liftM HBound  hboundP  )
    <|> try (reservedToken "class"    >> reserved "measure" >> liftM CMeas cMeasureP)
    <|> try (reservedToken "instance" >> reserved "measure" >> liftM IMeas iMeasureP)
    <|> (reservedToken "instance"  >> liftM RInst  instanceP )
    <|> (reservedToken "class"     >> liftM Class  classP    )
    <|> (reservedToken "import"    >> liftM Impt   symbolP   )
    <|> try (reservedToken "data" >> reserved "variance " >> liftM Varia datavarianceP)
    <|> (reservedToken "data"      >> liftM DDecl  dataDeclP )
    <|> (reservedToken "include"   >> liftM Incl   filePathP )
    <|> (reservedToken "invariant" >> liftM Invt   invariantP)
    <|> (reservedToken "using"     >> liftM IAlias invaliasP )
    <|> (reservedToken "type"      >> liftM Alias  aliasP    )
    <|> (reservedToken "predicate" >> liftM EAlias ealiasP   )
    <|> (reservedToken "expression">> liftM EAlias ealiasP   )
    <|> (reservedToken "embed"     >> liftM Embed  embedP    )
    <|> (reservedToken "qualif"    >> liftM Qualif (qualifierP sortP))
    <|> (reservedToken "Decrease"  >> liftM Decr   decreaseP )
    <|> (reservedToken "LAZYVAR"   >> liftM LVars  lazyVarP  )
    <|> (reservedToken "Strict"    >> liftM Lazy   lazyVarP  )
    <|> (reservedToken "Lazy"      >> liftM Lazy   lazyVarP  )
    <|> (reservedToken "LIQUID"    >> liftM Pragma pragmaP   )
    <|> ({- DEFAULT -}                liftM Asrts  tyBindsP  )

reservedToken :: Stream s m Char => String -> ParsecT s u m ()
reservedToken str = try(string str >> spaces1)

spaces1 :: Stream s m Char => ParsecT s u m ()
spaces1 = satisfy isSpace >> spaces


pragmaP :: Parser (Located String)
pragmaP = locParserP stringLiteral

lazyVarP :: Parser LocSymbol
lazyVarP = locParserP binderP

hmeasureP :: Parser LocSymbol
hmeasureP = locParserP binderP

axiomP :: Parser LocSymbol
axiomP = locParserP binderP

hboundP :: Parser LocSymbol
hboundP = locParserP binderP

inlineP :: Parser LocSymbol
inlineP = locParserP binderP

asizeP :: Parser LocSymbol
asizeP = locParserP binderP

decreaseP :: Parser (LocSymbol, [Int])
decreaseP = mapSnd f <$> liftM2 (,) (locParserP binderP) (spaces >> many integer)
  where
    f     = ((\n -> fromInteger n - 1) <$>)

filePathP     :: Parser FilePath
filePathP     = angles $ many1 pathCharP
  where
    pathCharP = choice $ char <$> pathChars
    pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

datavarianceP :: Parser (Located Symbol, [Variance])
datavarianceP = liftM2 (,) locUpperIdP (spaces >> many varianceP)

varianceP :: Parsec String u Variance
varianceP = (reserved "bivariant"     >> return Bivariant)
        <|> (reserved "invariant"     >> return Invariant)
        <|> (reserved "covariant"     >> return Covariant)
        <|> (reserved "contravariant" >> return Contravariant)
        <?> "Invalib variance annotation\t Use one of bivariant, invariant, covariant, contravariant"

tyBindsP :: Parser ([LocSymbol], (Located BareType, Maybe [Located Expr]))
tyBindsP = xyP (sepBy (locParserP binderP) comma) dcolon termBareTypeP

tyBindNoLocP :: Parser (LocSymbol, BareType)
tyBindNoLocP = second val <$> tyBindP

tyBindP    :: Parser (LocSymbol, Located BareType)
tyBindP    = xyP xP dcolon tP
  where
    xP     = locParserP binderP
    tP     = locParserP genBareTypeP

termBareTypeP :: Parser (Located BareType, Maybe [Located Expr])
termBareTypeP
   = try termTypeP
  <|> (, Nothing) <$> locParserP genBareTypeP

termTypeP :: Parser (Located BareType, Maybe [Located Expr])
termTypeP
  = do t <- locParserP genBareTypeP
       reserved "/"
       es <- brackets $ sepBy (locParserP exprP) comma
       return (t, Just es)

invariantP :: Parser (Located BareType)
invariantP = locParserP genBareTypeP

invaliasP :: Parser (Located BareType, Located BareType)
invaliasP
  = do t  <- locParserP genBareTypeP
       reserved "as"
       ta <- locParserP genBareTypeP
       return (t, ta)

genBareTypeP :: Parser BareType
genBareTypeP
  = bareTypeP

embedP :: Parser (Located Symbol, FTycon)
embedP
  = xyP locUpperIdP (reserved "as") fTyConP


aliasP :: Parser (RTAlias Symbol BareType)
aliasP  = rtAliasP id     bareTypeP

ealiasP :: Parser (RTAlias Symbol Expr)
ealiasP = try (rtAliasP symbol predP)
      <|> rtAliasP symbol exprP

rtAliasP :: (Symbol -> tv) -> Parser ty -> Parser (RTAlias tv ty)
rtAliasP f bodyP
  = do pos  <- getPosition
       name <- upperIdP
       spaces
       args <- sepBy aliasIdP blanks
       whiteSpace >> reservedOp "=" >> whiteSpace
       body <- bodyP
       posE <- getPosition
       let (tArgs, vArgs) = partition (isSmall . headSym) args
       return $ RTA name (f <$> tArgs) (f <$> vArgs) body pos posE

aliasIdP :: Parser Symbol
aliasIdP = condIdP alphaNums (isAlpha . head)
           where
             alphaNums = S.fromList $ ['A' .. 'Z'] ++ ['a'..'z'] ++ ['0'..'9']

measureP :: Parser (Measure (Located BareType) LocSymbol)
measureP
  = do (x, ty) <- tyBindP
       whiteSpace
       eqns    <- grabs $ measureDefP (rawBodyP <|> tyBodyP ty)
       return   $ Measure.mkM x ty eqns

cMeasureP :: Parser (Measure (Located BareType) ())
cMeasureP
  = do (x, ty) <- tyBindP
       return $ Measure.mkM x ty []

iMeasureP :: Parser (Measure (Located BareType) LocSymbol)
iMeasureP = measureP


oneClassArg :: Parser [Located BareType]
oneClassArg
  = sing <$> locParserP (rit <$> locUpperIdP <*> (map val <$> classParams))
  where
    rit t as    = RApp t ((`RVar` mempty) <$> as) [] mempty
    classParams =  (reserved "where" >> return [])
               <|> ((:) <$> locLowerIdP <*> classParams)
    sing x      = [x]

instanceP :: Parser (RInstance (Located BareType))
instanceP
  = do _    <- supersP
       c    <- locUpperIdP
       spaces
       tvs  <- (try oneClassArg) <|> (manyTill iargsP (try $ reserved "where"))
       ms   <- sepBy tyBindP semi
       spaces
       return $ RI c tvs ms 
  where
    superP   = locParserP (toRCls <$> bareAtomP (refBindP bindP))
    supersP  = try (((parens (superP `sepBy1` comma)) <|> fmap pure superP)
                       <* reserved "=>")
               <|> return []
    toRCls x = x

    iargsP   =   (mkVar <$> tyVarIdP)
            <|> (parens $ locParserP $ bareTypeP)


    mkVar v  = dummyLoc $ RVar v mempty





classP :: Parser (RClass (Located BareType))
classP
  = do sups <- supersP
       c    <- locUpperIdP
       spaces
       tvs  <- manyTill tyVarIdP (try $ reserved "where")
       ms   <- grabs tyBindP
       spaces
       return $ RClass (fmap symbol c) sups tvs ms -- sups tvs ms
  where
    superP   = locParserP (toRCls <$> bareAtomP (refBindP bindP))
    supersP  = try (((parens (superP `sepBy1` comma)) <|> fmap pure superP)
                       <* reserved "=>")
               <|> return []
    toRCls x = x

rawBodyP :: Parser Body
rawBodyP
  = braces $ do
      v <- symbolP
      reserved "|"
      p <- predP <* spaces
      return $ R v p

tyBodyP :: Located BareType -> Parser Body
tyBodyP ty
  = case outTy (val ty) of
      Just bt | isPropBareType bt
                -> P <$> predP
      _         -> E <$> exprP
    where outTy (RAllT _ t)    = outTy t
          outTy (RAllP _ t)    = outTy t
          outTy (RFun _ _ t _) = Just t
          outTy _              = Nothing

locUpperIdP' :: Parser (Located Symbol)
locUpperIdP' = locParserP upperIdP'

upperIdP' :: Parser Symbol
upperIdP' = try $ symbol <$> condIdP' (isUpper . head)

condIdP'  :: (String -> Bool) -> Parser Symbol
condIdP' f
  = do c  <- letter
       let isAlphaNumOr' c = isAlphaNum c || ('\''== c)
       cs <- many (satisfy isAlphaNumOr')
       blanks
       if f (c:cs) then return (symbol $ T.pack $ c:cs) else parserZero

binderP :: Parser Symbol
binderP    =  try $ symbol <$> idP badc
          <|> pwr <$> parens (idP bad)
  where
    idP p  = many1 (satisfy (not . p))
    badc c = (c == ':') || (c == ',') || bad c
    bad c  = isSpace c || c `elem` ("(,)" :: String)
    pwr s  = symbol $ "(" `mappend` s `mappend` ")"

grabs :: ParsecT s u m a -> ParsecT s u m [a]
grabs p = try (liftM2 (:) p (grabs p))
       <|> return []

measureDefP :: Parser Body -> Parser (Def (Located BareType) LocSymbol)
measureDefP bodyP
  = do mname   <- locParserP symbolP
       (c, xs) <- measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP
       whiteSpace
       let xs'  = (symbol . val) <$> xs
       return   $ Def mname [] (symbol <$> c) Nothing ((, Nothing) <$> xs') body

measurePatP :: Parser (LocSymbol, [LocSymbol])
measurePatP
  =  parens (try conPatP <|> try consPatP <|> nilPatP <|> tupPatP)
 <|> nullaryConPatP

tupPatP :: Parser (Located Symbol, [Located Symbol])
tupPatP  = mkTupPat  <$> sepBy1 locLowerIdP comma

conPatP :: Parser (Located Symbol, [Located Symbol])
conPatP  = (,)       <$> locParserP dataConNameP <*> sepBy locLowerIdP whiteSpace

consPatP :: IsString a
         => Parser (Located a, [Located Symbol])
consPatP = mkConsPat <$> locLowerIdP  <*> colon <*> locLowerIdP

nilPatP :: IsString a
        => Parser (Located a, [t])
nilPatP  = mkNilPat  <$> brackets whiteSpace

nullaryConPatP :: Parser (Located Symbol, [t])
nullaryConPatP = nilPatP <|> ((,[]) <$> locParserP dataConNameP)

mkTupPat :: Foldable t => t a -> (Located Symbol, t a)
mkTupPat zs     = (tupDataCon (length zs), zs)

mkNilPat :: IsString a => t -> (Located a, [t1])
mkNilPat _      = (dummyLoc "[]", []    )

mkConsPat :: IsString a => t1 -> t -> t1 -> (Located a, [t1])
mkConsPat x _ y = (dummyLoc ":" , [x, y])

tupDataCon :: Int -> Located Symbol
tupDataCon n    = dummyLoc $ symbol $ "(" <> replicate (n - 1) ',' <> ")"


-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP :: Parser [(Symbol, BareType)]
dataConFieldsP
  =   (braces $ sepBy predTypeDDP comma)
  <|> (sepBy dataConFieldP spaces)

dataConFieldP :: Parser (Symbol, BareType)
dataConFieldP
  = parens ( try predTypeDDP
             <|> do v <- dummyBindP
                    t <- bareTypeP
                    return (v,t)
           )
    <|> do v <- dummyBindP
           t <- bareTypeP
           return (v,t)

predTypeDDP :: Parser (Symbol, BareType)
predTypeDDP
  = liftM2 (,) bbindP bareTypeP

dataConP :: Parser (Located Symbol, [(Symbol, BareType)])
dataConP
  = do x   <- locParserP dataConNameP
       spaces
       xts <- dataConFieldsP
       return (x, xts)

dataConNameP :: Parser Symbol
dataConNameP
  =  try upperIdP
 <|> pwr <$> parens (idP bad)
  where
     idP p  = many1 (satisfy (not . p))
     bad c  = isSpace c || c `elem` ("(,)" :: String)
     pwr s  = symbol $ "(" <> s <> ")"

dataSizeP :: Parser (Maybe (Symbol -> Expr))
dataSizeP
  = (brackets $ (Just . mkFun) <$> locLowerIdP)
  <|> return Nothing
  where
    mkFun s x = mkEApp (symbol <$> s) [EVar x]

dataDeclP :: Parser DataDecl
dataDeclP = try dataDeclFullP <|> dataDeclSizeP


dataDeclSizeP :: Parser DataDecl
dataDeclSizeP
  = do pos <- getPosition
       x   <- locUpperIdP'
       spaces
       fsize <- dataSizeP
       return $ D x [] [] [] [] pos fsize

dataDeclFullP :: Parser DataDecl
dataDeclFullP
  = do pos <- getPosition
       x   <- locUpperIdP'
       spaces
       fsize <- dataSizeP
       spaces
       ts  <- sepBy tyVarIdP blanks
       ps  <- predVarDefsP
       whiteSpace >> reservedOp "=" >> whiteSpace
       dcs <- sepBy dataConP (reserved "|")
       whiteSpace
       return $ D x ts ps [] dcs pos fsize

---------------------------------------------------------------------
-- | Parsing Qualifiers ---------------------------------------------
---------------------------------------------------------------------

fTyConP :: Parser FTycon
fTyConP
  =   (reserved "int"     >> return intFTyCon)
  <|> (reserved "Integer" >> return intFTyCon)
  <|> (reserved "Int"     >> return intFTyCon)
  <|> (reserved "int"     >> return intFTyCon)
  <|> (reserved "real"    >> return realFTyCon)
  <|> (reserved "bool"    >> return boolFTyCon)
  <|> (symbolFTycon      <$> locUpperIdP)

---------------------------------------------------------------
-- | Bundling Parsers into a Typeclass ------------------------
---------------------------------------------------------------

instance Inputable BareType where
  rr' = doParse' bareTypeP

-- instance Inputable (Measure BareType LocSymbol) where
--   rr' = doParse' measureP
