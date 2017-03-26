{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE DeriveDataTypeable        #-}

module Language.Haskell.Liquid.Parse
  ( hsSpecificationP, specSpecificationP
  , singleSpecP, BPspec, Pspec(..)
  , parseSymbolToLogic
  )
  where

import           Control.Arrow                          (second)
import           Control.Monad
import           Data.String
import           Prelude                                hiding (error)
import           Text.Parsec
import           Text.Parsec.Error                      (newErrorMessage, Message (..))
import           Text.Parsec.Pos

import qualified Text.Parsec.Token                      as Token
import qualified Data.Text                              as T
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import           Data.Monoid
import           Data.Data


import           Data.Char                              (isSpace, isAlpha, isUpper, isAlphaNum, isDigit)
import           Data.List                              (foldl', partition)

import           GHC                                    (ModuleName, mkModuleName)
import           Text.PrettyPrint.HughesPJ              (text, (<+>))

import           Language.Fixpoint.Types                hiding (Error, R, Predicate)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types          -- hiding (Axiom)
import           Language.Fixpoint.Misc                 (mapSnd)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure        as Measure
import           Language.Fixpoint.Parse                hiding (angles, refBindP, refP, refDefP)

import Control.Monad.State

-- import Debug.Trace

--------------------------------------------------------------------------------
-- | Top Level Parsing API -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Used to parse .hs and .lhs files (via ApiAnnotations)

-------------------------------------------------------------------------------
hsSpecificationP :: ModuleName
                 -> [(SourcePos, String)] -> [BPspec]
                 -> Either [Error] (ModName, Measure.BareSpec)
-------------------------------------------------------------------------------
hsSpecificationP modName specComments specQuotes =
  case go ([], []) initPState $ reverse specComments of
    ([], specs) ->
      Right $ mkSpec (ModName SrcImport modName) (specs ++ specQuotes)
    (errs, _) ->
      Left errs
  where
    go (errs, specs) _ []
      = (reverse errs, reverse specs)
    go (errs, specs) pstate ((pos, specComment):xs)
      = case parseWithError pstate specP pos specComment of
          Left err        -> go (err:errs, specs) pstate xs
          Right (st,spec) -> go (errs,spec:specs) st xs

-- | Used to parse .spec files

--------------------------------------------------------------------------
specSpecificationP  :: SourceName -> String -> Either Error (ModName, Measure.BareSpec)
--------------------------------------------------------------------------
specSpecificationP f s = mapRight snd $  parseWithError initPState specificationP (newPos f 1 1) s

specificationP :: Parser (ModName, Measure.BareSpec)
specificationP
  = do reserved "module"
       reserved "spec"
       name   <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace)
       return $ mkSpec (ModName SpecImport $ mkModuleName $ symbolString name) xs

-------------------------------------------------------------------------------
singleSpecP :: SourcePos -> String -> Either Error BPspec
-------------------------------------------------------------------------------
singleSpecP pos = mapRight snd . parseWithError initPState specP pos

mapRight :: (a -> b) -> Either l a -> Either l b
mapRight f (Right x) = Right $ f x
mapRight _ (Left x)  = Left x

---------------------------------------------------------------------------
parseWithError :: PState -> Parser a -> SourcePos -> String -> Either Error (PState, a)
---------------------------------------------------------------------------
parseWithError pstate parser p s =
  case runState (runParserT doParse 0 (sourceName p) s) pstate of
    (Left e, _)            -> Left  $ parseErrorError e
    (Right (r, "", _), st) -> Right (st, r)
    (Right (_, rem, _), _) -> Left  $ parseErrorError $ remParseError p s rem
  where
    -- See http://stackoverflow.com/questions/16209278/parsec-consume-all-input
    doParse = setPosition p >> remainderP (whiteSpace *> parser <* (whiteSpace >> eof))


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
parseSymbolToLogic f = mapRight snd . parseWithError initPState toLogicP (newPos f 1 1)

toLogicP :: Parser LogicMap
toLogicP
  = toLogicMap <$> many toLogicOneP

toLogicOneP :: Parser  (LocSymbol, [Symbol], Expr)
toLogicOneP
  = do reserved "define"
       (x:xs) <- many1 (locParserP symbolP)
       reservedOp "="
       e      <- exprP
       return (x, val <$> xs, e)


defineP :: Parser (LocSymbol, Symbol)
defineP = do v <- locParserP binderP
             spaces
             reservedOp "="
             spaces
             x <- binderP
             return (v, x)

----------------------------------------------------------------------------------
-- Lexer Tokens ------------------------------------------------------------------
----------------------------------------------------------------------------------

dot :: Parser String
dot           = Token.dot           lexer

angles :: Parser a -> Parser a
angles        = Token.angles        lexer

stringLiteral :: Parser String
stringLiteral = Token.stringLiteral lexer

----------------------------------------------------------------------------------
-- BareTypes ---------------------------------------------------------------------
----------------------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType
bareTypeP
  =  (reserved "forall" >> (bareAllP <|> bareAllS))
 <|> try bareConstraintP -- starts with braces
 <|> try bareFunP -- starts with lowerId or parens or '_'
 <|> bareAtomBindP
 <|> (angles (do t <- parens bareTypeP
                 p <- monoPredicateP
                 return $ t `strengthen` MkUReft mempty p mempty))
 <?> "bareTypeP"

bareArgP :: Symbol -> Parser BareType
bareArgP vv
  =  bareAtomP (refDefP vv)
 <|> parens bareTypeP
 <?> "bareArgP"


bareAtomP :: (Parser Expr -> Parser (Reft -> BareType) -> Parser BareType)
          -> Parser BareType
bareAtomP ref
  =  ref refasHoleP bbaseP
 <|> holeP
 <|> (dummyP (bbaseP <* spaces))
 <?> "bareAtomP"

bareAtomBindP :: Parser BareType
bareAtomBindP = bareAtomP refBindBindP

{-
refBindP :: Parser Symbol
         -> Parser Expr
         -> Parser (Reft -> BareType)
         -> Parser BareType
refBindP bp rp kindP'
  = braces (
      (try(do x  <- bp
              i  <- freshIntP
              t  <- kindP'
              reservedOp "|"
              ra <- rp <* spaces
              let xi = intSymbol x i
              -- xi is a unique var based on the name in x.
              -- su replaces any use of x in the balance of the expression with the unique val
              let su v = if v == x then xi else v
              return $ substa su $ t (Reft (x, ra)) ))
     <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))
     <?> "refBindP"
   )
-}

refBindBindP :: Parser Expr
             -> Parser (Reft -> BareType)
             -> Parser BareType
refBindBindP rp kindP'
  = braces (
      (try(do x  <- bindP
              i  <- freshIntP
              t  <- kindP'
              reservedOp "|"
              ra <- rp <* spaces
              let xi = intSymbol x i
              -- xi is a unique var based on the name in x.
              -- su replaces any use of x in the balance of the expression with the unique val
              let su v = if v == x then xi else v
              return $ substa su $ t (Reft (x, ra)) ))
     <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))
     <?> "refBindBindP"
   )


refBindOptBindP :: Symbol
         -> Parser Expr
         -> Parser (Reft -> BareType)
         -> Parser BareType
refBindOptBindP vv rp kindP'
  = braces (
      (try(do x  <- optBindP vv
              i  <- freshIntP
              t  <- kindP'
              reservedOp "|"
              ra <- rp <* spaces
              let xi = intSymbol x i
              -- xi is a unique var based on the name in x.
              -- su replaces any use of x in the balance of the expression with the unique val
              let su v = if v == x then xi else v
              return $ substa su $ t (Reft (x, ra)) ))
     <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))
     <?> "refBindP"
   )

refP :: Parser (Reft -> BareType) -> Parser BareType
refP = refBindBindP refaP

refDefP :: Symbol -> Parser Expr -> Parser (Reft -> BareType) -> Parser BareType
refDefP x  = refBindOptBindP x


-- "sym :" or return the devault sym
optBindP :: Symbol
         -> Parser Symbol
optBindP x = try bindP <|> return x

holeP :: Parser (RType c tv (UReft Reft))
holeP       = reserved "_" >> spaces >> return (RHole $ uTop $ Reft ("VV", hole))

holeRefP :: Parser (r -> RType c tv (UReft r))
holeRefP    = reserved "_" >> spaces >> return (RHole . uTop)

-- NOPROP refasHoleP :: Parser Expr
-- NOPROP refasHoleP  = try refaP
-- NOPROP          <|> (reserved "_" >> return hole)

refasHoleP :: Parser Expr
refasHoleP
  =  (reserved "_" >> return hole)
 <|> refaP
 <?> "refasHoleP"

-- FIXME: the use of `blanks = oneOf " \t"` here is a terrible and fragile hack
-- to avoid parsing:
--
--   foo :: a -> b
--   bar :: a
--
-- as `foo :: a -> b bar`..
bbaseP :: Parser (Reft -> BareType)
bbaseP
  =  holeRefP  -- Starts with '_'
 <|> liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> parseHelper
 <|> liftM5 bCon bTyConP stratumP predicatesP (sepBy bareTyArgP blanks) mmonoPredicateP
           -- starts with "'" or upper case char
 <?> "bbaseP"
 where
   parseHelper = do
     l <- lowerIdP
     (    (liftM2 bAppTy (return $ bTyVar l) (sepBy1 bareTyArgP blanks))
      <|> (liftM3 bRVar  (return $ bTyVar l) stratumP monoPredicateP))

bTyConP :: Parser BTyCon
bTyConP
  =  (reservedOp "'" >> (mkPromotedBTyCon <$> locUpperIdP))
 <|> mkBTyCon <$> locUpperIdP
 <?> "bTyConP"

classBTyConP :: Parser BTyCon
classBTyConP = mkClassBTyCon <$> locUpperIdP

stratumP :: Parser Strata
stratumP
  = do reservedOp "^"
       bstratumP
 <|> return mempty
 <?> "stratumP"

bstratumP :: Parser [Stratum]
bstratumP
  = ((:[]) . SVar) <$> symbolP

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  holeRefP
 <|> liftM2 bLst (brackets (maybeP bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM5 bCon bTyConP stratumP predicatesP (return []) (return mempty))
 <|> liftM3 bRVar (bTyVar <$> lowerIdP) stratumP monoPredicateP
 <?> "bbaseNoAppP"

maybeP :: ParsecT s u m a -> ParsecT s u m (Maybe a)
maybeP p = liftM Just p <|> return Nothing

bareTyArgP :: Parser BareType
bareTyArgP
  =  -- try (RExprArg . expr <$> binderP) <|>
      (RExprArg . fmap expr <$> locParserP integer)
 <|> try (braces $ RExprArg <$> locParserP exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)
 <?> "bareTyArgP"

bareAtomNoAppP :: Parser BareType
bareAtomNoAppP
  =  refP bbaseNoAppP
 <|> (dummyP (bbaseNoAppP <* spaces))
 <?> "bareAtomNoAppP"


bareConstraintP :: Parser BareType
bareConstraintP
  = do ct   <- braces constraintP
       t    <- bareTypeP
       return $ rrTy ct t

constraintP :: Parser BareType
constraintP
  = do xts <- constraintEnvP
       t1  <- bareTypeP
       reservedOp "<:"
       t2  <- bareTypeP
       return $ fromRTypeRep $ RTypeRep [] [] [] ((val . fst <$> xts) ++ [dummySymbol])
                                                 (replicate (length xts + 1) mempty)
                                                 ((snd <$> xts) ++ [t1]) t2

constraintEnvP :: Parser [(LocSymbol, BareType)]
constraintEnvP
   =  try (do xts <- sepBy tyBindNoLocP comma
              reservedOp "|-"
              return xts)
  <|> return []
  <?> "constraintEnvP"

rrTy :: Monoid r => RType c tv r -> RType c tv r -> RType c tv r
rrTy ct = RRTy (xts ++ [(dummySymbol, tr)]) mempty OCons
  where
    tr   = ty_res trep
    xts  = zip (ty_binds trep) (ty_args trep)
    trep = toRTypeRep ct

bareAllS :: Parser BareType
bareAllS
  = do ss <- angles $ sepBy1 symbolP comma
       dot
       t  <- bareTypeP
       return $ foldr RAllS t ss

bareAllP :: Parser BareType
bareAllP
  = do as <- tyVarDefsP
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ foldr RAllT (foldr RAllP t ps) (makeRTVar <$> as)

tyVarDefsP :: Parser [BTyVar]
tyVarDefsP
  = try (parens $ many (bTyVar <$> tyKindVarIdP))
 <|> many (bTyVar <$> tyVarIdP)
 <?> "tyVarDefsP"

tyVarIdP :: Parser Symbol
tyVarIdP = symbol <$> condIdP alphanums (isSmall . head)
  where
    alphanums = S.fromList $ ['a'..'z'] ++ ['0'..'9']

tyKindVarIdP :: Parser Symbol
tyKindVarIdP
   =  try ( do s <- tyVarIdP; reservedOp "::"; _ <- kindP; return s)
  <|> tyVarIdP
  <?> "tyKindVarIdP"

kindP :: Parser BareType
kindP = bareAtomBindP

predVarDefsP :: Parser [PVar BSort]
predVarDefsP
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []
 <?> "predVarDefP"

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
    isOk      = isPropBareType tOut --  isHPropBareType tOut
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
  =   (reservedOp "->" >> return ArrowFun)
  <|> (reservedOp "=>" >> return ArrowPred)

bareFunP :: Parser BareType
bareFunP = do
  eb   <- eBindP
  let b = eBindSym eb
  t1   <- bareArgP b
  a    <- arrowP
  t2   <- bareTypeP
  return $ bareArrow eb t1 a t2

type EBind = Located (Either Symbol Symbol)

eBindSym :: EBind -> Symbol
eBindSym = either id id . val

eBindP :: Parser EBind
eBindP = locParserP (try (Left <$> funBindP) <|> (Right <$> dummyBindP))

funBindP :: Parser Symbol
funBindP = lowerIdP <* colon

dummyBindP :: Parser Symbol
dummyBindP = tempSymbol "db" <$> freshIntP

-- TODO:AZ this is only ever used with BareType, use that instead of RType BTyVar tv r
-- bareArrow :: (Monoid r)
--           => EBind -> RType BTyCon tv r -> ArrowSym -> RType BTyCon tv r
--           -> RType BTyCon tv r
bareArrow :: EBind -> BareType -> ArrowSym -> BareType
          -> BareType
bareArrow eb t1 ArrowFun t2
  = rFun (eBindSym eb) t1 t2
bareArrow eb t1 ArrowPred t2
  = case val eb of
      Right _ -> foldr (rFun dummySymbol) t2 (getClasses t1)
      Left x  -> uError $ ErrOther sp ("Invalid class constraint binder:" <+> pprint x)
    where
      sp = fSrcSpanSrcSpan . srcSpan $ eb

isPropBareType :: RType BTyCon t t1 -> Bool
isPropBareType  = isPrimBareType boolConName -- propConName

-- isHPropBareType :: RType BTyCon t t1 -> Bool
-- isHPropBareType = isPrimBareType hpropConName

isPrimBareType :: Symbol -> RType BTyCon t t1 -> Bool
isPrimBareType n (RApp tc [] _ _) = val (btc_tc tc) == n
isPrimBareType _ _                = False

getClasses :: RType BTyCon t t1 -> [RType BTyCon t t1]
getClasses (RApp tc ts ps r)
  | isTuple tc
  = concatMap getClasses ts
  | otherwise
  = [RApp (tc { btc_class = True }) ts ps r]
getClasses t
  = [t]

dummyP ::  Monad m => m (Reft -> b) -> m b
dummyP fm
  = fm `ap` return dummyReft

symsP :: (IsString tv, Monoid r)
      => Parser [(Symbol, RType c tv r)]
symsP
  = do reservedOp "\\"
       ss <- sepBy symbolP spaces
       reservedOp "->"
       return $ (, dummyRSort) <$> ss
 <|> return []
 <?> "symsP"

dummyRSort :: (IsString tv, Monoid r) => RType c tv r
dummyRSort
  = RVar "dummy" mempty

predicatesP :: (IsString tv, Monoid r)
            => Parser [Ref (RType c tv r) BareType]
predicatesP
   =  (angles $ sepBy1 predicate1P comma)
  <|> return []
  <?> "predicatesP"

predicate1P :: (IsString tv, Monoid r)
            => Parser (Ref (RType c tv r) BareType)
predicate1P
   =  try (RProp <$> symsP <*> refP bbaseP)
  <|> (rPropP [] . predUReft <$> monoPredicate1P)
  <|> (braces $ bRProp <$> symsP' <*> refaP)
  <?> "predicate1P"
   where
    symsP'       = do ss    <- symsP
                      fs    <- mapM refreshSym (fst <$> ss)
                      return $ zip ss fs
    refreshSym s = intSymbol s <$> freshIntP

mmonoPredicateP :: Parser Predicate
mmonoPredicateP
   = try (angles $ angles monoPredicate1P)
  <|> return mempty
  <?> "mmonoPredicateP"

monoPredicateP :: Parser Predicate
monoPredicateP
   = try (angles monoPredicate1P)
  <|> return mempty
  <?> "monoPredicateP"

monoPredicate1P :: Parser Predicate
monoPredicate1P
   =  (reserved "True" >> return mempty)
  <|> (pdVar <$> parens predVarUseP)
  <|> (pdVar <$>        predVarUseP)
  <?> "monoPredicate1P"

predVarUseP :: IsString t
            => Parser (PVar t)
predVarUseP
  = do (p, xs) <- funArgsP
       return   $ PV p (PVProp dummyTyId) dummySymbol [ (dummyTyId, dummySymbol, x) | x <- xs ]

funArgsP :: Parser (Symbol, [Expr])
funArgsP  = try realP <|> empP <?> "funArgsP"
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
           <?> "bargsP"
    bvsP   = try ( do reserved "forall"
                      xs <- many (locParserP (bTyVar <$> symbolP))
                      reservedOp  "."
                      return (fmap (`RVar` mempty) <$> xs)
                 )
           <|> return []


infixGenP :: Assoc -> Parser ()
infixGenP assoc = do
   spaces
   p <- maybeDigit
   spaces
   s <- infixIdP
   spaces
   addOperatorP (FInfix p s Nothing assoc)


infixP :: Parser ()
infixP = infixGenP AssocLeft

infixlP :: Parser ()
infixlP = infixGenP AssocLeft

infixrP :: Parser ()
infixrP = infixGenP AssocRight

maybeDigit :: Parser (Maybe Int)
maybeDigit
  = try (satisfy isDigit >>= return . Just . read . (:[]))
  <|> return Nothing

------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRProp :: [((Symbol, τ), Symbol)]
       -> Expr -> Ref τ (RType c BTyVar (UReft Reft))
bRProp []    _    = panic Nothing "Parse.bRProp empty list"
bRProp syms' expr = RProp ss $ bRVar (BTV dummyName) mempty mempty r
  where
    (ss, (v, _))  = (init syms, last syms)
    syms          = [(y, s) | ((_, s), y) <- syms']
    su            = mkSubst [(x, EVar y) | ((x, _), y) <- syms']
    r             = su `subst` Reft (v, expr)

bRVar :: tv -> Strata -> Predicate -> r -> RType c tv (UReft r)
bRVar α s p r             = RVar α (MkUReft r p s)

bLst :: Maybe (RType BTyCon tv (UReft r))
     -> [RTProp BTyCon tv (UReft r)]
     -> r
     -> RType BTyCon tv (UReft r)
bLst (Just t) rs r        = RApp (mkBTyCon $ dummyLoc listConName) [t] rs (reftUReft r)
bLst (Nothing) rs r       = RApp (mkBTyCon $ dummyLoc listConName) []  rs (reftUReft r)

bTup :: (PPrint r, Reftable r)
     => [RType BTyCon tv (UReft r)]
     -> [RTProp BTyCon tv (UReft r)]
     -> r
     -> RType BTyCon tv (UReft r)
bTup [t] _ r | isTauto r  = t
             | otherwise  = t `strengthen` (reftUReft r)
bTup ts rs r              = RApp (mkBTyCon $ dummyLoc tupConName) ts rs (reftUReft r)


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

type BPspec = Pspec (Located BareType) LocSymbol

data Pspec ty ctor
  = Meas    (Measure ty ctor)
  | Assm    (LocSymbol, ty)
  | Asrt    (LocSymbol, ty)
  | LAsrt   (LocSymbol, ty)
  | Asrts   ([LocSymbol], (ty, Maybe [Located Expr]))
  | Impt    Symbol
  | DDecl   DataDecl
  | NTDecl  DataDecl
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
  | Insts   (LocSymbol, Maybe Int)
  | HMeas   LocSymbol
  | Reflect LocSymbol
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
  | BFix    ()
  | Define  (LocSymbol, Symbol)
  deriving (Data, Typeable, Show)

-- | For debugging
{-instance Show (Pspec a b) where
  show (Meas   _) = "Meas"
  show (Assm   _) = "Assm"
  show (Asrt   _) = "Asrt"
  show (LAsrt  _) = "LAsrt"
  show (Asrts  _) = "Asrts"
  show (Impt   _) = "Impt"
  show (DDecl  _) = "DDecl"
  show (NTDecl _) = "NTDecl"
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
  -- show (Axiom  _) = "Axiom"
  show (Insts  _) = "Insts"
  show (Reflect _) = "Reflect"
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
  show (BFix   _) = "BFix"
  show (Define _) = "Define"-}

mkSpec :: ModName -> [BPspec] -> (ModName, Measure.Spec (Located BareType) LocSymbol)
mkSpec name xs         = (name,) $ Measure.qualifySpec (symbol name) Measure.Spec
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.asmSigs    = [a | Assm   a <- xs]
  , Measure.sigs       = [a | Asrt   a <- xs]
                      ++ [(y, t) | Asrts (ys, (t, _)) <- xs, y <- ys]
  , Measure.localSigs  = []
  , Measure.reflSigs   = []
  , Measure.invariants = [t | Invt   t <- xs]
  , Measure.ialiases   = [t | IAlias t <- xs]
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs] ++ [d | NTDecl d <- xs]
  , Measure.newtyDecls = [d | NTDecl d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.ealiases   = [e | EAlias e <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.decr       = [d | Decr d   <- xs]
  , Measure.lvars      = [d | LVars d  <- xs]
  , Measure.autois     = M.fromList [s | Insts s <- xs]
  , Measure.pragmas    = [s | Pragma s <- xs]
  , Measure.cmeasures  = [m | CMeas  m <- xs]
  , Measure.imeasures  = [m | IMeas  m <- xs]
  , Measure.classes    = [c | Class  c <- xs]
  , Measure.dvariance  = [v | Varia  v <- xs]
  , Measure.rinstance  = [i | RInst  i <- xs]
  , Measure.termexprs  = [(y, es) | Asrts (ys, (_, Just es)) <- xs, y <- ys]
  , Measure.lazy       = S.fromList [s | Lazy   s <- xs]
  , Measure.bounds     = M.fromList [(bname i, i) | PBound i <- xs]
  , Measure.reflects   = S.fromList [s | Reflect s <- xs]
  , Measure.hmeas      = S.fromList [s | HMeas  s <- xs]
  , Measure.inlines    = S.fromList [s | Inline s <- xs]
  , Measure.autosize   = S.fromList [s | ASize  s <- xs]
  , Measure.hbounds    = S.fromList [s | HBound s <- xs]
  , Measure.defs       = M.fromList [d | Define d <- xs]
  }

-- | Parse a single top level liquid specification
specP :: Parser BPspec
specP
  =     (fallbackSpecP "assume"     (liftM Assm    tyBindP  ))
    <|> (fallbackSpecP "assert"     (liftM Asrt    tyBindP  ))
    <|> (fallbackSpecP "autosize"   (liftM ASize   asizeP   ))
    <|> (reserved "Local"         >> liftM LAsrt   tyBindP  )
    <|> (fallbackSpecP "axiomatize" (liftM Reflect axiomP   ))
    <|> (fallbackSpecP "reflect"    (liftM Reflect axiomP   ))

    <|> (fallbackSpecP "measure" (((try (liftM Meas    measureP ))
                                     <|> liftM HMeas   hmeasureP)))

    <|> (fallbackSpecP "define"     (liftM Define  defineP  ))
    <|> (reserved "infixl"        >> liftM BFix    infixlP  )
    <|> (reserved "infixr"        >> liftM BFix    infixrP  )
    <|> (reserved "infix"         >> liftM BFix    infixP   )
    <|> (fallbackSpecP "defined"    (liftM Meas    measureP ))
    <|> (fallbackSpecP "inline"     (liftM Inline  inlineP  ))

    <|> (fallbackSpecP "bound"    (((liftM PBound  boundP   )
                                <|> (liftM HBound  hboundP  ))))
    <|> (reserved "class"
         >> ((reserved "measure"  >> liftM CMeas  cMeasureP )
                                 <|> liftM Class  classP    ))
    <|> (reserved "instance"
         >> ((reserved "measure"  >> liftM IMeas  iMeasureP )
                                 <|> liftM RInst  instanceP ))

    <|> (reserved "import"        >> liftM Impt   symbolP   )

    <|> (reserved "data"
        >> ((reserved "variance"  >> liftM Varia datavarianceP)
                                 <|> liftM DDecl  dataDeclP ))

    <|> (reserved "newtype"       >> liftM NTDecl newtypeP )
    <|> (reserved "include"       >> liftM Incl   filePathP )
    <|> (fallbackSpecP "invariant"  (liftM Invt   invariantP))
    <|> (reserved "using"         >> liftM IAlias invaliasP )
    <|> (reserved "type"          >> liftM Alias  aliasP    )
    <|> (fallbackSpecP "predicate"  (liftM EAlias ealiasP   ))
    <|> (fallbackSpecP "expression" (liftM EAlias ealiasP   ))
    <|> (fallbackSpecP "embed"      (liftM Embed  embedP    ))
    <|> (fallbackSpecP "qualif"     (liftM Qualif (qualifierP sortP)))
    <|> (reserved "Decrease"      >> liftM Decr   decreaseP )
    <|> (reserved "LAZYVAR"       >> liftM LVars  lazyVarP  )
    <|> (reserved "Strict"        >> liftM Lazy   lazyVarP  )
    <|> (reserved "Lazy"          >> liftM Lazy   lazyVarP  )
    <|> (reserved "automatic-instances" >> liftM Insts autoinstP  )
    <|> (reserved "LIQUID"        >> liftM Pragma pragmaP   )
    <|> {- DEFAULT -}                liftM Asrts  tyBindsP
    <?> "specP"

-- | Try the given parser on the tail after matching the reserved word, and if
-- it fails fall back to parsing it as a haskell signature for a function with
-- the same name.
fallbackSpecP :: String -> Parser BPspec -> Parser BPspec
fallbackSpecP kw p = do
  (Loc l1 l2 _) <- locParserP (reserved kw)
  (p <|> liftM Asrts (tyBindsRemP (Loc l1 l2 (symbol kw)) ))

-- | Same as tyBindsP, except the single initial symbol has already been matched
tyBindsRemP :: LocSymbol -> Parser ([LocSymbol], (Located BareType, Maybe [Located Expr]))
tyBindsRemP sym = do
  dcolon
  tb <- termBareTypeP
  return ([sym],tb)

pragmaP :: Parser (Located String)
pragmaP = locParserP stringLiteral

autoinstP :: Parser (LocSymbol, Maybe Int)
autoinstP = do x <- locParserP binderP
               spaces
               i <- maybeP (reserved "with" >> integer)
               return (x, fromIntegral <$> i)

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

varianceP :: Parser Variance
varianceP = (reserved "bivariant"     >> return Bivariant)
        <|> (reserved "invariant"     >> return Invariant)
        <|> (reserved "covariant"     >> return Covariant)
        <|> (reserved "contravariant" >> return Contravariant)
        <?> "Invalid variance annotation\t Use one of bivariant, invariant, covariant, contravariant"

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
termBareTypeP = do
  t <- locParserP genBareTypeP
  (termTypeP t
    <|> return (t, Nothing))

termTypeP :: Located BareType ->Parser (Located BareType, Maybe [Located Expr])
termTypeP t
  = do
       reservedOp "/"
       es <- brackets $ sepBy (locParserP exprP) comma
       return (t, Just es)

-- -------------------------------------

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
      <?> "ealiasP"

rtAliasP :: (Symbol -> tv) -> Parser ty -> Parser (RTAlias tv ty)
rtAliasP f bodyP
  -- TODO:AZ pretty sure that all the 'spaces' can be removed below, given
  --         proper use of reserved and reservedOp now
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
  = sing <$> locParserP (rit <$> classBTyConP <*> (map val <$> classParams))
  where
    rit t as    = RApp t ((`RVar` mempty) <$> as) [] mempty
    classParams =  (reserved "where" >> return [])
               <|> ((:) <$> (fmap bTyVar <$> locLowerIdP) <*> classParams)
    sing x      = [x]

instanceP :: Parser (RInstance (Located BareType))
instanceP
  = do _    <- supersP
       c    <- classBTyConP
       spaces
       tvs  <- (try oneClassArg) <|> (manyTill iargsP (try $ reserved "where"))
       ms   <- sepBy riMethodSigP semi
       spaces
       return $ RI c tvs ms
  where
    superP   = locParserP (toRCls <$> bareAtomBindP)
    supersP  = try (((parens (superP `sepBy1` comma)) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []
    toRCls x = x

    iargsP   =   (mkVar . bTyVar <$> tyVarIdP)
            <|> (parens $ locParserP $ bareTypeP)


    mkVar v  = dummyLoc $ RVar v mempty


riMethodSigP :: Parser (LocSymbol, RISig (Located BareType))
riMethodSigP
  = try (do reserved "assume"
            (x, t) <- tyBindP
            return (x, RIAssumed t) )
 <|> do (x, t) <- tyBindP
        return (x, RISig t)
 <?> "riMethodSigP"



classP :: Parser (RClass (Located BareType))
classP
  = do sups <- supersP
       c    <- classBTyConP
       spaces
       tvs  <- manyTill (bTyVar <$> tyVarIdP) (try $ reserved "where")
       ms   <- grabs tyBindP
       spaces
       return $ RClass c sups tvs ms -- sups tvs ms
  where
    superP   = locParserP (toRCls <$> bareAtomBindP)
    supersP  = try (((parens (superP `sepBy1` comma)) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []
    toRCls x = x

rawBodyP :: Parser Body
rawBodyP
  = braces $ do
      v <- symbolP
      reservedOp "|"
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
upperIdP' = try (symbol <$> condIdP' (isUpper . head))
        <|> (symbol <$> infixCondIdP')

-- TODO:AZ this looks dodgy, rather use reserved, reservedOp
condIdP'  :: (String -> Bool) -> Parser Symbol
condIdP' f
  = do c  <- letter
       let isAlphaNumOr' c = isAlphaNum c || ('\''== c)
       cs <- many (satisfy isAlphaNumOr')
       blanks
       if f (c:cs) then return (symbol $ T.pack $ c:cs) else parserZero

infixCondIdP' :: Parser Symbol
infixCondIdP'
  = do sym <- parens $ do
         c1 <- colon
         -- This is the same thing as 'startsVarSymASCII' from ghc-boot-th,
         -- but LH can't use that at the moment since it requires GHC 7.10.
         let isASCIISymbol = (`elem` ("!#$%&*+./<=>?@\\^|~-" :: String))
         ss <- many (satisfy isASCIISymbol)
         c2 <- colon
         return $ symbol $ T.pack $ c1 ++ ss ++ c2
       blanks
       return sym

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
 <?> "measurePatP"

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
                 <?> "nullaryConPatP"

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
   =  braces (sepBy predTypeDDP comma)
  <|> sepBy dataConFieldP spaces
  <?> "dataConFieldP"

dataConFieldP :: Parser (Symbol, BareType)
dataConFieldP
   =  parens (try predTypeDDP <|> dbTypeP)
  <|> dbTypeP
  <?> "dataConFieldP"
  where
    dbTypeP = (,) <$> dummyBindP <*> bareTypeP

predTypeDDP :: Parser (Symbol, BareType)
predTypeDDP = (,) <$> bbindP <*> bareTypeP

bbindP   :: Parser Symbol
bbindP   = lowerIdP <* dcolon
{-
lowerIdP :: Parser Symbol
lowerIdP = condIdP symChars (isSmall . head)
-}

dataConP :: Parser (Located Symbol, [(Symbol, BareType)])
dataConP
  = do x   <- locParserP dataConNameP
       spaces
       xts <- dataConFieldsP
       return (x, xts)


adtDataConP :: Parser (Located Symbol, [(Symbol, BareType)])
adtDataConP
  = do x   <- locParserP dataConNameP
       dcolon
       xts <- tRepToArgs . toRTypeRep <$> bareTypeP
       return (x, xts)
  where
    tRepToArgs trep = zip (ty_binds trep) (ty_args trep)

dataConNameP :: Parser Symbol
dataConNameP
  =  try upperIdP
 <|> pwr <$> parens (idP bad)
 <?> "dataConNameP"
  where
     idP p  = many1 (satisfy (not . p))
     bad c  = isSpace c || c `elem` ("(,)" :: String)
     pwr s  = symbol $ "(" <> s <> ")"

dataSizeP :: Parser (Maybe SizeFun)
dataSizeP
  = brackets (Just . SymSizeFun <$> locLowerIdP)
  <|> return Nothing

dataDeclP :: Parser DataDecl
dataDeclP
   =  try dataDeclFullP
  <|> try adtDataDeclFullP
  <|> dataDeclSizeP
  <?> "dataDeclP"

newtypeP :: Parser DataDecl
newtypeP = dataDeclP

dataDeclSizeP :: Parser DataDecl
dataDeclSizeP = do
  pos <- getPosition
  x   <- locUpperIdP'
  spaces
  fsize <- dataSizeP
  return $ D x [] [] [] [] pos fsize

dataDeclFullP :: Parser DataDecl
dataDeclFullP = do
  pos <- getPosition
  x   <- locUpperIdP'
  spaces
  fsize <- dataSizeP
  spaces
  ts  <- sepBy tyVarIdP blanks
  ps  <- predVarDefsP
  whiteSpace >> reservedOp "=" >> whiteSpace
  dcs <- sepBy dataConP (reservedOp "|")
  whiteSpace
  return $ D x ts ps [] dcs pos fsize


adtDataDeclFullP :: Parser DataDecl
adtDataDeclFullP = do
  pos <- getPosition
  x   <- locUpperIdP'
  spaces
  fsize <- dataSizeP
  spaces
  (ts, ps) <- tsps
  spaces
  dcs <- sepBy adtDataConP (reservedOp "|")
  whiteSpace
  return $ D x ts ps [] dcs pos fsize
  where
    tsps =  try ((, []) <$> manyTill tyVarIdP (try $ reserved "where"))
        <|> do ts <- sepBy tyVarIdP blanks
               ps  <- predVarDefsP
               whiteSpace >> reserved "where" >> whiteSpace
               return (ts, ps)

---------------------------------------------------------------------
-- | Parsing Qualifiers ---------------------------------------------
---------------------------------------------------------------------

fTyConP :: Parser FTycon
fTyConP
  =   (reserved "int"     >> return intFTyCon)
  <|> (reserved "Integer" >> return intFTyCon)
  <|> (reserved "Int"     >> return intFTyCon)
  <|> (reserved "real"    >> return realFTyCon)
  <|> (reserved "bool"    >> return boolFTyCon)
  <|> (symbolFTycon      <$> locUpperIdP)
  <?> "fTyConP"

---------------------------------------------------------------
-- | Bundling Parsers into a Typeclass ------------------------
---------------------------------------------------------------

-- instance Inputable BareType where
--   rr' = doParse' bareTypeP

-- instance Inputable (Measure BareType LocSymbol) where
--   rr' = doParse' measureP
