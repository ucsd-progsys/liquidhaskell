{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE DeriveDataTypeable        #-}

module Language.Haskell.Liquid.Parse
  ( hsSpecificationP
  , specSpecificationP
  , singleSpecP
  , BPspec
  , Pspec(..)
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
import           Data.Maybe (isNothing, fromMaybe)


import           Data.Char                              (isSpace, isAlpha, isUpper, isAlphaNum, isDigit)
import           Data.List                              (foldl', partition)

import           GHC                                    (ModuleName, mkModuleName)
import           Text.PrettyPrint.HughesPJ              (text )
-- import           SrcLoc                                 (noSrcSpan)

import           Language.Fixpoint.Types                hiding (panic, SVar, DDecl, DataDecl, DataCtor (..), Error, R, Predicate)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types          -- hiding (Axiom)
import qualified Language.Fixpoint.Misc                 as F           --  (mapSnd)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure        as Measure
import           Language.Fixpoint.Parse                hiding (dataDeclP, angles, refBindP, refP, refDefP)

import Control.Monad.State

-- import Debug.Trace

--------------------------------------------------------------------------------
-- | Top Level Parsing API -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Used to parse .hs and .lhs files (via ApiAnnotations)

-------------------------------------------------------------------------------
hsSpecificationP :: ModuleName
                 -> [(SourcePos, String)]
                 -> [BPspec]
                 -> Either [Error] (ModName, Measure.BareSpec)
-------------------------------------------------------------------------------
-- hsSpecificationP _ [] _ = Left [ErrParseAnn noSrcSpan (text "Malformed annotation")]
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



--------------------------------------------------------------------------------
-- Parse to Logic  -------------------------------------------------------------
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Lexer Tokens ----------------------------------------------------------------
--------------------------------------------------------------------------------

dot :: Parser String
dot = Token.dot lexer

angles :: Parser a -> Parser a
angles = Token.angles lexer

stringLiteral :: Parser String
stringLiteral = Token.stringLiteral lexer

--------------------------------------------------------------------------------
-- | BareTypes -----------------------------------------------------------------
--------------------------------------------------------------------------------

{- | [NOTE:BARETYPE-PARSE] Fundamentally, a type is ofthe form

      comp -> comp -> ... -> comp

So

  bt = comp
     | comp '->' bt

  comp = circle
       | '(' bt ')'

  circle = the ground component of a baretype, sans parens or "->" at the top level

Each 'comp' should have a variable to refer to it,
either a parser-assigned one or given explicitly. e.g.

  xs : [Int]

-}

data ParamComp = PC { _pci :: PcScope
                    , _pct :: BareType }
                    deriving (Show)

data PcScope = PcImplicit Symbol
             | PcExplicit Symbol
             | PcNoSymbol
             deriving (Eq,Show)

nullPC :: BareType -> ParamComp
nullPC bt = PC PcNoSymbol bt

btP :: Parser ParamComp
btP = do
  c@(PC sb _) <- compP
  case sb of
    PcNoSymbol   -> return c
    PcImplicit b -> parseFun c b
    PcExplicit b -> parseFun c b
  <?> "btP"
  where
    parseFun c@(PC sb t1) b  =
      ((do
            reservedOp "->"
            PC _ t2 <- btP
            return (PC sb (rFun b t1 t2)))
        <|>
         (do
            reservedOp "=>"
            PC _ t2 <- btP
            -- TODO:AZ return an error if s == PcExplicit
            return $ PC sb $ foldr (rFun dummySymbol) t2 (getClasses t1))
         <|> return c)


-- _rFun' b t1 t2 = tracepp msg (rFun b t1 t2)
 -- where msg    = "RFUN: b = " ++ showpp b ++
                -- " t1 = "     ++ showpp t1 ++
                -- " t2 = "     ++ showpp t2

compP :: Parser ParamComp
compP = circleP <* whiteSpace <|> parens btP <?> "compP"

circleP :: Parser ParamComp
circleP
  =  nullPC <$> (reserved "forall" >> bareAllP)
 <|> holePC                                 -- starts with '_'
 <|> namedCircleP                           -- starts with lower
 <|> bareTypeBracesP                        -- starts with '{'
 <|> unnamedCircleP
 <|> anglesCircleP                          -- starts with '<'
 <|> nullPC <$> (dummyP (bbaseP <* spaces)) -- starts with '_' or '[' or '(' or lower or "'" or upper
 <?> "circleP"

anglesCircleP :: Parser ParamComp
anglesCircleP
  = angles $ do
      PC sb t <- parens btP
      p <- monoPredicateP
      return $ PC sb (t `strengthen` MkUReft mempty p mempty)

holePC :: Parser ParamComp
holePC = do
  h <- holeP
  b <- dummyBindP
  return (PC (PcImplicit b) h)

namedCircleP :: Parser ParamComp
namedCircleP = do
  lb <- locParserP lowerIdP
  (do _ <- colon
      let b = val lb
      PC (PcExplicit b) <$> bareArgP b
    <|> do
      b <- dummyBindP
      PC (PcImplicit b) <$> dummyP (lowerIdTail (val lb))
    )

unnamedCircleP :: Parser ParamComp
unnamedCircleP = do
  lb <- locParserP dummyBindP
  let b = val lb
  t1 <- bareArgP b
  return $ PC (PcImplicit b) t1

-- ---------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType
bareTypeP = do
  PC _ v <- btP
  return v

bareTypeBracesP :: Parser ParamComp
bareTypeBracesP = do
  t <-  braces (
            (try (do
               ct <- constraintP
               return $ Right ct
                     ))
           <|>
            (try(do
                    x  <- symbolP
                    _ <- colon
                    -- NOSUBST i  <- freshIntP
                    t  <- bbaseP
                    reservedOp "|"
                    ra <- refasHoleP <* spaces
                    -- xi is a unique var based on the name in x.
                    -- su replaces any use of x in the balance of the expression with the unique val
                    -- NOSUBST let xi = intSymbol x i
                    -- NOSUBST let su v = if v == x then xi else v
                    return $ Left $ PC (PcExplicit x) $ t (Reft (x, ra)) ))
           <|> do t <- ((RHole . uTop . Reft . ("VV",)) <$> (refasHoleP <* spaces))
                  return (Left $ nullPC t)
            )
  case t of
    Left l -> return l
    Right ct -> do
      PC _sb tt <- btP
      return $ nullPC $ rrTy ct tt

bareArgP :: Symbol -> Parser BareType
bareArgP vvv
  =  refDefP vvv refasHoleP bbaseP    -- starts with '{'
 <|> holeP                            -- starts with '_'
 <|> (dummyP (bbaseP <* spaces))
 <|> parens bareTypeP                 -- starts with '('
                                      -- starts with '_', '[', '(', lower, upper
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


-- Either
--  { x : t | ra }
-- or
--  { ra }
refBindBindP :: Parser Expr
             -> Parser (Reft -> BareType)
             -> Parser BareType
refBindBindP rp kindP'
  = braces (
      ((do
              x  <- symbolP
              _ <- colon
              -- NOSUBST i  <- freshIntP
              t  <- kindP'
              reservedOp "|"
              ra <- rp <* spaces
              -- xi is a unique var based on the name in x.
              -- su replaces any use of x in the balance of the expression with the unique val
              -- NOSUBST let xi = intSymbol x i
              -- NOSUBST let su v = if v == x then xi else v
              return $ {- substa su $ NOSUBST -} t (Reft (x, ra)) ))
     <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))
     <?> "refBindBindP"
   )


refDefP :: Symbol
        -> Parser Expr
        -> Parser (Reft -> BareType)
        -> Parser BareType
refDefP vv rp kindP' = braces $ do
  x       <- optBindP vv
  -- NOSUBST i       <- freshIntP
  t       <- try (kindP' <* reservedOp "|") <|> return (RHole . uTop) <?> "refDefP"
  ra      <- (rp <* spaces)
  -- xi is a unique var based on the name in x.
  -- su replaces any use of x in the balance of the expression with the unique val
  -- NOSUBST let xi   = intSymbol x i
  -- NOSUBST let su v = if v == x then xi else v
  return   $ {- substa su $ NOSUBST -} t (Reft (x, ra))
       -- substa su . t . Reft . (x,) <$> (rp <* spaces))
      --  <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))

refP :: Parser (Reft -> BareType) -> Parser BareType
refP = refBindBindP refaP

-- "sym :" or return the devault sym
optBindP :: Symbol -> Parser Symbol
optBindP x = try bindP <|> return x

holeP :: Parser BareType
holeP    = reserved "_" >> spaces >> return (RHole $ uTop $ Reft ("VV", hole))

holeRefP :: Parser (Reft -> BareType)
holeRefP = reserved "_" >> spaces >> return (RHole . uTop)

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
 <|> liftM2 bTup (parens $ sepBy (maybeBind bareTypeP) comma) predicatesP
 <|> try parseHelper  -- starts with lower
 <|> liftM5 bCon bTyConP stratumP predicatesP (sepBy bareTyArgP blanks) mmonoPredicateP
           -- starts with "'" or upper case char
 <?> "bbaseP"
 where
   parseHelper = do
     l <- lowerIdP
     lowerIdTail l

maybeBind :: Parser a -> Parser (Maybe Symbol, a)
maybeBind p = do {bd <- maybeP' bbindP; ty <- p ; return (bd, ty)}
  where
    maybeP' p = try (Just <$> p)
             <|> return Nothing

lowerIdTail :: Symbol -> Parser (Reft -> BareType)
lowerIdTail l =
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
 <|> liftM2 bTup (parens $ sepBy (maybeBind bareTypeP) comma) predicatesP
 <|> try (liftM5 bCon bTyConP stratumP predicatesP (return []) (return mempty))
 <|> liftM3 bRVar (bTyVar <$> lowerIdP) stratumP monoPredicateP
 <?> "bbaseNoAppP"

maybeP :: ParsecT s u m a -> ParsecT s u m (Maybe a)
maybeP p = liftM Just p <|> return Nothing

bareTyArgP :: Parser BareType
bareTyArgP
  =  (RExprArg . fmap expr <$> locParserP integer)
 <|> try (braces $ RExprArg <$> locParserP exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)
 <?> "bareTyArgP"

bareAtomNoAppP :: Parser BareType
bareAtomNoAppP
  =  refP bbaseNoAppP
 <|> (dummyP (bbaseNoAppP <* spaces))
 <?> "bareAtomNoAppP"


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

--  "forall <z w> . TYPE"
-- or
--  "forall x y <z :: Nat, w :: Int> . TYPE"
bareAllP :: Parser BareType
bareAllP = do
  as <- tyVarDefsP
  vs <- angles inAngles
        <|> (return $ Right [])
  dot
  t <- bareTypeP
  case vs of
    Left ss  -> return $ foldr RAllS t ss
    Right ps -> return $ foldr RAllT (foldr RAllP t ps) (makeRTVar <$> as)
  where
    inAngles =
      (
       (try  (Right <$> sepBy  predVarDefP comma))
        <|> ((Left  <$> sepBy1 symbolP     comma))
       )

tyVarDefsP :: Parser [BTyVar]
tyVarDefsP
  = (parens $ many (bTyVar <$> tyKindVarIdP))
 <|> many (bTyVar <$> tyVarIdP)
 <?> "tyVarDefsP"

-- TODO:AZ use something from Token instead
tyVarIdP :: Parser Symbol
tyVarIdP = symbol <$> condIdP (lower <|> char '_') alphanums isNotReserved -- (isSmall . head)
  where
    alphanums = S.fromList $ ['a'..'z'] ++ ['0'..'9']

tyKindVarIdP :: Parser Symbol
tyKindVarIdP = do
   tv <- tyVarIdP
   (  (do reservedOp "::"; _ <- kindP; return tv)
    <|> return tv)

kindP :: Parser BareType
kindP = bareAtomBindP

predVarDefsP :: Parser [PVar BSort]
predVarDefsP
  =  (angles $ sepBy1 predVarDefP comma)
 <|> return []
 <?> "predVarDefP"

predVarDefP :: Parser (PVar BSort)
predVarDefP
  = bPVar <$> predVarIdP <*> dcolon <*> propositionSortP

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

propositionSortP :: Parser [(Symbol, BSort)]
propositionSortP = map (F.mapSnd toRSort) <$> propositionTypeP

propositionTypeP :: Parser [(Symbol, BareType)]
propositionTypeP = either parserFail return =<< (mkPropositionType <$> bareTypeP)

mkPropositionType :: BareType -> Either String [(Symbol, BareType)]
mkPropositionType t
  | isOk      = Right $ zip (ty_binds tRep) (ty_args tRep)
  | otherwise = Left err
  where
    isOk      = isPropBareType (ty_res tRep)
    tRep      = toRTypeRep t
    err       = "Proposition type with non-Bool output: " ++ showpp t

xyP :: Parser x -> Parser a -> Parser y -> Parser (x, y)
xyP lP sepP rP = (\x _ y -> (x, y)) <$> lP <*> (spaces >> sepP) <*> rP

dummyBindP :: Parser Symbol
dummyBindP = tempSymbol "db" <$> freshIntP

isPropBareType :: RType BTyCon t t1 -> Bool
isPropBareType  = isPrimBareType boolConName

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
    bargsP =     ( do reservedOp "\\"
                      xs <- many (parens tyBindP)
                      reservedOp  "->"
                      return xs
                 )
           <|> return []
           <?> "bargsP"
    bvsP   =     ( do reserved "forall"
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

bTup :: (PPrint r, Reftable r, Reftable (RType BTyCon BTyVar (UReft r)), Reftable (RTProp BTyCon BTyVar (UReft r)))
     => [(Maybe Symbol, RType BTyCon BTyVar (UReft r))]
     -> [RTProp BTyCon BTyVar (UReft r)]
     -> r
     -> RType BTyCon BTyVar (UReft r)
bTup [(_,t)] _ r
  | isTauto r  = t
  | otherwise  = t `strengthen` (reftUReft r)
bTup ts rs r
  | all isNothing (fst <$> ts) || length ts < 2
  = RApp (mkBTyCon $ dummyLoc tupConName) (snd <$> ts) rs (reftUReft r)
  | otherwise
  = RApp (mkBTyCon $ dummyLoc tupConName) ((top . snd) <$> ts) rs' (reftUReft r)
  where
    args       = [(fromMaybe dummySymbol x, mapReft mempty t) | (x,t) <- ts]
    makeProp i = RProp (take i args) ((snd <$> ts)!!i)
    rs'        = makeProp <$> [1..(length ts-1)]


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
  , Measure.invariants = [(Nothing, t) | Invt   t <- xs]
  , Measure.ialiases   = [t | IAlias t <- xs]
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs] ++ [d | NTDecl d <- xs]
  , Measure.newtyDecls = [d | NTDecl d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.ealiases   = [e | EAlias e <- xs]
  , Measure.embeds     = M.fromList [(c, fTyconSort tc) | Embed (c, tc) <- xs]
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
  , Measure.axeqs      = []
  }

-- | Parse a single top level liquid specification
specP :: Parser BPspec
specP
  =     (fallbackSpecP "assume"     (liftM Assm    tyBindP  ))
    <|> (fallbackSpecP "assert"     (liftM Asrt    tyBindP  ))
    <|> (fallbackSpecP "autosize"   (liftM ASize   asizeP   ))
    <|> (reserved "local"         >> liftM LAsrt   tyBindP  )

    -- TODO: These next two are synonyms, kill one
    <|> (fallbackSpecP "axiomatize" (liftM Reflect axiomP   ))
    <|> (fallbackSpecP "reflect"    (liftM Reflect axiomP   ))

    <|> (fallbackSpecP "measure"    hmeasureP)

    <|> (fallbackSpecP "define"     (liftM Define  defineP  ))
    <|> (reserved "infixl"        >> liftM BFix    infixlP  )
    <|> (reserved "infixr"        >> liftM BFix    infixrP  )
    <|> (reserved "infix"         >> liftM BFix    infixP   )
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
        >> ((reserved "variance"  >> liftM Varia  datavarianceP)
                                 <|> liftM DDecl  dataDeclP ))

    <|> (reserved "newtype"       >> liftM NTDecl dataDeclP )
    <|> (reserved "include"       >> liftM Incl   filePathP )
    <|> (fallbackSpecP "invariant"  (liftM Invt   invariantP))
    <|> (reserved "using"         >> liftM IAlias invaliasP )
    <|> (reserved "type"          >> liftM Alias  aliasP    )

    -- TODO: Next two are basically synonyms
    <|> (fallbackSpecP "predicate"  (liftM EAlias ealiasP   ))
    <|> (fallbackSpecP "expression" (liftM EAlias ealiasP   ))

    <|> (fallbackSpecP "embed"      (liftM Embed  embedP    ))
    <|> (fallbackSpecP "qualif"     (liftM Qualif (qualifierP sortP)))
    <|> (reserved "decrease"      >> liftM Decr   decreaseP )
    <|> (reserved "lazyvar"       >> liftM LVars  lazyVarP  )

    <|> (reserved "lazy"          >> liftM Lazy   lazyVarP  )

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

axiomP :: Parser LocSymbol
axiomP = locParserP binderP

hboundP :: Parser LocSymbol
hboundP = locParserP binderP

inlineP :: Parser LocSymbol
inlineP = locParserP binderP

asizeP :: Parser LocSymbol
asizeP = locParserP binderP

decreaseP :: Parser (LocSymbol, [Int])
decreaseP = F.mapSnd f <$> liftM2 (,) (locParserP binderP) (spaces >> many integer)
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
genBareTypeP = bareTypeP

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
aliasIdP = condIdP (letter <|> char '_') alphaNums (isAlpha . head)
           where
             alphaNums = S.fromList $ ['A' .. 'Z'] ++ ['a'..'z'] ++ ['0'..'9']

hmeasureP :: Parser BPspec
hmeasureP = do
  b <- locParserP binderP
  spaces
  ((do dcolon
       ty <- locParserP genBareTypeP
       whiteSpace
       eqns <- grabs $ measureDefP (rawBodyP <|> tyBodyP ty)
       return (Meas $ Measure.mkM b ty eqns))
    <|> (return (HMeas b))
    )

measureP :: Parser (Measure (Located BareType) LocSymbol)
measureP
  = do (x, ty) <- tyBindP
       whiteSpace
       eqns    <- grabs $ measureDefP (rawBodyP <|> tyBodyP ty)
       return   $ Measure.mkM x ty eqns


-- | class measure
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

-- | LHS of the thing being defined
binderP :: Parser Symbol
binderP    = pwr    <$> parens (idP bad)
         <|> symbol <$> idP badc
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

dataConP :: Parser DataCtor
dataConP = do
  x   <- locParserP dataConNameP
  spaces
  xts <- dataConFieldsP
  return $ DataCtor x xts Nothing

adtDataConP :: Parser DataCtor
adtDataConP = do
  x     <- locParserP dataConNameP
  dcolon
  tr    <- toRTypeRep <$> bareTypeP
  return $ DataCtor x (tRepFields tr) (Just $ ty_res tr)

tRepFields :: RTypeRep c tv r -> [(Symbol, RType c tv r)]
tRepFields tr = zip (ty_binds tr) (ty_args tr)

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
dataDeclP = do
  pos <- getPosition
  x   <- locUpperIdP'
  spaces
  fsize <- dataSizeP
  (dataDeclBodyP pos x fsize <|> return (emptyDecl x pos fsize))

emptyDecl :: LocSymbol -> SourcePos -> Maybe SizeFun -> DataDecl
emptyDecl x pos fsize@(Just _)
  = D (DnName x) [] [] [] [] pos fsize Nothing DataUser
emptyDecl x pos _
  = uError (ErrBadData (sourcePosSrcSpan pos) (pprint (val x)) msg)
  where
    msg = "You should specify either a default [size] or one or more fields in the data declaration"

dataDeclBodyP :: SourcePos -> LocSymbol -> Maybe SizeFun -> Parser DataDecl
dataDeclBodyP pos x fsize = do
  vanilla    <- null <$> sepBy locUpperIdP blanks
  ts         <- sepBy noWhere blanks
  ps         <- predVarDefsP
  (pTy, dcs) <- dataCtorsP
  let dn      = dataDeclName pos x vanilla dcs
  whiteSpace
  return      $ D dn ts ps [] dcs pos fsize pTy DataUser

dataDeclName :: SourcePos -> LocSymbol -> Bool -> [DataCtor] -> DataName
dataDeclName _ x True  _     = DnName x               -- vanilla data    declaration
dataDeclName _ _ False (d:_) = DnCon  (dcName d)      -- family instance declaration
dataDeclName p x _  _        = uError (ErrBadData (sourcePosSrcSpan p) (pprint (val x)) msg)
  where
    msg                  = "You should specify at least one data constructor for a family instance"


dataCtorsP :: Parser (Maybe BareType, [DataCtor])
dataCtorsP
  =  (reservedOp "="     >> ((Nothing, ) <$>                 sepBy dataConP    (reservedOp "|")))
 <|> (reserved   "where" >> ((Nothing, ) <$>                 sepBy adtDataConP (reservedOp "|")))
 <|> (                      ((,)         <$> dataPropTyP <*> sepBy adtDataConP (reservedOp "|")))

noWhere :: Parser Symbol
noWhere = try $ do
  s <- tyVarIdP
  if s == "where"
    then parserZero
    else return s

dataPropTyP :: Parser (Maybe BareType)
dataPropTyP = Just <$> between dcolon (reserved "where") bareTypeP

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
