{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Haskell.Liquid.Parse
  ( hsSpecificationP
  , specSpecificationP
  , singleSpecP
  , BPspec
  , Pspec(..)
  , parseSymbolToLogic
  , parseTest'
  )
  where

import           Control.Arrow                          (second)
import           Control.Monad
import           Control.Monad.Identity
import qualified Data.Foldable                          as F
import           Data.String
import           Data.Void
import           Prelude                                hiding (error)
import           Text.Megaparsec                        hiding (ParseError)
import           Text.Megaparsec.Char
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import           Data.Data
import qualified Data.Maybe                             as Mb -- (isNothing, fromMaybe)
import           Data.Char                              (isSpace, isAlphaNum)
import           Data.List                              (partition)
import           GHC                                    (ModuleName, mkModuleName)
import qualified Text.PrettyPrint.HughesPJ              as PJ
import           Text.PrettyPrint.HughesPJ.Compat       ((<+>))
import           Language.Fixpoint.Types                hiding (panic, SVar, DDecl, DataDecl, DataCtor (..), Error, R, Predicate)
import           Language.Haskell.Liquid.GHC.Misc       hiding (getSourcePos)
import           Language.Haskell.Liquid.Types
-- import           Language.Haskell.Liquid.Types.Errors
import qualified Language.Fixpoint.Misc                 as Misc
import qualified Language.Haskell.Liquid.Misc           as Misc
import qualified Language.Haskell.Liquid.Measure        as Measure
import           Language.Fixpoint.Parse                hiding (defineP, dataDeclP, refBindP, refP, refDefP, parseTest')

import Control.Monad.State

-- import Debug.Trace

-- * Top-level parsing API

-- | Used to parse .hs and .lhs files (via ApiAnnotations).
hsSpecificationP :: ModuleName
                 -> [(SourcePos, String)]
                 -> [BPspec]
                 -> Either [Error] (ModName, Measure.BareSpec)
hsSpecificationP modName specComments specQuotes =
  case go ([], []) initPStateWithList specComments of
    ([], specs) ->
      Right $ mkSpec (ModName SrcImport modName) (specs ++ specQuotes)
    (errors, _) ->
      Left errors
  where
    go :: ([Error], [BPspec])   -- accumulated errors and parsed specs (in reverse order)
       -> PState                -- parser state (primarily infix operator priorities)
       -> [(SourcePos, String)] -- remaining unparsed spec comments
       -> ([Error], [BPspec])   -- final errors and parsed specs
    go (errors, specs) _ []
      = (reverse errors, reverse specs)
    go (errors, specs) pstate ((pos, specComment):xs)
      = -- 'specP' parses a single spec comment, i.e., a single LH directive
        -- we allow a "block" of specs now
        case parseWithError pstate (block specP) pos specComment of
          Left err'       -> go (parseErrorBundleToErrors err' ++ errors, specs) pstate xs
          Right (st,spec) -> go (errors,spec ++ specs) st xs

initPStateWithList :: PState
initPStateWithList
  = (initPState composeFun)
               { empList    = Just (EVar ("GHC.Types.[]" :: Symbol))
               , singList   = Just (\e -> EApp (EApp (EVar ("GHC.Types.:"  :: Symbol)) e) (EVar ("GHC.Types.[]" :: Symbol)))
               }
  where composeFun = Just $ EVar functionComposisionSymbol

-- | Used to parse .spec files.
specSpecificationP  :: SourceName -> String -> Either (ParseErrorBundle String Void) (ModName, Measure.BareSpec)
--------------------------------------------------------------------------
specSpecificationP f s = mapRight snd $  parseWithError initPStateWithList (specificationP <* eof) (initialPos f) s

-- | Parses a module spec.
--
-- A module spec is a module only containing spec constructs for Liquid Haskell,
-- and no "normal" Haskell code.
--
specificationP :: Parser (ModName, Measure.BareSpec)
specificationP = do
  reserved "module"
  reserved "spec"
  name   <- symbolP
  reserved "where"
  xs     <- block specP
  return $ mkSpec (ModName SpecImport $ mkModuleName $ symbolString name) xs

-- debugP = grabs (specP <* whiteSpace)

-------------------------------------------------------------------------------
singleSpecP :: SourcePos -> String -> Either (ParseErrorBundle String Void) BPspec
-------------------------------------------------------------------------------
singleSpecP pos = mapRight snd . parseWithError initPStateWithList specP pos

mapRight :: (a -> b) -> Either l a -> Either l b
mapRight f (Right x) = Right $ f x
mapRight _ (Left x)  = Left x

-- Note [PState in parser]
--
-- In the original parsec parser, 'PState' did not contain the supply counter.
-- The supply counter was separately initialised to 0 on every parser call, e.g.
-- in 'parseWithError'.
--
-- Now, the supply counter is a part of 'PState' and would normally be threaded
-- between subsequent parsing calls within s single file, as for example issued
-- by 'hsSpecificationP'. This threading seems correct to me (Andres). It sounds
-- like we would want to have the same behaviour of the counter whether we are
-- parsing several separate specs or a single combined spec.
--
-- However, I am getting one test failure due to the threading change, namely
-- Tests.Micro.class-laws-pos.FreeVar.hs, because in a unification call two
-- variables occurring in a binding position do not match. This seems like a bug
-- in the unifier. I'm nevertheless reproucing the "old" supply behaviour for
-- now. This should be revisited later. TODO.

-- | Entry point for parsers.
--
-- Resets the supply in the given state to 0, see Note [PState in parser].
-- Also resets the layout stack, as different spec comments in a file can
-- start at different columns, and we do not want layout info to carry
-- across different such comments.
--
parseWithError :: forall a. PState -> Parser a -> SourcePos -> String -> Either (ParseErrorBundle String Void) (PState, a)
parseWithError pstate parser p s =
  case snd (runIdentity (runParserT' (runStateT doParse pstate{supply = 0, layoutStack = Empty}) internalParserState)) of
    Left peb -> Left peb
    Right (r, st) -> Right (st, r)
  where
    doParse :: Parser a
    doParse = spaces *> parser <* eof
    internalParserState =
      State
        { stateInput = s
        , stateOffset = 0
        , statePosState =
          PosState
            { pstateInput = s
            , pstateOffset = 0
            , pstateSourcePos = p
            , pstateTabWidth = defaultTabWidth
            , pstateLinePrefix = ""
            }
        , stateParseErrors = []
        }

-- | Function to test parsers interactively.
parseTest' :: Show a => Parser a -> String -> IO ()
parseTest' parser input =
  parseTest (evalStateT parser initPStateWithList) input

parseErrorBundleToErrors :: ParseErrorBundle String Void -> [Error]
parseErrorBundleToErrors (ParseErrorBundle errors posState) =
  let
    (es, _) = attachSourcePos errorOffset errors posState
  in
    parseErrorError <$> F.toList es

---------------------------------------------------------------------------
parseErrorError     :: (ParseError, SourcePos) -> Error
---------------------------------------------------------------------------
parseErrorError (e, pos) = ErrParse sp msg e
  where
    sp              = sourcePosSrcSpan pos
    msg             = "Error Parsing Specification from:" <+> PJ.text (sourceName pos)

--------------------------------------------------------------------------------
-- Parse to Logic  -------------------------------------------------------------
--------------------------------------------------------------------------------

parseSymbolToLogic :: SourceName -> String -> Either (ParseErrorBundle String Void) LogicMap
parseSymbolToLogic f = mapRight snd . parseWithError initPStateWithList toLogicP (initialPos f)

toLogicP :: Parser LogicMap
toLogicP
  = toLogicMap <$> many toLogicOneP

toLogicOneP :: Parser  (LocSymbol, [Symbol], Expr)
toLogicOneP
  = do reserved "define"
       (x:xs) <- some locSymbolP
       reservedOp "="
       e      <- exprP <|> predP
       return (x, val <$> xs, e)


defineP :: Parser (LocSymbol, Symbol)
defineP =
  (,) <$> locBinderP <* reservedOp "=" <*> binderP

--------------------------------------------------------------------------------
-- | BareTypes -----------------------------------------------------------------
--------------------------------------------------------------------------------

{- | [NOTE:BARETYPE-PARSE] Fundamentally, a type is of the form

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
    parseFun c@(PC sb t1) sy  =
      (do
            reservedOp "->"
            PC _ t2 <- btP
            return (PC sb (rFun sy t1 t2)))
        <|>
         (do
            reservedOp "=>"
            PC _ t2 <- btP
            -- TODO:AZ return an error if s == PcExplicit
            return $ PC sb $ foldr (rFun dummySymbol) t2 (getClasses t1))
         <|>
          (do
             b <- locInfixSymbolP
             PC _ t2 <- btP
             return $ PC sb $ RApp (mkBTyCon b) [t1,t2] [] mempty)
         <|> return c


compP :: Parser ParamComp
compP = circleP <|> parens btP <?> "compP"

circleP :: Parser ParamComp
circleP
  =  nullPC <$> (reserved "forall" >> bareAllP)
 <|> holePC                                 -- starts with '_'
 <|> namedCircleP                           -- starts with lower
 <|> bareTypeBracesP                        -- starts with '{'
 <|> unnamedCircleP
 <|> anglesCircleP                          -- starts with '<'
 <|> nullPC <$> dummyP bbaseP               -- starts with '_' or '[' or '(' or lower or "'" or upper
 <?> "circleP"

anglesCircleP :: Parser ParamComp
anglesCircleP
  = angles $ do
      PC sb t <- parens btP
      p       <- monoPredicateP
      return   $ PC sb (t `strengthen` MkUReft mempty p)

holePC :: Parser ParamComp
holePC = do
  h <- holeP
  b <- dummyBindP
  return (PC (PcImplicit b) h)

namedCircleP :: Parser ParamComp
namedCircleP = do
  lb <- locLowerIdP
  do _ <- reservedOp ":"
     let b = val lb
     PC (PcExplicit b) <$> bareArgP b
    <|> do
      b <- dummyBindP
      PC (PcImplicit b) <$> dummyP (lowerIdTail (val lb))

unnamedCircleP :: Parser ParamComp
unnamedCircleP = do
  lb <- located dummyBindP
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
  t <-  try (braces (
            try (Right <$> constraintP)
           <|>
            (do
                    x  <- symbolP
                    _ <- reservedOp ":"
                    -- NOSUBST i  <- freshIntP
                    t  <- bbaseP
                    reservedOp "|"
                    ra <- refasHoleP
                    -- xi is a unique var based on the name in x.
                    -- su replaces any use of x in the balance of the expression with the unique val
                    -- NOSUBST let xi = intSymbol x i
                    -- NOSUBST let su v = if v == x then xi else v
                    return $ Left $ PC (PcExplicit x) $ t (Reft (x, ra)) )
            )) <|> try (helper holeOrPredsP) <|> helper predP
  case t of
    Left l -> return l
    Right ct -> do
      PC _sb tt <- btP
      return $ nullPC $ rrTy ct tt
  where
    holeOrPredsP
      = (reserved "_" >> return hole)
     <|> try (pAnd <$> brackets (sepBy predP semi))
    helper p = braces $ do
      t <- RHole . uTop . Reft . ("VV",) <$> p
      return (Left $ nullPC t)


bareArgP :: Symbol -> Parser BareType
bareArgP vvv
  =  refDefP vvv refasHoleP bbaseP    -- starts with '{'
 <|> holeP                            -- starts with '_'
 <|> dummyP bbaseP
 <|> parens bareTypeP                 -- starts with '('
                                      -- starts with '_', '[', '(', lower, upper
 <?> "bareArgP"

bareAtomP :: (Parser Expr -> Parser (Reft -> BareType) -> Parser BareType)
          -> Parser BareType
bareAtomP ref
  =  ref refasHoleP bbaseP
 <|> holeP
 <|> dummyP bbaseP
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
      (do
              x  <- symbolP
              _ <- reservedOp ":"
              -- NOSUBST i  <- freshIntP
              t  <- kindP'
              reservedOp "|"
              ra <- rp
              -- xi is a unique var based on the name in x.
              -- su replaces any use of x in the balance of the expression with the unique val
              -- NOSUBST let xi = intSymbol x i
              -- NOSUBST let su v = if v == x then xi else v
              return $ {- substa su $ NOSUBST -} t (Reft (x, ra)) )
     <|> (RHole . uTop . Reft . ("VV",) <$> rp)
     <?> "refBindBindP"
   )


refDefP :: Symbol
        -> Parser Expr
        -> Parser (Reft -> BareType)
        -> Parser BareType
refDefP sy rp kindP' = braces $ do
  x       <- optBindP sy
  -- NOSUBST i       <- freshIntP
  t       <- try (kindP' <* reservedOp "|") <|> return (RHole . uTop) <?> "refDefP"
  ra      <- rp
  -- xi is a unique var based on the name in x.
  -- su replaces any use of x in the balance of the expression with the unique val
  -- NOSUBST let xi   = intSymbol x i
  -- NOSUBST let su v = if v == x then xi else v
  return   $ {- substa su $ NOSUBST -} t (Reft (x, ra))
       -- substa su . t . Reft . (x,) <$> (rp <* spaces))
      --  <|> ((RHole . uTop . Reft . ("VV",)) <$> (rp <* spaces))

refP :: Parser (Reft -> BareType) -> Parser BareType
refP = refBindBindP refaP

relrefaP :: Parser RelExpr
relrefaP =
  try (ERUnChecked <$> refaP <* reserved ":=>" <*> relrefaP)
    <|> try (ERChecked <$> refaP <* reserved "!=>" <*> relrefaP)
    <|> ERBasic <$> refaP

-- "sym :" or return the devault sym
optBindP :: Symbol -> Parser Symbol
optBindP x = try bindP <|> return x

holeP :: Parser BareType
holeP    = reserved "_" >> return (RHole $ uTop $ Reft ("VV", hole))

holeRefP :: Parser (Reft -> BareType)
holeRefP = reserved "_" >> return (RHole . uTop)

-- NOPROP refasHoleP :: Parser Expr
-- NOPROP refasHoleP  = try refaP
-- NOPROP          <|> (reserved "_" >> return hole)

refasHoleP :: Parser Expr
refasHoleP
  =  (reserved "_" >> return hole)
 <|> refaP
 <?> "refasHoleP"

bbaseP :: Parser (Reft -> BareType)
bbaseP
  =  holeRefP  -- Starts with '_'
 <|> liftM2 bLst (brackets (optional bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy (maybeBind bareTypeP) comma) predicatesP
 <|> try parseHelper  -- starts with lower
 <|> liftM4 bCon bTyConP predicatesP (many bareTyArgP) mmonoPredicateP
           -- starts with "'" or upper case char
 <?> "bbaseP"
 where
   parseHelper = do
     l <- lowerIdP
     lowerIdTail l

maybeBind :: Parser a -> Parser (Maybe Symbol, a)
maybeBind parser = do {bd <- maybeP' bbindP; ty <- parser ; return (bd, ty)}
  where
    maybeP' p = try (Just <$> p)
             <|> return Nothing

lowerIdTail :: Symbol -> Parser (Reft -> BareType)
lowerIdTail l =
          fmap (bAppTy (bTyVar l)) (some bareTyArgP)
      <|> fmap (bRVar (bTyVar l)) monoPredicateP

bTyConP :: Parser BTyCon
bTyConP
  =  (reservedOp "'" >> (mkPromotedBTyCon <$> locUpperIdP))
 <|> mkBTyCon <$> locUpperIdP
 <|> (reserved "*" >> return (mkBTyCon (dummyLoc $ symbol ("*" :: String))))
 <?> "bTyConP"

mkPromotedBTyCon :: LocSymbol -> BTyCon
mkPromotedBTyCon x = BTyCon x False True -- (consSym '\'' <$> x) False True

classBTyConP :: Parser BTyCon
classBTyConP = mkClassBTyCon <$> locUpperIdP

mkClassBTyCon :: LocSymbol -> BTyCon
mkClassBTyCon x = BTyCon x True False

bbaseNoAppP :: Parser (Reft -> BareType)
bbaseNoAppP
  =  holeRefP
 <|> liftM2 bLst (brackets (optional bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy (maybeBind bareTypeP) comma) predicatesP
 <|> try (liftM4 bCon bTyConP predicatesP (return []) (return mempty))
 <|> liftM2 bRVar (bTyVar <$> lowerIdP) monoPredicateP
 <?> "bbaseNoAppP"

bareTyArgP :: Parser BareType
bareTyArgP
  =  (RExprArg . fmap expr <$> locNatural)
 <|> try (braces $ RExprArg <$> located exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)
 <?> "bareTyArgP"

bareAtomNoAppP :: Parser BareType
bareAtomNoAppP
  =  refP bbaseNoAppP
 <|> dummyP bbaseNoAppP
 <?> "bareAtomNoAppP"


constraintP :: Parser BareType
constraintP
  = do xts <- constraintEnvP
       t1  <- bareTypeP
       reservedOp "<:"
       fromRTypeRep . RTypeRep [] []
                               ((val . fst <$> xts) ++ [dummySymbol])
                               (replicate (length xts + 1) defRFInfo)
                               (replicate (length xts + 1) mempty)
                               ((snd <$> xts) ++ [t1]) <$> bareTypeP

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
  sp <- getSourcePos
  as  <- tyVarDefsP
  ps  <- angles inAngles
        <|> return []
  _ <- dot
  t <- bareTypeP
  return $ foldr rAllT (foldr (rAllP sp) t ps) (makeRTVar <$> as)
  where
    rAllT a t = RAllT a t mempty
    inAngles  = try  (sepBy  predVarDefP comma)

-- See #1907 for why we have to alpha-rename pvar binders
rAllP :: SourcePos -> PVar BSort -> BareType -> BareType
rAllP sp p t = RAllP p' ({- F.tracepp "rAllP" $ -} substPVar p p' t)
  where
    p'  = p { pname = pn' }
    pn' = pname p `intSymbol` lin `intSymbol` col
    lin = unPos (sourceLine sp)
    col = unPos (sourceColumn  sp)

tyVarDefsP :: Parser [BTyVar]
tyVarDefsP
  = parens (many (bTyVar <$> tyKindVarIdP))
 <|> many (bTyVar <$> tyVarIdP)
 <?> "tyVarDefsP"

tyKindVarIdP :: Parser Symbol
tyKindVarIdP = do
   tv <- tyVarIdP
   do reservedOp "::"; _ <- kindP; return tv <|> return tv

kindP :: Parser BareType
kindP = bareAtomBindP

predVarDefsP :: Parser [PVar BSort]
predVarDefsP
  =  angles (sepBy1 predVarDefP comma)
 <|> return []
 <?> "predVarDefP"

predVarDefP :: Parser (PVar BSort)
predVarDefP
  = bPVar <$> predVarIdP <*> reservedOp "::" <*> propositionSortP

predVarIdP :: Parser Symbol
predVarIdP
  = symbol <$> tyVarIdP

bPVar :: Symbol -> t -> [(Symbol, t1)] -> PVar t1
bPVar p _ xts  = PV p (PVProp τ) dummySymbol τxs
  where
    (_, τ) = safeLast "bPVar last" xts
    τxs    = [ (τ', x, EVar x) | (x, τ') <- init xts ]
    safeLast _ xs@(_:_) = last xs
    safeLast msg _      = panic Nothing $ "safeLast with empty list " ++ msg

propositionSortP :: Parser [(Symbol, BSort)]
propositionSortP = map (Misc.mapSnd toRSort) <$> propositionTypeP

propositionTypeP :: Parser [(Symbol, BareType)]
propositionTypeP = either fail return . mkPropositionType =<< bareTypeP

mkPropositionType :: BareType -> Either String [(Symbol, BareType)]
mkPropositionType t
  | isOk      = Right $ zip (ty_binds tRep) (ty_args tRep)
  | otherwise = Left mkErr
  where
    isOk      = isPropBareType (ty_res tRep)
    tRep      = toRTypeRep t
    mkErr     = "Proposition type with non-Bool output: " ++ showpp t

xyP :: Parser x -> Parser a -> Parser y -> Parser (x, y)
xyP lP sepP rP =
  (,) <$> lP <* sepP <*> rP

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
       ss <- many symbolP
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
   =  angles (sepBy1 predicate1P comma)
  <|> return []
  <?> "predicatesP"

predicate1P :: (IsString tv, Monoid r)
            => Parser (Ref (RType c tv r) BareType)
predicate1P
   =  try (RProp <$> symsP <*> refP bbaseP)
  <|> (rPropP [] . predUReft <$> monoPredicate1P)
  <|> braces (bRProp <$> symsP' <*> refaP)
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

predVarUseP :: Parser (PVar String)
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
  name   <- locUpperIdP
  reservedOp "="
  vs      <- bvsP
  params' <- many (parens tyBindP)
  args    <- bargsP
  Bound name vs params' args <$> predP
 where
    bargsP =     ( do reservedOp "\\"
                      xs <- many (parens tyBindP)
                      reservedOp  "->"
                      return xs
                 )
           <|> return []
           <?> "bargsP"
    bvsP   =     ( do reserved "forall"
                      xs <- many (fmap bTyVar <$> locSymbolP)
                      reservedOp  "."
                      return (fmap (`RVar` mempty) <$> xs)
                 )
           <|> return []


infixGenP :: Assoc -> Parser ()
infixGenP assoc = do
   p <- maybeDigit
   s <- infixIdP -- TODO: Andres: infixIdP was defined as many (satisfy (`notElem` [' ', '.'])) which does not make sense at all
   -- Andres: going via Symbol seems unnecessary and wasteful here
   addOperatorP (FInfix p (symbolString s) Nothing assoc)

infixP :: Parser ()
infixP = infixGenP AssocLeft

infixlP :: Parser ()
infixlP = infixGenP AssocLeft

infixrP :: Parser ()
infixrP = infixGenP AssocRight

maybeDigit :: Parser (Maybe Int)
maybeDigit
  = optional (lexeme (read . pure <$> digitChar))

------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRProp :: [((Symbol, τ), Symbol)]
       -> Expr -> Ref τ (RType c BTyVar (UReft Reft))
bRProp []    _    = panic Nothing "Parse.bRProp empty list"
bRProp syms' epr  = RProp ss $ bRVar (BTV dummyName) mempty r
  where
    (ss, (v, _))  = (init symsf, last symsf)
    symsf         = [(y, s) | ((_, s), y) <- syms']
    su            = mkSubst [(x, EVar y) | ((x, _), y) <- syms']
    r             = su `subst` Reft (v, epr)

bRVar :: tv -> Predicate -> r -> RType c tv (UReft r)
bRVar α p r = RVar α (MkUReft r p)

bLst :: Maybe (RType BTyCon tv (UReft r))
     -> [RTProp BTyCon tv (UReft r)]
     -> r
     -> RType BTyCon tv (UReft r)
bLst (Just t) rs r = RApp (mkBTyCon $ dummyLoc listConName) [t] rs (reftUReft r)
bLst Nothing  rs r = RApp (mkBTyCon $ dummyLoc listConName) []  rs (reftUReft r)

bTup :: (PPrint r, Reftable r, Reftable (RType BTyCon BTyVar (UReft r)), Reftable (RTProp BTyCon BTyVar (UReft r)))
     => [(Maybe Symbol, RType BTyCon BTyVar (UReft r))]
     -> [RTProp BTyCon BTyVar (UReft r)]
     -> r
     -> RType BTyCon BTyVar (UReft r)
bTup [(_,t)] _ r
  | isTauto r  = t
  | otherwise  = t `strengthen` reftUReft r
bTup ts rs r
  | all Mb.isNothing (fst <$> ts) || length ts < 2
  = RApp (mkBTyCon $ dummyLoc tupConName) (snd <$> ts) rs (reftUReft r)
  | otherwise
  = RApp (mkBTyCon $ dummyLoc tupConName) (top . snd <$> ts) rs' (reftUReft r)
  where
    args       = [(Mb.fromMaybe dummySymbol x, mapReft mempty t) | (x,t) <- ts]
    makeProp i = RProp (take i args) ((snd <$> ts)!!i)
    rs'        = makeProp <$> [1..(length ts-1)]


-- Temporarily restore this hack benchmarks/esop2013-submission/Array.hs fails
-- w/o it
-- TODO RApp Int [] [p] true should be syntactically different than RApp Int [] [] p
-- bCon b s [RProp _ (RHole r1)] [] _ r = RApp b [] [] $ r1 `meet` (MkUReft r mempty s)
bCon :: c
     -> [RTProp c tv (UReft r)]
     -> [RType c tv (UReft r)]
     -> Predicate
     -> r
     -> RType c tv (UReft r)
bCon b rs ts p r = RApp b ts rs $ MkUReft r p

bAppTy :: (Foldable t, PPrint r, Reftable r)
       => tv -> t (RType c tv (UReft r)) -> r -> RType c tv (UReft r)
bAppTy v ts r  = ts' `strengthen` reftUReft r
  where
    ts'        = foldl' (\a b -> RAppTy a b mempty) (RVar v mempty) ts

reftUReft :: r -> UReft r
reftUReft r    = MkUReft r mempty

predUReft :: Monoid r => Predicate -> UReft r
predUReft p    = MkUReft dummyReft p

dummyReft :: Monoid a => a
dummyReft      = mempty

dummyTyId :: IsString a => a
dummyTyId      = ""

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

type BPspec = Pspec LocBareType LocSymbol

-- | The AST for a single parsed spec.
data Pspec ty ctor
  = Meas    (Measure ty ctor)                             -- ^ 'measure' definition
  | Assm    (LocSymbol, ty)                               -- ^ 'assume' signature (unchecked)
  | AssmReflect (LocSymbol, LocSymbol)                    -- ^ 'assume reflects' signature (unchecked)
  | Asrt    (LocSymbol, ty)                               -- ^ 'assert' signature (checked)
  | LAsrt   (LocSymbol, ty)                               -- ^ 'local' assertion -- TODO RJ: what is this
  | Asrts   ([LocSymbol], (ty, Maybe [Located Expr]))     -- ^ TODO RJ: what is this
  | Impt    Symbol                                        -- ^ 'import' a specification module
  | DDecl   DataDecl                                      -- ^ refined 'data'    declaration
  | NTDecl  DataDecl                                      -- ^ refined 'newtype' declaration
  | Relational (LocSymbol, LocSymbol, ty, ty, RelExpr, RelExpr) -- ^ relational signature
  | AssmRel (LocSymbol, LocSymbol, ty, ty, RelExpr, RelExpr) -- ^ 'assume' relational signature
  | Class   (RClass ty)                                   -- ^ refined 'class' definition
  | CLaws   (RClass ty)                                   -- ^ 'class laws' definition
  | ILaws   (RILaws ty)
  | RInst   (RInstance ty)                                -- ^ refined 'instance' definition
  | Incl    FilePath                                      -- ^ 'include' a path -- TODO: deprecate
  | Invt    ty                                            -- ^ 'invariant' specification
  | Using  (ty, ty)                                       -- ^ 'using' declaration (for local invariants on a type)
  | Alias   (Located (RTAlias Symbol BareType))           -- ^ 'type' alias declaration
  | EAlias  (Located (RTAlias Symbol Expr))               -- ^ 'predicate' alias declaration
  | Embed   (LocSymbol, FTycon, TCArgs)                   -- ^ 'embed' declaration
  | Qualif  Qualifier                                     -- ^ 'qualif' definition
  | LVars   LocSymbol                                     -- ^ 'lazyvar' annotation, defer checks to *use* sites
  | Lazy    LocSymbol                                     -- ^ 'lazy' annotation, skip termination check on binder
  | Fail    LocSymbol                                     -- ^ 'fail' annotation, the binder should be unsafe
  | Rewrite LocSymbol                                     -- ^ 'rewrite' annotation, the binder generates a rewrite rule
  | Rewritewith (LocSymbol, [LocSymbol])                  -- ^ 'rewritewith' annotation, the first binder is using the rewrite rules of the second list,
  | Insts   (LocSymbol, Maybe Int)                        -- ^ 'auto-inst' or 'ple' annotation; use ple locally on binder
  | HMeas   LocSymbol                                     -- ^ 'measure' annotation; lift Haskell binder as measure
  | Reflect LocSymbol                                     -- ^ 'reflect' annotation; reflect Haskell binder as function in logic
  | OpaqueReflect LocSymbol                               -- ^ 'opaque-reflect' annotation
  | Inline  LocSymbol                                     -- ^ 'inline' annotation;  inline (non-recursive) binder as an alias
  | Ignore  LocSymbol                                     -- ^ 'ignore' annotation; skip all checks inside this binder
  | ASize   LocSymbol                                     -- ^ 'autosize' annotation; automatically generate size metric for this type
  | HBound  LocSymbol                                     -- ^ 'bound' annotation; lift Haskell binder as an abstract-refinement "bound"
  | PBound  (Bound ty Expr)                               -- ^ 'bound' definition
  | Pragma  (Located String)                              -- ^ 'LIQUID' pragma, used to save configuration options in source files
  | CMeas   (Measure ty ())                               -- ^ 'class measure' definition
  | IMeas   (Measure ty ctor)                             -- ^ 'instance measure' definition
  | Varia   (LocSymbol, [Variance])                       -- ^ 'variance' annotations, marking type constructor params as co-, contra-, or in-variant
  | DSize   ([ty], LocSymbol)                             -- ^ 'data size' annotations, generating fancy termination metric
  | BFix    ()                                            -- ^ fixity annotation
  | Define  (LocSymbol, Symbol)                           -- ^ 'define' annotation for specifying aliases c.f. `include-CoreToLogic.lg`
  deriving (Data, Show, Typeable)

instance (PPrint ty, PPrint ctor) => PPrint (Pspec ty ctor) where
  pprintTidy = ppPspec

splice :: PJ.Doc -> [PJ.Doc] -> PJ.Doc
splice sep = PJ.hcat . PJ.punctuate sep

ppAsserts :: (PPrint t) => Tidy -> [LocSymbol] -> t -> Maybe [Located Expr] -> PJ.Doc
ppAsserts k lxs t mles
  = PJ.hcat [ splice ", " (pprintTidy k <$> (val <$> lxs))
            , " :: "
            , pprintTidy k t
            , ppLes mles
            ]
  where
    ppLes Nothing    = ""
    ppLes (Just les) = "/" <+> pprintTidy k (val <$> les)

ppPspec :: (PPrint t, PPrint c) => Tidy -> Pspec t c -> PJ.Doc
ppPspec k (Meas m)
  = "measure" <+> pprintTidy k m
ppPspec k (Assm (lx, t))
  = "assume"  <+> pprintTidy k (val lx) <+> "::" <+> pprintTidy k t
ppPspec k (AssmReflect (lx, ly))
  = "assume reflect"  <+> pprintTidy k (val lx) <+> "as" <+> pprintTidy k (val ly)
ppPspec k (Asrt (lx, t))
  = "assert"  <+> pprintTidy k (val lx) <+> "::" <+> pprintTidy k t
ppPspec k (LAsrt (lx, t))
  = "local assert"  <+> pprintTidy k (val lx) <+> "::" <+> pprintTidy k t
ppPspec k (Asrts (lxs, (t, les)))
  = ppAsserts k lxs t les
ppPspec k (Impt  x)
  = "import" <+> pprintTidy k x
ppPspec k (DDecl d)
  = pprintTidy k d
ppPspec k (NTDecl d)
  = "newtype" <+> pprintTidy k d
ppPspec _ (Incl f)
  = "include" <+> "<" PJ.<> PJ.text f PJ.<> ">"
ppPspec k (Invt t)
  = "invariant" <+> pprintTidy k t
ppPspec k (Using (t1, t2))
  = "using" <+> pprintTidy k t1 <+> "as" <+> pprintTidy k t2
ppPspec k (Alias   (Loc _ _ rta))
  = "type" <+> pprintTidy k rta
ppPspec k (EAlias  (Loc _ _ rte))
  = "predicate" <+> pprintTidy k rte
ppPspec k (Embed   (lx, tc, NoArgs))
  = "embed" <+> pprintTidy k (val lx)         <+> "as" <+> pprintTidy k tc
ppPspec k (Embed   (lx, tc, WithArgs))
  = "embed" <+> pprintTidy k (val lx) <+> "*" <+> "as" <+> pprintTidy k tc
ppPspec k (Qualif  q)
  = pprintTidy k q
ppPspec k (LVars   lx)
  = "lazyvar" <+> pprintTidy k (val lx)
ppPspec k (Lazy   lx)
  = "lazy" <+> pprintTidy k (val lx)
ppPspec k (Rewrite   lx)
  = "rewrite" <+> pprintTidy k (val lx)
ppPspec k (Rewritewith (lx, lxs))
  = "rewriteWith" <+> pprintTidy k (val lx) <+> PJ.hsep (map go lxs)
  where
    go s = pprintTidy k $ val s
ppPspec k (Fail   lx)
  = "fail" <+> pprintTidy k (val lx)
ppPspec k (Insts   (lx, mbN))
  = "automatic-instances" <+> pprintTidy k (val lx) <+> maybe "" (("with" <+>) . pprintTidy k) mbN
ppPspec k (HMeas   lx)
  = "measure" <+> pprintTidy k (val lx)
ppPspec k (Reflect lx)
  = "reflect" <+> pprintTidy k (val lx)
ppPspec k (OpaqueReflect lx)
  = "opaque-reflect" <+> pprintTidy k (val lx)
ppPspec k (Inline  lx)
  = "inline" <+> pprintTidy k (val lx)
ppPspec k (Ignore  lx)
  = "ignore" <+> pprintTidy k (val lx)
ppPspec k (HBound  lx)
  = "bound" <+> pprintTidy k (val lx)
ppPspec k (ASize   lx)
  = "autosize" <+> pprintTidy k (val lx)
ppPspec k (PBound  bnd)
  = pprintTidy k bnd
ppPspec _ (Pragma  (Loc _ _ s))
  = "LIQUID" <+> PJ.text s
ppPspec k (CMeas   m)
  = "class measure" <+> pprintTidy k m
ppPspec k (IMeas   m)
  = "instance  measure" <+> pprintTidy k m
ppPspec k (Class   cls)
  = pprintTidy k cls
ppPspec k (CLaws  cls)
  = pprintTidy k cls
ppPspec k (RInst   inst)
  = pprintTidy k inst
ppPspec k (Varia   (lx, vs))
  = "data variance" <+> pprintTidy k (val lx) <+> splice " " (pprintTidy k <$> vs)
ppPspec k (DSize   (ds, ss))
  = "data size" <+> splice " " (pprintTidy k <$> ds) <+> pprintTidy k (val ss)
ppPspec _ (BFix    _)           --
  = "fixity"
ppPspec k (Define  (lx, y))
  = "define" <+> pprintTidy k (val lx) <+> "=" <+> pprintTidy k y
ppPspec _ ILaws{}
  = "TBD-INSTANCE-LAWS"
ppPspec k (Relational (lxl, lxr, tl, tr, q, p))
  = "relational"
        <+> pprintTidy k (val lxl) <+> "::" <+> pprintTidy k tl <+> "~"
        <+> pprintTidy k (val lxr) <+> "::" <+> pprintTidy k tr <+> "|"
        <+> pprintTidy k q <+> "=>" <+> pprintTidy k p
ppPspec k (AssmRel (lxl, lxr, tl, tr, q, p))
  = "assume relational"
        <+> pprintTidy k (val lxl) <+> "::" <+> pprintTidy k tl <+> "~"
        <+> pprintTidy k (val lxr) <+> "::" <+> pprintTidy k tr <+> "|"
        <+> pprintTidy k q <+> "=>" <+> pprintTidy k p


-- | For debugging
{-instance Show (Pspec a b) where
  show (Meas   _) = "Meas"
  show (Assm   _) = "Assm"
  show (Asrt   _) = "Asrt"
  show (LAsrt  _) = "LAsrt"
  show (Asrts  _) = "Asrts"
  show (Impt   _) = "Impt"
  shcl  _) = "DDecl"
  show (NTDecl _) = "NTDecl"
  show (Incl   _) = "Incl"
  show (Invt   _) = "Invt"
  show (Using _) = "Using"
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

qualifySpec :: Symbol -> Spec ty bndr -> Spec ty bndr
qualifySpec name sp = sp { sigs      = [ (tx x, t)  | (x, t)  <- sigs sp]
                         -- , asmSigs   = [ (tx x, t)  | (x, t)  <- asmSigs sp]
                         }
  where
    tx :: Located Symbol -> Located Symbol
    tx = fmap (qualifySymbol name)

-- | Turns a list of parsed specifications into a "bare spec".
--
-- This is primarily a rearrangement, as the bare spec is a record containing
-- different kinds of spec directives in different positions, whereas the input
-- list is a mixed list.
--
-- In addition, the sigs of the spec (these are asserted/checked LH type
-- signatues) are being qualified, i.e., the binding occurrences are prefixed
-- with the module name.
--
-- Andres: It is unfortunately totally unclear to me what the justification
-- for the qualification is, and in particular, why it is being done for
-- the asserted signatures only. My trust is not exactly improved by the
-- commented out line in 'qualifySpec'.
--
mkSpec :: ModName -> [BPspec] -> (ModName, Measure.Spec LocBareType LocSymbol)
mkSpec name xs         = (name,) $ qualifySpec (symbol name) Measure.Spec
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.asmSigs    = [a | Assm   a <- xs]
  , Measure.asmReflectSigs = [(l, r) | AssmReflect (l, r) <- xs]
  , Measure.sigs       = [a | Asrt   a <- xs]
                      ++ [(y, t) | Asrts (ys, (t, _)) <- xs, y <- ys]
  , Measure.localSigs  = []
  , Measure.reflSigs   = []
  , Measure.impSigs    = []
  , Measure.expSigs    = []
  , Measure.invariants = [(Nothing, t) | Invt   t <- xs]
  , Measure.ialiases   = [t | Using t <- xs]
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs] ++ [d | NTDecl d <- xs]
  , Measure.newtyDecls = [d | NTDecl d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.ealiases   = [e | EAlias e <- xs]
  , Measure.embeds     = tceFromList [(c, (fTyconSort tc, a)) | Embed (c, tc, a) <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.lvars      = S.fromList [d | LVars d  <- xs]
  , Measure.autois     = M.fromList [s | Insts s <- xs]
  , Measure.pragmas    = [s | Pragma s <- xs]
  , Measure.cmeasures  = [m | CMeas  m <- xs]
  , Measure.imeasures  = [m | IMeas  m <- xs]
  , Measure.omeasures  = []
  , Measure.classes    = [c | Class  c <- xs]
  , Measure.relational = [r | Relational r <- xs]
  , Measure.asmRel     = [r | AssmRel r <- xs]
  , Measure.claws      = [c | CLaws  c <- xs]
  , Measure.dvariance  = [v | Varia  v <- xs]
  , Measure.dsize      = [v | DSize  v <- xs]
  , Measure.rinstance  = [i | RInst  i <- xs]
  , Measure.ilaws      = [i | ILaws  i <- xs]
  , Measure.termexprs  = [(y, es) | Asrts (ys, (_, Just es)) <- xs, y <- ys]
  , Measure.lazy       = S.fromList [s | Lazy   s <- xs]
  , Measure.fails      = S.fromList [s | Fail   s <- xs]
  , Measure.rewrites   = S.fromList [s | Rewrite s <- xs]
  , Measure.rewriteWith = M.fromList [s | Rewritewith s <- xs]
  , Measure.bounds     = M.fromList [(bname i, i) | PBound i <- xs]
  , Measure.reflects   = S.fromList [s | Reflect s <- xs]
  , Measure.opaqueReflects = S.fromList [s | OpaqueReflect s <- xs]
  , Measure.hmeas      = S.fromList [s | HMeas  s <- xs]
  , Measure.inlines    = S.fromList [s | Inline s <- xs]
  , Measure.ignores    = S.fromList [s | Ignore s <- xs]
  , Measure.autosize   = S.fromList [s | ASize  s <- xs]
  , Measure.hbounds    = S.fromList [s | HBound s <- xs]
  , Measure.defs       = M.fromList [d | Define d <- xs]
  , Measure.axeqs      = []
  }

-- | Parse a single top level liquid specification
specP :: Parser BPspec
specP
  = fallbackSpecP "assume" ((reserved "reflect" >> fmap AssmReflect assmReflectBindP)
        <|> (reserved "relational" >>  fmap AssmRel relationalP)
        <|>                            fmap Assm   tyBindP  )
    <|> fallbackSpecP "assert"      (fmap Asrt    tyBindP  )
    <|> fallbackSpecP "autosize"    (fmap ASize   asizeP   )
    <|> (reserved "local"         >> fmap LAsrt   tyBindP  )

    -- TODO: These next two are synonyms, kill one
    <|> fallbackSpecP "axiomatize"  (fmap Reflect axiomP   )
    <|> fallbackSpecP "reflect"     (fmap Reflect axiomP   )
    <|> (reserved "opaque-reflect" >> fmap OpaqueReflect axiomP  )

    <|> fallbackSpecP "measure"    hmeasureP

    <|> fallbackSpecP "define"      (fmap Define  defineP  )
    <|> (reserved "infixl"        >> fmap BFix    infixlP  )
    <|> (reserved "infixr"        >> fmap BFix    infixrP  )
    <|> (reserved "infix"         >> fmap BFix    infixP   )
    <|> fallbackSpecP "inline"      (fmap Inline  inlineP  )
    <|> fallbackSpecP "ignore"      (fmap Ignore  inlineP  )

    <|> fallbackSpecP "bound"       (fmap PBound  boundP
                                 <|> fmap HBound  hboundP  )
    <|> (reserved "class"
         >> ((reserved "measure"  >> fmap CMeas  cMeasureP )
         <|> (reserved "laws"     >> fmap CLaws  classP)
         <|> fmap Class  classP                            ))
    <|> (reserved "instance"
         >> ((reserved "measure"  >> fmap IMeas  iMeasureP )
         <|> (reserved "laws"     >> fmap ILaws instanceLawP)
         <|> fmap RInst  instanceP ))

    <|> (reserved "import"        >> fmap Impt   symbolP   )

    <|> (reserved "data"
        >> ((reserved "variance"  >> fmap Varia  datavarianceP)
        <|> (reserved "size"      >> fmap DSize  dsizeP)
        <|> fmap DDecl  dataDeclP ))
    <|> (reserved "newtype"       >> fmap NTDecl dataDeclP )
    <|> (reserved "relational"    >> fmap Relational relationalP )
    <|> (reserved "include"       >> fmap Incl   filePathP )
    <|> fallbackSpecP "invariant"   (fmap Invt   invariantP)
    <|> (reserved "using"          >> fmap Using invaliasP )
    <|> (reserved "type"          >> fmap Alias  aliasP    )

    -- TODO: Next two are basically synonyms
    <|> fallbackSpecP "predicate"   (fmap EAlias ealiasP   )
    <|> fallbackSpecP "expression"  (fmap EAlias ealiasP   )

    <|> fallbackSpecP "embed"       (fmap Embed  embedP    )
    <|> fallbackSpecP "qualif"      (fmap Qualif (qualifierP sortP))
    <|> (reserved "lazyvar"       >> fmap LVars  lazyVarP  )

    <|> (reserved "lazy"          >> fmap Lazy   lazyVarP  )
    <|> (reserved "rewrite"       >> fmap Rewrite   rewriteVarP )
    <|> (reserved "rewriteWith"   >> fmap Rewritewith   rewriteWithP )
    <|> (reserved "fail"          >> fmap Fail   failVarP  )
    <|> (reserved "ple"           >> fmap Insts autoinstP  )
    <|> (reserved "automatic-instances" >> fmap Insts autoinstP  )
    <|> (reserved "LIQUID"        >> fmap Pragma pragmaP   )
    <|> (reserved "liquid"        >> fmap Pragma pragmaP   )
    <|> {- DEFAULT -}                fmap Asrts  tyBindsP
    <?> "specP"

-- | Try the given parser on the tail after matching the reserved word, and if
-- it fails fall back to parsing it as a haskell signature for a function with
-- the same name.
fallbackSpecP :: String -> Parser BPspec -> Parser BPspec
fallbackSpecP kw p = do
  (Loc l1 l2 _) <- locReserved kw
  p <|> fmap Asrts (tyBindsRemP (Loc l1 l2 (symbol kw)) )

-- | Same as tyBindsP, except the single initial symbol has already been matched
tyBindsRemP :: LocSymbol -> Parser ([LocSymbol], (Located BareType, Maybe [Located Expr]))
tyBindsRemP sy = do
  reservedOp "::"
  tb <- termBareTypeP
  return ([sy],tb)

pragmaP :: Parser (Located String)
pragmaP = locStringLiteral

autoinstP :: Parser (LocSymbol, Maybe Int)
autoinstP = do x <- locBinderP
               i <- optional (reserved "with" >> natural)
               return (x, fromIntegral <$> i)

lazyVarP :: Parser LocSymbol
lazyVarP = locBinderP


rewriteVarP :: Parser LocSymbol
rewriteVarP = locBinderP

rewriteWithP :: Parser (LocSymbol, [LocSymbol])
rewriteWithP = (,) <$> locBinderP <*> brackets (sepBy1 locBinderP comma)

failVarP :: Parser LocSymbol
failVarP = locBinderP

axiomP :: Parser LocSymbol
axiomP = locBinderP

hboundP :: Parser LocSymbol
hboundP = locBinderP

inlineP :: Parser LocSymbol
inlineP = locBinderP

asizeP :: Parser LocSymbol
asizeP = locBinderP

filePathP     :: Parser FilePath
filePathP     = angles $ some pathCharP
  where
    pathCharP :: Parser Char
    pathCharP = choice $ char <$> pathChars

    pathChars :: [Char]
    pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

datavarianceP :: Parser (Located Symbol, [Variance])
datavarianceP = liftM2 (,) locUpperIdP (many varianceP)

dsizeP :: Parser ([Located BareType], Located Symbol)
dsizeP = liftM2 (,) (parens $ sepBy (located genBareTypeP) comma) locBinderP


varianceP :: Parser Variance
varianceP = (reserved "bivariant"     >> return Bivariant)
        <|> (reserved "invariant"     >> return Invariant)
        <|> (reserved "covariant"     >> return Covariant)
        <|> (reserved "contravariant" >> return Contravariant)
        <?> "Invalid variance annotation\t Use one of bivariant, invariant, covariant, contravariant"

tyBindsP :: Parser ([LocSymbol], (Located BareType, Maybe [Located Expr]))
tyBindsP =
  xyP (sepBy1 locBinderP comma) (reservedOp "::") termBareTypeP

tyBindNoLocP :: Parser (LocSymbol, BareType)
tyBindNoLocP = second val <$> tyBindP

-- | Parses a type signature as it occurs in "assume" and "assert" directives.
tyBindP :: Parser (LocSymbol, Located BareType)
tyBindP =
  (,) <$> locBinderP <* reservedOp "::" <*> located genBareTypeP

-- | Parses a loc symbol.
assmReflectBindP :: Parser (LocSymbol, LocSymbol)
assmReflectBindP =
  (,) <$> locBinderP <* reservedOp "as" <*> locBinderP

termBareTypeP :: Parser (Located BareType, Maybe [Located Expr])
termBareTypeP = do
  t <- located genBareTypeP
  termTypeP t <|> return (t, Nothing)

termTypeP :: Located BareType ->Parser (Located BareType, Maybe [Located Expr])
termTypeP t
  = do
       reservedOp "/"
       es <- brackets $ sepBy (located exprP) comma
       return (t, Just es)

-- -------------------------------------

invariantP :: Parser (Located BareType)
invariantP = located genBareTypeP

invaliasP :: Parser (Located BareType, Located BareType)
invaliasP
  = do t  <- located genBareTypeP
       reserved "as"
       ta <- located genBareTypeP
       return (t, ta)

genBareTypeP :: Parser BareType
genBareTypeP = bareTypeP

embedP :: Parser (Located Symbol, FTycon, TCArgs)
embedP = do
  x <- locUpperIdP
  a <- try (reserved "*" >> return WithArgs) <|> return NoArgs -- TODO: reserved "*" looks suspicious
  _ <- reserved "as"
  t <- fTyConP
  return (x, t, a)
  --  = xyP locUpperIdP symbolTCArgs (reserved "as") fTyConP


aliasP :: Parser (Located (RTAlias Symbol BareType))
aliasP  = rtAliasP id     bareTypeP <?> "aliasP"

ealiasP :: Parser (Located (RTAlias Symbol Expr))
ealiasP = try (rtAliasP symbol predP)
      <|> rtAliasP symbol exprP
      <?> "ealiasP"

-- | Parser for a LH type synonym.
rtAliasP :: (Symbol -> tv) -> Parser ty -> Parser (Located (RTAlias tv ty))
rtAliasP f bodyP
  = do pos  <- getSourcePos
       name <- upperIdP
       args <- many aliasIdP
       reservedOp "="
       body <- bodyP
       posE <- getSourcePos
       let (tArgs, vArgs) = partition (isSmall . headSym) args
       return $ Loc pos posE (RTA name (f <$> tArgs) vArgs body)

hmeasureP :: Parser BPspec
hmeasureP = do
  setLayout
  b <- locBinderP
  (do reservedOp "::"
      ty <- located genBareTypeP
      popLayout >> popLayout
      eqns <- block $ try $ measureDefP (rawBodyP <|> tyBodyP ty)
      return (Meas $ Measure.mkM b ty eqns MsMeasure mempty))
    <|> (popLayout >> popLayout >> return (HMeas b))

measureP :: Parser (Measure (Located BareType) LocSymbol)
measureP = do
  (x, ty) <- indentedLine tyBindP
  _ <- optional semi
  eqns    <- block $ measureDefP (rawBodyP <|> tyBodyP ty)
  return   $ Measure.mkM x ty eqns MsMeasure mempty

-- | class measure
cMeasureP :: Parser (Measure (Located BareType) ())
cMeasureP
  = do (x, ty) <- tyBindP
       return $ Measure.mkM x ty [] MsClass mempty

iMeasureP :: Parser (Measure (Located BareType) LocSymbol)
iMeasureP = measureP


oneClassArg :: Parser [Located BareType]
oneClassArg
  = sing <$> located (rit <$> classBTyConP <*> (map val <$> classParams))
  where
    rit t as    = RApp t ((`RVar` mempty) <$> as) [] mempty
    classParams =  (reserved "where" >> return [])
               <|> ((:) <$> (fmap bTyVar <$> locLowerIdP) <*> classParams)
    sing x      = [x]


superP :: Parser (Located BareType)
superP = located (toRCls <$> bareAtomBindP)
  where toRCls x = x

instanceLawP :: Parser (RILaws (Located BareType))
instanceLawP
  = do l1   <- getSourcePos
       sups <- supersP
       c    <- classBTyConP
       tvs  <- manyTill (located bareTypeP) (try $ reserved "where")
       ms   <- block eqBinderP
       l2   <- getSourcePos
       return $ RIL c sups tvs ms (Loc l1 l2 ())
  where
    supersP  = try ((parens (superP `sepBy1` comma) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []

    eqBinderP = xyP xP (reservedOp "=") xP

    xP = locBinderP

instanceP :: Parser (RInstance (Located BareType))
instanceP
  = do _    <- supersP
       c    <- classBTyConP
       tvs  <- try oneClassArg <|> manyTill iargsP (try $ reserved "where")
       ms   <- block riMethodSigP
       return $ RI c tvs ms
  where
    supersP  = try ((parens (superP `sepBy1` comma) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []

    iargsP   =   (mkVar . bTyVar <$> tyVarIdP)
            <|> parens (located bareTypeP)


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
       tvs  <- manyTill (bTyVar <$> tyVarIdP) (try $ reserved "where")
       ms   <- block tyBindP -- <|> sepBy tyBindP semi
       return $ RClass c sups tvs ms
  where
    supersP  = try ((parens (superP `sepBy1` comma) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []

rawBodyP :: Parser Body
rawBodyP
  = braces $ do
      v <- symbolP
      reservedOp "|"
      R v <$> predP

tyBodyP :: Located BareType -> Parser Body
tyBodyP ty
  = case outTy (val ty) of
      Just bt | isPropBareType bt
                -> P <$> predP
      _         -> E <$> exprP
    where outTy (RAllT _ t _)    = outTy t
          outTy (RAllP _ t)      = outTy t
          outTy (RFun _ _ _ t _) = Just t
          outTy _                = Nothing

locUpperOrInfixIdP :: Parser (Located Symbol)
locUpperOrInfixIdP = locUpperIdP' <|> locInfixCondIdP

locBinderP :: Parser (Located Symbol)
locBinderP =
  located binderP -- TODO

-- | LHS of the thing being defined
--
-- TODO, Andres: this is still very broken
--
{-
binderP :: Parser Symbol
binderP    = pwr    <$> parens (idP bad)
         <|> symbol <$> idP badc
  where
    idP p  = takeWhile1P Nothing (not . p)
    badc c = (c == ':') || (c == ',') || bad c
    bad c  = isSpace c || c `elem` ("(,)[]" :: String)
    pwr s  = symbol $ "(" `mappend` s `mappend` ")"
-}
binderP :: Parser Symbol
binderP =
      symbol . (\ x -> "(" <> x <> ")") . symbolText <$> parens infixBinderIdP
  <|> binderIdP
  -- Note: It is important that we do *not* use the LH/fixpoint reserved words here,
  -- because, for example, we must be able to use "assert" as an identifier.
  --
  -- TODO, Andres: I have no idea why we make the parens part of the symbol here.
  -- But I'm reproducing this behaviour for now, as it is backed up via a few tests.

measureDefP :: Parser Body -> Parser (Def (Located BareType) LocSymbol)
measureDefP bodyP
  = do mname   <- locSymbolP
       (c, xs) <- measurePatP
       reservedOp "="
       body    <- bodyP
       let xs'  = symbol . val <$> xs
       return   $ Def mname (symbol <$> c) Nothing ((, Nothing) <$> xs') body

measurePatP :: Parser (LocSymbol, [LocSymbol])
measurePatP
  =  parens (try conPatP <|> try consPatP <|> nilPatP <|> tupPatP)
 <|> nullaryConPatP
 <?> "measurePatP"

tupPatP :: Parser (Located Symbol, [Located Symbol])
tupPatP  = mkTupPat  <$> sepBy1 locLowerIdP comma

conPatP :: Parser (Located Symbol, [Located Symbol])
conPatP  = (,)       <$> dataConNameP <*> many locLowerIdP

consPatP :: IsString a
         => Parser (Located a, [Located Symbol])
consPatP = mkConsPat <$> locLowerIdP  <*> reservedOp ":" <*> locLowerIdP

nilPatP :: IsString a
        => Parser (Located a, [t])
nilPatP  = mkNilPat  <$> brackets (pure ())

nullaryConPatP :: Parser (Located Symbol, [t])
nullaryConPatP = nilPatP <|> ((,[]) <$> dataConNameP)
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
   =  explicitCommaBlock predTypeDDP -- braces (sepBy predTypeDDP comma)
  <|> many dataConFieldP
  <?> "dataConFieldP"

dataConFieldP :: Parser (Symbol, BareType)
dataConFieldP
   =  parens (try predTypeDDP <|> dbTypeP)
  <|> dbTyArgP -- unparenthesised constructor fields must be "atomic"
  <?> "dataConFieldP"
  where
    dbTypeP = (,) <$> dummyBindP <*> bareTypeP
    dbTyArgP = (,) <$> dummyBindP <*> bareTyArgP

predTypeDDP :: Parser (Symbol, BareType)
predTypeDDP = (,) <$> bbindP <*> bareTypeP

bbindP   :: Parser Symbol
bbindP   = lowerIdP <* reservedOp "::"

dataConP :: [Symbol] -> Parser DataCtor
dataConP as = do
  x   <- dataConNameP
  xts <- dataConFieldsP
  return $ DataCtor x as [] xts Nothing

adtDataConP :: [Symbol] -> Parser DataCtor
adtDataConP as = do
  x     <- dataConNameP
  reservedOp "::"
  tr    <- toRTypeRep <$> bareTypeP
  return $ DataCtor x (tRepVars as tr) [] (tRepFields tr) (Just $ ty_res tr)

tRepVars :: Symbolic a => [Symbol] -> RTypeRep c a r -> [Symbol]
tRepVars as tr = case fst <$> ty_vars tr of
  [] -> as
  vs -> symbol . ty_var_value <$> vs

tRepFields :: RTypeRep c tv r -> [(Symbol, RType c tv r)]
tRepFields tr = zip (ty_binds tr) (ty_args tr)

-- TODO: fix Located
dataConNameP :: Parser (Located Symbol)
dataConNameP
  =  located
 (   try upperIdP
 <|> pwr <$> parens (idP bad)
 <?> "dataConNameP"
 )
  where
     idP p  = takeWhile1P Nothing (not . p)
     bad c  = isSpace c || c `elem` ("(,)" :: String)
     pwr s  = symbol $ "(" <> s <> ")"

dataSizeP :: Parser (Maybe SizeFun)
dataSizeP
  = brackets (Just . SymSizeFun <$> locLowerIdP)
  <|> return Nothing

relationalP :: Parser (LocSymbol, LocSymbol, LocBareType, LocBareType, RelExpr, RelExpr)
relationalP = do
   x <- locBinderP
   reserved "~"
   y <- locBinderP
   reserved "::"
   braces $ do
    tx <- located genBareTypeP
    reserved "~"
    ty <- located genBareTypeP
    reserved "|"
    assm <- try (relrefaP <* reserved "|-") <|> return (ERBasic PTrue)
    ex <- relrefaP
    return (x,y,tx,ty,assm,ex)

dataDeclP :: Parser DataDecl
dataDeclP = do
  pos <- getSourcePos
  x   <- locUpperOrInfixIdP
  fsize <- dataSizeP
  dataDeclBodyP pos x fsize <|> return (emptyDecl x pos fsize)

emptyDecl :: LocSymbol -> SourcePos -> Maybe SizeFun -> DataDecl
emptyDecl x pos fsize@(Just _)
  = DataDecl (DnName x) [] [] Nothing pos fsize Nothing DataUser
emptyDecl x pos _
  = uError (ErrBadData (sourcePosSrcSpan pos) (pprint (val x)) msg)
  where
    msg = "You should specify either a default [size] or one or more fields in the data declaration"

dataDeclBodyP :: SourcePos -> LocSymbol -> Maybe SizeFun -> Parser DataDecl
dataDeclBodyP pos x fsize = do
  vanilla    <- null <$> many locUpperIdP
  as         <- many noWhere -- TODO: check this again
  ps         <- predVarDefsP
  (pTy, dcs) <- dataCtorsP as
  let dn      = dataDeclName pos x vanilla dcs
  return      $ DataDecl dn as ps (Just dcs) pos fsize pTy DataUser

dataDeclName :: SourcePos -> LocSymbol -> Bool -> [DataCtor] -> DataName
dataDeclName _ x True  _     = DnName x               -- vanilla data    declaration
dataDeclName _ _ False (d:_) = DnCon  (dcName d)      -- family instance declaration
dataDeclName p x _  _        = uError (ErrBadData (sourcePosSrcSpan p) (pprint (val x)) msg)
  where
    msg                  = "You should specify at least one data constructor for a family instance"

-- | Parse the constructors of a datatype, allowing both classic and GADT-style syntax.
--
-- Note that as of 2020-10-14, we changed the syntax of GADT-style datatype declarations
-- to match Haskell more closely and parse all constructors in a layout-sensitive block,
-- whereas before we required them to be separated by @|@.
--
dataCtorsP :: [Symbol] -> Parser (Maybe BareType, [DataCtor])
dataCtorsP as = do
  (pTy, dcs) <-     (reservedOp "="     >> ((Nothing, ) <$>                 sepBy (dataConP    as) (reservedOp "|")))
                <|> (reserved   "where" >> ((Nothing, ) <$>                 block (adtDataConP as)                 ))
                <|>                        ((,)         <$> dataPropTyP <*> block (adtDataConP as)                  )
  return (pTy, Misc.sortOn (val . dcName) dcs)

noWhere :: Parser Symbol
noWhere =
  try $ do
  s <- tyVarIdP
  guard (s /= "where")
  return s

dataPropTyP :: Parser (Maybe BareType)
dataPropTyP = Just <$> between (reservedOp "::") (reserved "where") bareTypeP

---------------------------------------------------------------------
-- Identifiers ------------------------------------------------------
---------------------------------------------------------------------

-- Andres, TODO: Fix all the rules for identifiers. This was limited to all lowercase letters before.
tyVarIdR :: Parser Symbol
tyVarIdR =
  condIdR (lowerChar <|> char '_') isAlphaNum isNotReserved "unexpected reserved name"

tyVarIdP :: Parser Symbol
tyVarIdP =
  lexeme tyVarIdR

aliasIdR :: Parser Symbol
aliasIdR =
  condIdR (letterChar <|> char '_') isAlphaNum (const True) "unexpected"

aliasIdP :: Parser Symbol
aliasIdP =
  lexeme aliasIdR

-- | Andres, TODO: This must be liberal with respect to reserved words (LH reserved words are
-- not Haskell reserved words, and we want to redefine all sorts of internal stuff).
--
-- Also, this currently accepts qualified names by allowing '.' ...
-- Moreover, it seems that it is currently allowed to use qualified symbolic names in
-- unparenthesised form. Oh, the parser is also used for reflect, where apparently
-- symbolic names appear in unqualified and unparenthesised form.
-- Furthermore, : is explicitly excluded because a : can directly, without whitespace,
-- follow a binder ...
--
binderIdR :: Parser Symbol
binderIdR =
  condIdR (letterChar <|> char '_' <|> satisfy isHaskellOpStartChar) (\ c -> isAlphaNum c || isHaskellOpStartChar c || c `elem` ("_'" :: String)) (const True) "unexpected"

binderIdP :: Parser Symbol
binderIdP =
  lexeme binderIdR

infixBinderIdR :: Parser Symbol
infixBinderIdR =
  condIdR (letterChar <|> char '_' <|> satisfy isHaskellOpChar) (\ c -> isAlphaNum c || isHaskellOpChar c || c `elem` ("_'" :: String)) (const True) "unexpected"

infixBinderIdP :: Parser Symbol
infixBinderIdP =
  lexeme infixBinderIdR

upperIdR' :: Parser Symbol
upperIdR' =
  condIdR upperChar (\ c -> isAlphaNum c || c == '\'') (const True) "unexpected"

locUpperIdP' :: Parser (Located Symbol)
locUpperIdP' =
  locLexeme upperIdR'

-- Andres, TODO: This used to force a colon at the end. Also, it used to not
-- allow colons in the middle. Finally, it should probably exclude all reserved
-- operators. I'm just excluding :: because I'm pretty sure that would be
-- undesired.
--
infixCondIdR :: Parser Symbol
infixCondIdR =
  condIdR (char ':') isHaskellOpChar (/= "::") "unexpected double colon"

-- Andres, TODO: This used to be completely ad-hoc. It's still not good though.
infixIdR :: Parser Symbol
infixIdR =
  condIdR (satisfy isHaskellOpChar) isHaskellOpChar (/= "::") "unexpected double colon"

infixIdP :: Parser Symbol
infixIdP =
  lexeme infixIdR

{-
infixVarIdR :: Parser Symbol
infixVarIdR =
  condIdR (satisfy isHaskellOpStartChar) isHaskellOpChar (const True)

infixVarIdP :: Parser Symbol
infixVarIdP =
  lexeme infixVarIdR
-}

isHaskellOpChar :: Char -> Bool
isHaskellOpChar c
  = c `elem` (":!#$%&*+./<=>?@\\^|~-" :: String)

isHaskellOpStartChar :: Char -> Bool
isHaskellOpStartChar c
  = c `elem` ("!#$%&*+./<=>?@\\^|~-" :: String)

locInfixCondIdP :: Parser (Located Symbol)
locInfixCondIdP =
  locLexeme infixCondIdR
