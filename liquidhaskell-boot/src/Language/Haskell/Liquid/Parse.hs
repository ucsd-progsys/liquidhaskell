{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# OPTIONS_GHC -Wno-orphans           #-}

module Language.Haskell.Liquid.Parse
  ( hsSpecificationP
  , parseSpecComments
  , singleSpecP
  , BPspec (..)
  , parseTest'
  )
  where

import           Control.Arrow                          (second)
import           Control.Monad
import           Control.Monad.Identity
import           Data.Bifunctor                         (first)
import qualified Data.Char                              as Char
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
import qualified Text.PrettyPrint.HughesPJ              as PJ
import           Text.PrettyPrint.HughesPJ.Compat       ((<+>))
import           Language.Fixpoint.Types                hiding (panic, SVar, DDecl, DataDecl, DataCtor (..), Error, R, Predicate)
import           Language.Haskell.Liquid.GHC.Misc       hiding (getSourcePos)
import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import qualified Language.Haskell.Liquid.Misc           as Misc
import qualified Language.Haskell.Liquid.Measure        as Measure
import           Language.Fixpoint.Parse                hiding (Parser, dataDeclP, refBindP, refP, refDefP, parseTest')
import qualified Liquid.GHC.API                         as GHC

import Control.Monad.State

-- * Top-level parsing API

hsSpecificationP :: GHC.ModuleName -> [BPspec] -> (ModName, BareSpecParsed)
hsSpecificationP modName specs = (ModName SrcImport modName, mkSpec specs)

-- | Parse comments in .hs and .lhs files
parseSpecComments :: [(SourcePos, String)] -> Either [Error] [BPspec]
parseSpecComments specComments =
  case go ([], []) initPStateWithList specComments of
    ([], specs) ->
      Right specs
    (errors, _) ->
      Left errors
  where
    go :: ([Error], [BPspec])   -- accumulated errors and parsed specs (in reverse order)
       -> LHPState              -- parser state (primarily infix operator priorities)
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

type LHPState = PStateV LocSymbol
type Parser = ParserV LocSymbol

instance ParseableV LocSymbol where
  parseV = locSymbolP
  mkSu = Su . M.fromList . reverse . filter notTrivial
    where
      notTrivial (x, EVar y) = x /= val y
      notTrivial _           = True
  vFromString = fmap symbol

initPStateWithList :: LHPState
initPStateWithList
  = (initPState composeFun)
               { empList    = Just $ \lx -> EVar ("GHC.Types.[]" <$ lx)
               , singList   = Just (\lx e -> EApp (EApp (EVar ("GHC.Types.:" <$ lx)) e) (EVar ("GHC.Types.[]" <$ lx)))
               }
  where composeFun = Nothing

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
parseWithError :: forall a. LHPState -> Parser a -> SourcePos -> String -> Either (ParseErrorBundle String Void) (LHPState, a)
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
                    , _pct :: BareTypeParsed }

data PcScope = PcImplicit Symbol
             | PcExplicit Symbol
             | PcNoSymbol
             deriving (Eq,Show)

nullPC :: BareTypeParsed -> ParamComp
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
            return (PC sb (mkRFun sy t1 t2)))
        <|>
         (do
            reservedOp "=>"
            PC _ t2 <- btP
            -- TODO:AZ return an error if s == PcExplicit
            return $ PC sb $ foldr (mkRFun dummySymbol) t2 (getClasses t1))
         <|>
          (do
             b <- locInfixSymbolP
             PC _ t2 <- btP
             return $ PC sb $ RApp
               (mkBTyCon $ fmap (makeUnresolvedLHName LHTcName) b)
               [t1,t2]
               []
               trueURef
          )
         <|> return c

    mkRFun b t t' = RFun b defRFInfo t t' trueURef

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
      return   $ PC sb (t `strengthenUReft` MkUReft trueReft p)

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
      PC (PcImplicit b) <$> dummyP (lowerIdTail lb)

unnamedCircleP :: Parser ParamComp
unnamedCircleP = do
  lb <- located dummyBindP
  let b = val lb
  t1 <- bareArgP b
  return $ PC (PcImplicit b) t1

-- ---------------------------------------------------------------------

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareTypeParsed
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


bareArgP :: Symbol -> Parser BareTypeParsed
bareArgP vvv
  =  refDefP vvv refasHoleP bbaseP    -- starts with '{'
 <|> holeP                            -- starts with '_'
 <|> dummyP bbaseP
 <|> parens bareTypeP                 -- starts with '('
                                      -- starts with '_', '[', '(', lower, upper
 <?> "bareArgP"

bareAtomP
  :: (Parser (ExprV LocSymbol) -> Parser (ReftV LocSymbol -> BareTypeParsed) -> Parser BareTypeParsed)
  -> Parser BareTypeParsed
bareAtomP ref
  =  ref refasHoleP bbaseP
 <|> holeP
 <|> dummyP bbaseP
 <?> "bareAtomP"

bareAtomBindP :: Parser BareTypeParsed
bareAtomBindP = bareAtomP refBindBindP


-- Either
--  { x : t | ra }
-- or
--  { ra }
refBindBindP :: Parser (ExprV LocSymbol)
             -> Parser (ReftV LocSymbol -> BareTypeParsed)
             -> Parser BareTypeParsed
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
        -> Parser (ExprV LocSymbol)
        -> Parser (ReftV LocSymbol -> BareTypeParsed)
        -> Parser BareTypeParsed
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

refP :: Parser (ReftV LocSymbol -> BareTypeParsed) -> Parser BareTypeParsed
refP = refBindBindP refaP

relrefaP :: Parser (RelExprV LocSymbol)
relrefaP =
  try (ERUnChecked <$> refaP <* reserved ":=>" <*> relrefaP)
    <|> try (ERChecked <$> refaP <* reserved "!=>" <*> relrefaP)
    <|> ERBasic <$> refaP

-- "sym :" or return the devault sym
optBindP :: Symbol -> Parser Symbol
optBindP x = try bindP <|> return x

holeP :: Parser BareTypeParsed
holeP    = reserved "_" >> return (RHole $ uTop $ Reft ("VV", hole))

holeRefP :: Parser (ReftV v -> BareTypeV v)
holeRefP = reserved "_" >> return (RHole . uTop)

-- NOPROP refasHoleP :: Parser Expr
-- NOPROP refasHoleP  = try refaP
-- NOPROP          <|> (reserved "_" >> return hole)

refasHoleP :: Parser (ExprV LocSymbol)
refasHoleP
  =  (reserved "_" >> return hole)
 <|> refaP
 <?> "refasHoleP"

bbaseP :: Parser (ReftV LocSymbol -> BareTypeParsed)
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
     l <- located lowerIdP
     lowerIdTail l

maybeBind :: Parser a -> Parser (Maybe Symbol, a)
maybeBind parser = do {bd <- maybeP' bbindP; ty <- parser ; return (bd, ty)}
  where
    maybeP' p = try (Just <$> p)
             <|> return Nothing

lowerIdTail :: LocSymbol -> Parser (ReftV LocSymbol -> BareTypeParsed)
lowerIdTail l =
          fmap (bAppTy (bTyVar l)) (some bareTyArgP)
      <|> fmap (bRVar (bTyVar l)) monoPredicateP

bTyConP :: Parser BTyCon
bTyConP
  =  (reservedOp "'" >> mkPromotedBTyCon <$> locUpperIdLHNameP (LHDataConName LHAnyModuleNameF))
 <|> mkBTyCon <$> locUpperIdLHNameP LHTcName
 <|> (reserved "*" >>
        return (mkBTyCon (dummyLoc $ makeUnresolvedLHName LHTcName $ symbol ("*" :: String)))
     )
 <?> "bTyConP"

locUpperIdLHNameP :: LHNameSpace -> Parser (Located LHName)
locUpperIdLHNameP ns = fmap (makeUnresolvedLHName ns) <$> locUpperIdP

mkPromotedBTyCon :: Located LHName -> BTyCon
mkPromotedBTyCon x = BTyCon x False True -- (consSym '\'' <$> x) False True

classBTyConP :: Parser BTyCon
classBTyConP = mkClassBTyCon <$> locUpperIdLHNameP LHTcName

mkClassBTyCon :: Located LHName -> BTyCon
mkClassBTyCon x = BTyCon x True False

bbaseNoAppP :: Parser (ReftV LocSymbol -> BareTypeParsed)
bbaseNoAppP
  =  holeRefP
 <|> liftM2 bLst (brackets (optional bareTypeP)) predicatesP
 <|> liftM2 bTup (parens $ sepBy (maybeBind bareTypeP) comma) predicatesP
 <|> try (liftM4 bCon bTyConP predicatesP (return []) (return $ Pr []))
 <|> liftM2 bRVar (bTyVar <$> located lowerIdP) monoPredicateP
 <?> "bbaseNoAppP"

bareTyArgP :: Parser BareTypeParsed
bareTyArgP
  =  (RExprArg . fmap (ECon . I) <$> locNatural)
 <|> try (braces $ RExprArg <$> located exprP)
 <|> try bareAtomNoAppP
 <|> try (parens bareTypeP)
 <?> "bareTyArgP"

bareAtomNoAppP :: Parser BareTypeParsed
bareAtomNoAppP
  =  refP bbaseNoAppP
 <|> dummyP bbaseNoAppP
 <?> "bareAtomNoAppP"


constraintP :: Parser BareTypeParsed
constraintP
  = do xts <- constraintEnvP
       t1  <- bareTypeP
       reservedOp "<:"
       fromRTypeRep . RTypeRep [] []
                               ((val . fst <$> xts) ++ [dummySymbol])
                               (replicate (length xts + 1) defRFInfo)
                               (replicate (length xts + 1) trueURef)
                               ((snd <$> xts) ++ [t1]) <$> bareTypeP

trueURef :: UReftV v (ReftV v)
trueURef = MkUReft trueReft (Pr [])

constraintEnvP :: Parser [(LocSymbol, BareTypeParsed)]
constraintEnvP
   =  try (do xts <- sepBy tyBindNoLocP comma
              reservedOp "|-"
              return xts)
  <|> return []
  <?> "constraintEnvP"

rrTy :: BareTypeParsed -> BareTypeParsed -> BareTypeParsed
rrTy ct = RRTy (xts ++ [(dummySymbol, tr)]) trueURef OCons
  where
    tr   = ty_res trep
    xts  = zip (ty_binds trep) (ty_args trep)
    trep = toRTypeRep ct

--  "forall <z w> . TYPE"
-- or
--  "forall x y <z :: Nat, w :: Int> . TYPE"
bareAllP :: Parser BareTypeParsed
bareAllP = do
  sp <- getSourcePos
  as  <- tyVarDefsP
  ps  <- angles inAngles
        <|> return []
  _ <- dot
  t <- bareTypeP
  return $ foldr rAllT (foldr (rAllP sp) t ps) (makeRTVar <$> as)
  where
    rAllT a t = RAllT a t trueURef
    inAngles  = try  (sepBy  predVarDefP comma)

-- See #1907 for why we have to alpha-rename pvar binders
rAllP :: SourcePos -> PVarV LocSymbol (BSortV LocSymbol) -> BareTypeParsed -> BareTypeParsed
rAllP sp p t = RAllP p' ({- F.tracepp "rAllP" $ -} substPVar p p' t)
  where
    p'  = p { pname = pn' }
    pn' = pname p `intSymbol` lin `intSymbol` col
    lin = unPos (sourceLine sp)
    col = unPos (sourceColumn  sp)

tyVarDefsP :: Parser [BTyVar]
tyVarDefsP
  = parens (many (bTyVar <$> located tyKindVarIdP))
 <|> many (bTyVar <$> located tyVarIdP)
 <?> "tyVarDefsP"

tyKindVarIdP :: Parser Symbol
tyKindVarIdP = do
   tv <- tyVarIdP
   do reservedOp "::"; _ <- kindP; return tv <|> return tv

kindP :: Parser BareTypeParsed
kindP = bareAtomBindP

predVarDefsP :: Parser [PVarV LocSymbol (BSortV LocSymbol)]
predVarDefsP
  =  angles (sepBy1 predVarDefP comma)
 <|> return []
 <?> "predVarDefP"

predVarDefP :: Parser (PVarV LocSymbol (BSortV LocSymbol))
predVarDefP
  = bPVar <$> predVarIdP <*> reservedOp "::" <*> propositionSortP

predVarIdP :: Parser Symbol
predVarIdP
  = symbol <$> tyVarIdP

bPVar :: Symbol -> t -> [(Symbol, t1)] -> PVarV LocSymbol t1
bPVar p _ xts  = PV p τ dummySymbol τxs
  where
    (_, τ) = safeLast "bPVar last" xts
    τxs    = [ (τ', x, EVar (dummyLoc x)) | (x, τ') <- init xts ]
    safeLast _ xs@(_:_) = last xs
    safeLast msg _      = panic Nothing $ "safeLast with empty list " ++ msg

propositionSortP :: Parser [(Symbol, BSortV LocSymbol)]
propositionSortP = map (fmap toRSort) <$> propositionTypeP

propositionTypeP :: Parser [(Symbol, BareTypeParsed)]
propositionTypeP = either fail return . mkPropositionType =<< bareTypeP

mkPropositionType :: BareTypeParsed -> Either String [(Symbol, BareTypeParsed)]
mkPropositionType t
  | isOk      = Right $ zip (ty_binds tRep) (ty_args tRep)
  | otherwise = Left mkErr
  where
    isOk      = isPropBareType (ty_res tRep)
    tRep      = toRTypeRep t
    mkErr     = "Proposition type with non-Bool output: " ++ showpp (parsedToBareType t)

xyP :: Parser x -> Parser a -> Parser y -> Parser (x, y)
xyP lP sepP rP =
  (,) <$> lP <* sepP <*> rP

dummyBindP :: Parser Symbol
dummyBindP = tempSymbol "db" <$> freshIntP

isPropBareType :: RTypeV v BTyCon t t1 -> Bool
isPropBareType (RApp tc [] _ _) =
    case val (btc_tc tc) of
      LHNUnresolved _ s -> s == boolConName
      _ -> False
isPropBareType _ = False

getClasses :: RTypeV v BTyCon t t1 -> [RTypeV v BTyCon t t1]
getClasses (RApp tc ts ps r)
  | isTuple tc
  = concatMap getClasses ts
  | otherwise
  = [RApp (tc { btc_class = True }) ts ps r]
getClasses t
  = [t]

dummyP ::  Monad m => m (ReftV LocSymbol -> b) -> m b
dummyP fm
  = fm `ap` return trueReft

symsP :: Monoid r
      => Parser [(Symbol, RTypeV v c BTyVar r)]
symsP
  = do reservedOp "\\"
       ss <- many symbolP
       reservedOp "->"
       return $ (, dummyRSort) <$> ss
 <|> return []
 <?> "symsP"

dummyRSort :: Monoid r => RTypeV v c BTyVar r
dummyRSort
  = RVar (BTV "dummy") mempty

predicatesP :: Monoid r
            => Parser [Ref (RTypeV LocSymbol c BTyVar r) BareTypeParsed]
predicatesP
   =  angles (sepBy1 predicate1P comma)
  <|> return []
  <?> "predicatesP"

predicate1P :: Monoid r
            => Parser (Ref (RTypeV LocSymbol c BTyVar r) BareTypeParsed)
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

mmonoPredicateP :: Parser (PredicateV LocSymbol)
mmonoPredicateP
   = try (angles $ angles monoPredicate1P)
  <|> return (Pr [])
  <?> "mmonoPredicateP"

monoPredicateP :: Parser (PredicateV LocSymbol)
monoPredicateP
   = try (angles monoPredicate1P)
  <|> return (Pr [])
  <?> "monoPredicateP"

monoPredicate1P :: Parser (PredicateV LocSymbol)
monoPredicate1P
   =  (reserved "True" >> return (Pr []))
  <|> (pdVar <$> parens predVarUseP)
  <|> (pdVar <$>        predVarUseP)
  <?> "monoPredicate1P"

predVarUseP :: Parser (PVarV LocSymbol String)
predVarUseP
  = do (p, xs) <- funArgsP
       return   $ PV p dummyTyId dummySymbol [ (dummyTyId, dummySymbol, x) | x <- xs ]

funArgsP :: Parser (Symbol, [ExprV LocSymbol])
funArgsP  = try realP <|> empP <?> "funArgsP"
  where
    empP  = (,[]) <$> predVarIdP
    realP = do (EVar lp, xs) <- splitEApp <$> funAppP
               return (val lp, xs)

boundP :: Parser (Bound (Located BareTypeParsed) (ExprV LocSymbol))
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
                      xs <- many $ do
                        ls <- locSymbolP
                        pure $ bTyVar ls <$ ls
                      reservedOp  "."
                      return (fmap (`RVar` trueURef) <$> xs)
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
       -> ExprV LocSymbol -> Ref τ (RTypeV LocSymbol c BTyVar (UReftV LocSymbol (ReftV LocSymbol)))
bRProp []    _    = panic Nothing "Parse.bRProp empty list"
bRProp syms' epr  = RProp ss $ bRVar (BTV $ dummyLoc dummyName) (Pr []) r
  where
    (ss, (v, _))  = (init symsf, last symsf)
    symsf         = [(y, s) | ((_, s), y) <- syms']
    su            = mkSubstLocSymbol [(x, EVar $ dummyLoc y) | ((x, _), y) <- syms', x /= v]
    r             = Reft (v, substExprV val su epr)

mkSubstLocSymbol :: [(Symbol, ExprV LocSymbol)] -> SubstV LocSymbol
mkSubstLocSymbol = Su . M.fromList . reverse . filter notTrivial
  where
    notTrivial (x, EVar y) = x /= val y
    notTrivial _           = True

bRVar :: tv -> PredicateV v -> r -> RTypeV v c tv (UReftV v r)
bRVar α p r = RVar α (MkUReft r p)

bLst :: Maybe (RTypeV v BTyCon tv (UReftV v r))
     -> [RTPropV v BTyCon tv (UReftV v r)]
     -> r
     -> RTypeV v BTyCon tv (UReftV v r)
bLst (Just t) rs r = RApp (mkBTyCon $ dummyLoc $ makeUnresolvedLHName LHTcName listConName) [t] rs (reftUReft r)
bLst Nothing  rs r = RApp (mkBTyCon $ dummyLoc $ makeUnresolvedLHName LHTcName listConName) []  rs (reftUReft r)

bTup :: [(Maybe Symbol, BareTypeParsed)]
     -> [RTPropV LocSymbol BTyCon BTyVar (UReftV LocSymbol (ReftV LocSymbol))]
     -> ReftV LocSymbol
     -> BareTypeParsed
bTup [(_,t)] _ r
  | isTauto (fmap val r)  = t
  | otherwise  = t `strengthenUReft` reftUReft r
bTup ts rs r
  | all Mb.isNothing (fst <$> ts) || length ts < 2
  = RApp
      (mkBTyCon $ dummyLoc $ makeUnresolvedLHName LHTcName $ fromString $ "Tuple" ++ show (length ts))
      (snd <$> ts) rs (reftUReft r)
  | otherwise
  = RApp
      (mkBTyCon $ dummyLoc $ makeUnresolvedLHName LHTcName $ fromString $ "Tuple" ++ show (length ts))
      (mapReft (const trueURef) . snd <$> ts)
      rs'
      (reftUReft r)
  where
    args       = [(Mb.fromMaybe dummySymbol x, mapReft mempty t) | (x,t) <- ts]
    makeProp i = RProp (reverse $ take i args) ((snd <$> ts)!!i)
    rs'        = makeProp <$> [1..(length ts-1)]


-- Temporarily restore this hack benchmarks/esop2013-submission/Array.hs fails
-- w/o it
-- TODO RApp Int [] [p] true should be syntactically different than RApp Int [] [] p
-- bCon b s [RProp _ (RHole r1)] [] _ r = RApp b [] [] $ r1 `meet` (MkUReft r mempty s)
bCon :: c
     -> [RTPropV v c tv (UReftV v r)]
     -> [RTypeV v c tv (UReftV v r)]
     -> PredicateV v
     -> r
     -> RTypeV v c tv (UReftV v r)
bCon b rs ts p r = RApp b ts rs $ MkUReft r p

bAppTy :: Foldable t => BTyVar -> t BareTypeParsed -> ReftV LocSymbol -> BareTypeParsed
bAppTy v ts r  = strengthenUReft ts' (reftUReft r)
  where
    ts'        = foldl' (\a b -> RAppTy a b (uTop trueReft)) (RVar v (uTop trueReft)) ts

strengthenUReft
  :: BareTypeParsed -> UReftV LocSymbol (ReftV LocSymbol) -> BareTypeParsed
strengthenUReft = strengthenWith meetUReft
  where
    meetUReft (MkUReft r0 (Pr p0)) (MkUReft r1 (Pr p1)) =
       MkUReft (meetReftV r0 r1) (Pr $ p0 <> p1)

    meetReftV :: ReftV LocSymbol -> ReftV LocSymbol -> ReftV LocSymbol
    meetReftV (Reft (v, ra)) (Reft (v', ra'))
      | v == v'          = Reft (v , pAnd [ra, ra'])
      | v == dummySymbol = Reft (v', pAnd [ra', substExprV val (Su $ M.fromList [(v , EVar (dummyLoc v'))]) ra])
      | otherwise        = Reft (v , pAnd [ra, substExprV val (Su $ M.fromList [(v', EVar (dummyLoc v))]) ra'])

substExprV :: (v -> Symbol) -> SubstV v -> ExprV v -> ExprV v
substExprV toSym su0 = go
  where
    go (EApp f e) = EApp (go f) (go e)
    go (ELam x e) = ELam x (substExprV toSym (removeSubst su0 (fst x)) e)
    go (ECoerc a t e) = ECoerc a t (go e)
    go (ENeg e) = ENeg (go e)
    go (EBin op e1 e2) = EBin op (go e1) (go e2)
    go (EIte p e1 e2) = EIte (go p) (go e1) (go e2)
    go (ECst e so) = ECst (go e) so
    go (EVar x) = appSubst su0 x
    go (PAnd ps) = PAnd $ map go ps
    go (POr  ps) = POr $ map go ps
    go (PNot p) = PNot (go p)
    go (PImp p1 p2) = PImp (go p1) (go p2)
    go (PIff p1 p2) = PIff (go p1) (go p2)
    go (PAtom r e1 e2) = PAtom r (go e1) (go e2)
    go (PKVar k su') = PKVar k $ su' `appendSubst` su0
    go (PGrad k su' i e) = PGrad k (su' `appendSubst` su0) i (go e)
    go (PAll _ _) = panic Nothing "substExprV: PAll"
    go (PExist _ _) = panic Nothing "substExprV: PExist"
    go p = p

    appSubst (Su s) x = Mb.fromMaybe (EVar x) (M.lookup (toSym x) s)

    removeSubst (Su su) x = Su $ M.delete x su

    appendSubst (Su s1) θ2@(Su s2) = Su $ M.union s1' s2
      where
        s1' = substExprV toSym θ2 <$> s1


reftUReft :: r -> UReftV v r
reftUReft r    = MkUReft r (Pr [])

predUReft :: PredicateV v -> UReftV v (ReftV v)
predUReft = MkUReft trueReft

dummyTyId :: String
dummyTyId = ""

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

-- | The AST for a single parsed spec.
data BPspec
  = Meas    (MeasureV LocSymbol LocBareTypeParsed (Located LHName)) -- ^ 'measure' definition
  | Assm    (Located LHName, LocBareTypeParsed)              -- ^ 'assume' signature (unchecked)
  | AssmReflect (Located LHName, Located LHName)             -- ^ 'assume reflects' signature (unchecked)
  | Asrt    (Located LHName, LocBareTypeParsed)              -- ^ 'assert' signature (checked)
  | Asrts   ([Located LHName], (LocBareTypeParsed, Maybe [Located (ExprV LocSymbol)])) -- ^ sym0, ..., symn :: ty / [m0,..., mn]
  | DDecl   DataDeclParsed                                -- ^ refined 'data'    declaration
  | NTDecl  DataDeclParsed                                -- ^ refined 'newtype' declaration
  | Relational (Located LHName, Located LHName, LocBareTypeParsed, LocBareTypeParsed, RelExprV LocSymbol, RelExprV LocSymbol) -- ^ relational signature
  | AssmRel (Located LHName, Located LHName, LocBareTypeParsed, LocBareTypeParsed, RelExprV LocSymbol, RelExprV LocSymbol) -- ^ 'assume' relational signature
  | Class   (RClass LocBareTypeParsed)                    -- ^ refined 'class' definition
  | RInst   (RInstance LocBareTypeParsed)                 -- ^ refined 'instance' definition
  | Invt    LocBareTypeParsed                             -- ^ 'invariant' specification
  | Using  (LocBareTypeParsed, LocBareTypeParsed)         -- ^ 'using' declaration (for local invariants on a type)
  | Alias   (Located (RTAlias Symbol BareTypeParsed))     -- ^ 'type' alias declaration
  | EAlias  (Located (RTAlias Symbol (ExprV LocSymbol)))  -- ^ 'predicate' alias declaration
  | Embed   (Located LHName, FTycon, TCArgs)              -- ^ 'embed' declaration
  | Qualif  (QualifierV LocSymbol)                        -- ^ 'qualif' definition
  | LVars   (Located LHName)                              -- ^ 'lazyvar' annotation, defer checks to *use* sites
  | Lazy    (Located LHName)                              -- ^ 'lazy' annotation, skip termination check on binder
  | Fail    (Located LHName)                              -- ^ 'fail' annotation, the binder should be unsafe
  | Rewrite (Located LHName)                              -- ^ 'rewrite' annotation, the binder generates a rewrite rule
  | Rewritewith (Located LHName, [Located LHName])        -- ^ 'rewritewith' annotation, the first binder is using the rewrite rules of the second list,
  | Insts   (Located LHName)                              -- ^ 'auto-inst' or 'ple' annotation; use ple locally on binder
  | HMeas   (Located LHName)                              -- ^ 'measure' annotation; lift Haskell binder as measure
  | Reflect (Located LHName)                              -- ^ 'reflect' annotation; reflect Haskell binder as function in logic
  | PrivateReflect LocSymbol                              -- ^ 'private-reflect' annotation
  | OpaqueReflect (Located LHName)                        -- ^ 'opaque-reflect' annotation
  | Inline  (Located LHName)                              -- ^ 'inline' annotation;  inline (non-recursive) binder as an alias
  | Ignore  (Located LHName)                              -- ^ 'ignore' annotation; skip all checks inside this binder
  | ASize   (Located LHName)                              -- ^ 'autosize' annotation; automatically generate size metric for this type
  | PBound  (Bound LocBareTypeParsed (ExprV LocSymbol))   -- ^ 'bound' definition
  | Pragma  (Located String)                              -- ^ 'LIQUID' pragma, used to save configuration options in source files
  | CMeas   (MeasureV LocSymbol LocBareTypeParsed ())     -- ^ 'class measure' definition
  | IMeas   (MeasureV LocSymbol LocBareTypeParsed (Located LHName)) -- ^ 'instance measure' definition
  | Varia   (Located LHName, [Variance])                  -- ^ 'variance' annotations, marking type constructor params as co-, contra-, or in-variant
  | DSize   ([LocBareTypeParsed], LocSymbol)              -- ^ 'data size' annotations, generating fancy termination metric
  | BFix    ()                                            -- ^ fixity annotation
  | Define  (Located LHName, ([Symbol], ExprV LocSymbol)) -- ^ 'define' annotation for specifying logic aliases
  deriving (Data, Typeable)

instance PPrint BPspec where
  pprintTidy = ppPspec

splice :: PJ.Doc -> [PJ.Doc] -> PJ.Doc
splice sep = PJ.hcat . PJ.punctuate sep

ppAsserts :: (PPrint t) => Tidy -> [Located LHName] -> t -> Maybe [Located (ExprV LocSymbol)] -> PJ.Doc
ppAsserts k lxs t mles
  = PJ.hcat [ splice ", " (map (pprintTidy k . val) lxs)
            , " :: "
            , pprintTidy k t
            , ppLes mles
            ]
  where
    ppLes Nothing    = ""
    ppLes (Just les) = "/" <+> pprintTidy k (fmap val . val <$> les)

pprintSymbolWithParens :: LHName -> PJ.Doc
pprintSymbolWithParens lhname =
    case symbolString $ getLHNameSymbol lhname of
      n@(c:_) | not (Char.isAlpha c) -> "(" <> PJ.text n <> ")"
      n -> PJ.text n

ppPspec :: Tidy -> BPspec -> PJ.Doc
ppPspec k (Meas m)
  = "measure" <+> pprintTidy k (val <$> unLocMeasureV m)
ppPspec k (Assm (lx, t))
  = "assume"  <+> pprintSymbolWithParens (val lx) <+> "::" <+> pprintTidy k (parsedToBareType <$> t)
ppPspec k (AssmReflect (lx, ly))
  = "assume reflect"  <+> pprintTidy k (val lx) <+> "as" <+> pprintTidy k (val ly)
ppPspec k (Asrt (lx, t))
  = "assert"  <+> pprintTidy k (val lx) <+> "::" <+> pprintTidy k (parsedToBareType <$> t)
ppPspec k (Asrts (lxs, (t, les)))
  = ppAsserts k lxs (parsedToBareType <$> t) les
ppPspec k (DDecl d)
  = pprintTidy k (parsedToBareType <$> mapDataDeclV val d)
ppPspec k (NTDecl d)
  = "newtype" <+> pprintTidy k (parsedToBareType <$> mapDataDeclV val d)
ppPspec k (Invt t)
  = "invariant" <+> pprintTidy k (parsedToBareType <$> t)
ppPspec k (Using (t1, t2))
  = "using" <+> pprintTidy k (parsedToBareType <$> t1) <+> "as" <+> pprintTidy k (parsedToBareType <$> t2)
ppPspec k (Alias   (Loc _ _ rta))
  = "type" <+> pprintTidy k (fmap parsedToBareType rta)
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
ppPspec k (Insts   lx)
  = "automatic-instances" <+> pprintTidy k (val lx)
ppPspec k (HMeas   lx)
  = "measure" <+> pprintTidy k (val lx)
ppPspec k (Reflect lx)
  = "reflect" <+> pprintTidy k (val lx)
ppPspec k (PrivateReflect lx)
  = "private-reflect" <+> pprintTidy k (val lx)
ppPspec k (OpaqueReflect lx)
  = "opaque-reflect" <+> pprintTidy k (val lx)
ppPspec k (Inline  lx)
  = "inline" <+> pprintTidy k (val lx)
ppPspec k (Ignore  lx)
  = "ignore" <+> pprintTidy k (val lx)
ppPspec k (ASize   lx)
  = "autosize" <+> pprintTidy k (val lx)
ppPspec k (PBound  bnd)
  = pprintTidy k $ mapBoundTy (fmap parsedToBareType) bnd
ppPspec _ (Pragma  (Loc _ _ s))
  = "LIQUID" <+> PJ.text s
ppPspec k (CMeas   m)
  = "class measure" <+> pprintTidy k (unLocMeasureV m)
ppPspec k (IMeas   m)
  = "instance measure" <+> pprintTidy k (val <$> unLocMeasureV m)
ppPspec k (Class   cls)
  = pprintTidy k $ fmap (fmap parsedToBareType) cls
ppPspec k (RInst   inst)
  = pprintTidy k $ fmap (fmap parsedToBareType) inst
ppPspec k (Varia   (lx, vs))
  = "data variance" <+> pprintTidy k (val lx) <+> splice " " (pprintTidy k <$> vs)
ppPspec k (DSize   (ds, ss))
  = "data size" <+> splice " " (pprintTidy k <$> map (fmap parsedToBareType) ds) <+> pprintTidy k (val ss)
ppPspec _ (BFix    _)           --
  = "fixity"
ppPspec k (Define  (lx, (ys, e)))
  = "define" <+> pprintTidy k (val lx) <+> " " <+> pprintTidy k ys <+> "=" <+> pprintTidy k e
ppPspec k (Relational (lxl, lxr, tl, tr, q, p))
  = "relational"
        <+> pprintTidy k (val lxl) <+> "::" <+> pprintTidy k (parsedToBareType <$> tl) <+> "~"
        <+> pprintTidy k (val lxr) <+> "::" <+> pprintTidy k (parsedToBareType <$> tr) <+> "|"
        <+> pprintTidy k (fmap val q) <+> "=>" <+> pprintTidy k (fmap val p)
ppPspec k (AssmRel (lxl, lxr, tl, tr, q, p))
  = "assume relational"
        <+> pprintTidy k (val lxl) <+> "::" <+> pprintTidy k (parsedToBareType <$> tl) <+> "~"
        <+> pprintTidy k (val lxr) <+> "::" <+> pprintTidy k (parsedToBareType <$> tr) <+> "|"
        <+> pprintTidy k (fmap val q) <+> "=>" <+> pprintTidy k (fmap val p)

unLocMeasureV :: MeasureV LocSymbol LocBareTypeParsed v -> MeasureV Symbol LocBareType v
unLocMeasureV = mapMeasureV val . mapMeasureTy (fmap parsedToBareType)

-- | For debugging
{-instance Show (Pspec a b) where
  show (Meas   _) = "Meas"
  show (Assm   _) = "Assm"
  show (Asrt   _) = "Asrt"
  show (Asrts  _) = "Asrts"
  show (Impt   _) = "Impt"
  shcl  _) = "DDecl"
  show (NTDecl _) = "NTDecl"
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
  show (Reflect _) = "Reflect"
  show (HMeas  _) = "HMeas"
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
mkSpec :: [BPspec] -> Measure.Spec LocSymbol BareTypeParsed
mkSpec xs = Measure.Spec
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.asmSigs    = [a | Assm   a <- xs]
  , Measure.asmReflectSigs = [(l, r) | AssmReflect (l, r) <- xs]
  , Measure.sigs       = [a | Asrt   a <- xs]
                      ++ [(y, t) | Asrts (ys, (t, _)) <- xs, y <- ys]
  , Measure.expSigs    = []
  , Measure.invariants = [(Nothing, t) | Invt   t <- xs]
  , Measure.ialiases   = [t | Using t <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs] ++ [d | NTDecl d <- xs]
  , Measure.newtyDecls = [d | NTDecl d <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.ealiases   = [e | EAlias e <- xs]
  , Measure.embeds     = tceFromList [(c, (fTyconSort tc, a)) | Embed (c, tc, a) <- xs]
  , Measure.qualifiers = [q | Qualif q <- xs]
  , Measure.lvars      = S.fromList [d | LVars d  <- xs]
  , Measure.autois     = S.fromList [s | Insts s <- xs]
  , Measure.pragmas    = [s | Pragma s <- xs]
  , Measure.cmeasures  = [m | CMeas  m <- xs]
  , Measure.imeasures  = [m | IMeas  m <- xs]
  , Measure.omeasures  = []
  , Measure.classes    = [c | Class  c <- xs]
  , Measure.relational = [r | Relational r <- xs]
  , Measure.asmRel     = [r | AssmRel r <- xs]
  , Measure.dvariance  = [v | Varia  v <- xs]
  , Measure.dsize      = [v | DSize  v <- xs]
  , Measure.rinstance  = [i | RInst  i <- xs]
  , Measure.termexprs  = [(y, es) | Asrts (ys, (_, Just es)) <- xs, y <- ys]
  , Measure.lazy       = S.fromList [s | Lazy   s <- xs]
  , Measure.fails      = S.fromList [s | Fail   s <- xs]
  , Measure.rewrites   = S.fromList [s | Rewrite s <- xs]
  , Measure.rewriteWith = M.fromList [s | Rewritewith s <- xs]
  , Measure.bounds     = M.fromList [(bname i, i) | PBound i <- xs]
  , Measure.reflects   = S.fromList [s | Reflect s <- xs]
  , Measure.privateReflects = S.fromList [s | PrivateReflect s <- xs]
  , Measure.opaqueReflects = S.fromList [s | OpaqueReflect s <- xs]
  , Measure.hmeas      = S.fromList [s | HMeas  s <- xs]
  , Measure.inlines    = S.fromList [s | Inline s <- xs]
  , Measure.ignores    = S.fromList [s | Ignore s <- xs]
  , Measure.autosize   = S.fromList [s | ASize  s <- xs]
  , Measure.axeqs      = []
  , Measure.defines    = [ toLMapV d | Define d <- xs]
  , Measure.usedDataCons = mempty
  }

-- | Parse a single top level liquid specification
specP :: Parser BPspec
specP
  = fallbackSpecP "assume" ((reserved "reflect" >> fmap AssmReflect assmReflectBindP)
        <|> (reserved "relational" >>  fmap AssmRel relationalP)
        <|>                            fmap Assm   tyBindLHNameP  )
    <|> fallbackSpecP "assert"      (fmap Asrt    tyBindLocalLHNameP)
    <|> fallbackSpecP "autosize"    (fmap ASize   tyConBindLHNameP)

    -- TODO: These next two are synonyms, kill one
    <|> fallbackSpecP "axiomatize"  (fmap Reflect locBinderLHNameP)
    <|> fallbackSpecP "reflect"     (fmap Reflect locBinderLHNameP)
    <|> (reserved "private-reflect" >> fmap PrivateReflect axiomP  )
    <|> (reserved "opaque-reflect" >> fmap OpaqueReflect locBinderLHNameP  )

    <|> fallbackSpecP "define"  logDefineP
    <|> fallbackSpecP "measure" hmeasureP

    <|> (reserved "infixl"        >> fmap BFix    infixlP  )
    <|> (reserved "infixr"        >> fmap BFix    infixrP  )
    <|> (reserved "infix"         >> fmap BFix    infixP   )
    <|> fallbackSpecP "inline"      (fmap Inline locBinderThisModuleLHNameP)
    <|> fallbackSpecP "ignore"      (fmap Ignore  locBinderThisModuleLHNameP)

    <|> fallbackSpecP "bound"       (fmap PBound  boundP)
    <|> (reserved "class"
         >> ((reserved "measure"  >> fmap CMeas  cMeasureP )
         <|> fmap Class  classP                            ))
    <|> (reserved "instance"
         >> ((reserved "measure"  >> fmap IMeas  iMeasureP )
         <|> fmap RInst  instanceP ))

    <|> (reserved "data"
        >> ((reserved "variance"  >> fmap Varia  datavarianceP)
        <|> (reserved "size"      >> fmap DSize  dsizeP)
        <|> fmap DDecl  dataDeclP ))
    <|> (reserved "newtype"       >> fmap NTDecl dataDeclP )
    <|> (reserved "relational"    >> fmap Relational relationalP )
    <|> fallbackSpecP "invariant"   (fmap Invt   invariantP)
    <|> (reserved "using"          >> fmap Using invaliasP )
    <|> (reserved "type"          >> fmap Alias  aliasP    )

    -- TODO: Next two are basically synonyms
    <|> fallbackSpecP "predicate"   (fmap EAlias ealiasP   )
    <|> fallbackSpecP "expression"  (fmap EAlias ealiasP   )

    <|> fallbackSpecP "embed"       (fmap Embed  embedP    )
    <|> fallbackSpecP "qualif"      (fmap Qualif (qualifierP sortP))
    <|> (reserved "lazyvar"       >> fmap LVars  locBinderThisModuleLHNameP)

    <|> (reserved "lazy"          >> fmap Lazy   locBinderLHNameP)
    <|> (reserved "rewrite"       >> fmap Rewrite locBinderLHNameP)
    <|> (reserved "rewriteWith"   >> fmap Rewritewith   rewriteWithP )
    <|> (reserved "fail"          >> fmap Fail locBinderThisModuleLHNameP )
    <|> (reserved "ple"           >> fmap Insts locBinderThisModuleLHNameP  )
    <|> (reserved "automatic-instances" >> fmap Insts locBinderThisModuleLHNameP  )
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
  p <|> fmap Asrts (tyBindsRemP (Loc l1 l2 (makeUnresolvedLHName (LHVarName LHThisModuleNameF) (symbol kw))))

-- | Same as tyBindsP, except the single initial symbol has already been matched
tyBindsRemP
  :: Located LHName
  -> Parser ([Located LHName], (Located BareTypeParsed, Maybe [Located (ExprV LocSymbol)]))
tyBindsRemP sy = do
  reservedOp "::"
  tb <- termBareTypeP
  return ([sy],tb)

pragmaP :: Parser (Located String)
pragmaP = locStringLiteral

rewriteWithP :: Parser (Located LHName, [Located LHName])
rewriteWithP = (,) <$> locBinderLHNameP <*> brackets (sepBy1 locBinderLHNameP comma)

axiomP :: Parser LocSymbol
axiomP = locBinderP

datavarianceP :: Parser (Located LHName, [Variance])
datavarianceP = liftM2 (,) (locUpperIdLHNameP LHTcName) (many varianceP)

dsizeP :: Parser ([Located BareTypeParsed], Located Symbol)
dsizeP = liftM2 (,) (parens $ sepBy (located genBareTypeP) comma) locBinderP


varianceP :: Parser Variance
varianceP = (reserved "bivariant"     >> return Bivariant)
        <|> (reserved "invariant"     >> return Invariant)
        <|> (reserved "covariant"     >> return Covariant)
        <|> (reserved "contravariant" >> return Contravariant)
        <?> "Invalid variance annotation\t Use one of bivariant, invariant, covariant, contravariant"

tyBindsP :: Parser ([Located LHName], (Located BareTypeParsed, Maybe [Located (ExprV LocSymbol)]))
tyBindsP =
  xyP (sepBy1 locBinderThisModuleLHNameP comma) (reservedOp "::") termBareTypeP

tyBindNoLocP :: Parser (LocSymbol, BareTypeParsed)
tyBindNoLocP = second val <$> tyBindP

-- | Parses a type signature as it occurs in "assume" and "assert" directives.
tyBindP :: Parser (LocSymbol, Located BareTypeParsed)
tyBindP =
  (,) <$> locBinderP <* reservedOp "::" <*> located genBareTypeP

tyBindLogicNameP :: Parser (Located LHName, Located BareTypeParsed)
tyBindLogicNameP =
  (,) <$> locBinderLogicNameP <* reservedOp "::" <*> located genBareTypeP

tyBindLHNameP :: Parser (Located LHName, Located BareTypeParsed)
tyBindLHNameP = do
    x <- locBinderLHNameP
    _ <- reservedOp "::"
    t <- located genBareTypeP
    return (x, t)

tyBindLocalLHNameP :: Parser (Located LHName, Located BareTypeParsed)
tyBindLocalLHNameP = do
    x <- locBinderThisModuleLHNameP
    _ <- reservedOp "::"
    t <- located genBareTypeP
    return (x, t)

-- | Parses a loc symbol.
assmReflectBindP :: Parser (Located LHName, Located LHName)
assmReflectBindP =
  (,) <$> locBinderLHNameP <* reservedOp "as" <*> locBinderLHNameP

termBareTypeP :: Parser (Located BareTypeParsed, Maybe [Located (ExprV LocSymbol)])
termBareTypeP = do
  t <- located genBareTypeP
  termTypeP t <|> return (t, Nothing)

termTypeP :: Located BareTypeParsed -> Parser (Located BareTypeParsed, Maybe [Located (ExprV LocSymbol)])
termTypeP t
  = do
       reservedOp "/"
       es <- brackets $ sepBy (located exprP) comma
       return (t, Just es)

-- -------------------------------------

invariantP :: Parser (Located BareTypeParsed)
invariantP = located genBareTypeP

invaliasP :: Parser (Located BareTypeParsed, Located BareTypeParsed)
invaliasP
  = do t  <- located genBareTypeP
       reserved "as"
       ta <- located genBareTypeP
       return (t, ta)

genBareTypeP :: Parser BareTypeParsed
genBareTypeP = bareTypeP

embedP :: Parser (Located LHName, FTycon, TCArgs)
embedP = do
  x <- locUpperIdLHNameP LHTcName
  a <- try (reserved "*" >> return WithArgs) <|> return NoArgs -- TODO: reserved "*" looks suspicious
  _ <- reserved "as"
  t <- fTyConP
  return (x, t, a)
  --  = xyP locUpperIdP symbolTCArgs (reserved "as") fTyConP


aliasP :: Parser (Located (RTAlias Symbol BareTypeParsed))
aliasP  = rtAliasP id     bareTypeP <?> "aliasP"

ealiasP :: Parser (Located (RTAlias Symbol (ExprV LocSymbol)))
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

logDefineP :: Parser BPspec
logDefineP =
    do s <- locBinderLHNameP
       args <- many locSymbolP
       reservedOp "="
       e <- exprP <|> predP
       return (Define (s, (val <$> args, e)))

hmeasureP :: Parser BPspec
hmeasureP = do
  setLayout
  do b <- try (locBinderLogicNameP <* reservedOp "::")
     ty <- located genBareTypeP
     popLayout >> popLayout
     eqns <- block $ try $ measureDefP LHLogicNameBinder (rawBodyP <|> tyBodyP ty)
     return (Meas $ Measure.mkM b ty eqns MsMeasure mempty)
    <|>
   do b <- locBinderLHNameP
      popLayout >> popLayout >> return (HMeas b)

iMeasureP :: Parser (MeasureV LocSymbol (Located BareTypeParsed) (Located LHName))
iMeasureP = do
  (x, ty) <- indentedLine tyBindP
  _ <- optional semi
  eqns    <- block $ measureDefP LHLogicName (rawBodyP <|> tyBodyP ty)
  return   $ Measure.mkM (makeUnresolvedLHName LHLogicName <$> x) ty eqns MsMeasure mempty

-- | class measure
cMeasureP :: Parser (MeasureV LocSymbol (Located BareTypeParsed) ())
cMeasureP
  = do (x, ty) <- tyBindLogicNameP
       return $ Measure.mkM x ty [] MsClass mempty

oneClassArg :: Parser [Located BareTypeParsed]
oneClassArg
  = sing <$> located (rit <$> classBTyConP <*> (map val <$> classParams))
  where
    rit t as    = RApp t ((`RVar` trueURef) <$> as) [] trueURef
    classParams =  (reserved "where" >> return [])
               <|> ((:) <$> ((\ls -> bTyVar ls <$ ls) <$> locLowerIdP) <*> classParams)
    sing x      = [x]


superP :: Parser (Located BareTypeParsed)
superP = located (toRCls <$> bareAtomBindP)
  where toRCls x = x

instanceP :: Parser (RInstance (Located BareTypeParsed))
instanceP
  = do _    <- supersP
       c    <- classBTyConP
       tvs  <- try oneClassArg <|> manyTill iargsP (try $ reserved "where")
       ms   <- block riMethodSigP
       return $ RI c Nothing tvs ms
  where
    supersP  = try ((parens (superP `sepBy1` comma) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []

    iargsP   =   (mkVar . bTyVar <$> located tyVarIdP)
            <|> parens (located bareTypeP)


    mkVar v  = dummyLoc $ RVar v (uTop trueReft)


riMethodSigP :: Parser (Located LHName, RISig (Located BareTypeParsed))
riMethodSigP
  = try (do reserved "assume"
            (x, t) <- tyBindLHNameP
            return (x, RIAssumed t) )
 <|> do (x, t) <- tyBindLHNameP
        return (x, RISig t)
 <?> "riMethodSigP"

classP :: Parser (RClass (Located BareTypeParsed))
classP
  = do sups <- supersP
       c    <- classBTyConP
       tvs  <- manyTill (bTyVar <$> located tyVarIdP) (try $ reserved "where")
       ms   <- block tyBindLHNameP -- <|> sepBy tyBindP semi
       return $ RClass c sups tvs ms
  where
    supersP  = try ((parens (superP `sepBy1` comma) <|> fmap pure superP)
                       <* reservedOp "=>")
               <|> return []

rawBodyP :: Parser (BodyV LocSymbol)
rawBodyP
  = braces $ do
      v <- symbolP
      reservedOp "|"
      R v <$> predP

tyBodyP :: Located BareTypeParsed -> Parser (BodyV LocSymbol)
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

locBinderLogicNameP :: Parser (Located LHName)
locBinderLogicNameP =
  fmap (makeUnresolvedLHName LHLogicNameBinder) <$> located binderP

locBinderLHNameP :: Parser (Located LHName)
locBinderLHNameP =
  located $ makeUnresolvedLHName (LHVarName LHAnyModuleNameF) <$> binderP

locBinderThisModuleLHNameP :: Parser (Located LHName)
locBinderThisModuleLHNameP =
  located $ makeUnresolvedLHName (LHVarName LHThisModuleNameF) <$> binderP

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
      parens infixBinderIdP
  <|> binderIdP
  -- Note: It is important that we do *not* use the LH/fixpoint reserved words here,
  -- because, for example, we must be able to use "assert" as an identifier.

measureDefP :: LHNameSpace -> Parser (BodyV LocSymbol) -> Parser (DefV LocSymbol (Located BareTypeParsed) (Located LHName))
measureDefP ns bodyP
  = do mname   <- fmap (makeUnresolvedLHName ns) <$> locSymbolP
       (c, xs) <- measurePatP
       reservedOp "="
       body    <- bodyP
       let xs'  = symbol . val <$> xs
       return   $ Def mname c Nothing ((, Nothing) <$> xs') body

measurePatP :: Parser (Located LHName, [LocSymbol])
measurePatP
  =  parens (try conPatP <|> try consPatP <|> nilPatP <|> tupPatP)
 <|> nullaryConPatP
 <?> "measurePatP"

tupPatP :: Parser (Located LHName, [Located Symbol])
tupPatP  = mkTupPat  <$> located (sepBy1 locLowerIdP comma)

conPatP :: Parser (Located LHName, [Located Symbol])
conPatP  = (,)       <$> dataConLHNameP <*> many locLowerIdP

consPatP :: Parser (Located LHName, [Located Symbol])
consPatP = mkConsPat <$> locLowerIdP  <*> located (reservedOp ":") <*> locLowerIdP

nilPatP :: Parser (Located LHName, [t])
nilPatP  = mkNilPat  <$> located (brackets (pure ()))

nullaryConPatP :: Parser (Located LHName, [t])
nullaryConPatP = nilPatP <|> ((,[]) <$> dataConLHNameP)
                 <?> "nullaryConPatP"

mkTupPat :: Foldable t => Located (t a) -> (Located LHName, t a)
mkTupPat lzs =
    let tupledDC = GHC.tupleDataCon GHC.Boxed (length (val lzs))
     in (makeGHCLHName (GHC.getName tupledDC) (symbol tupledDC) <$ lzs, val lzs)

mkNilPat :: Located t -> (Located LHName, [t1])
mkNilPat lx     = (makeGHCLHName (GHC.getName GHC.nilDataCon) (symbol GHC.nilDataCon) <$ lx, [])

mkConsPat :: t1 -> Located t -> t1 -> (Located LHName, [t1])
mkConsPat x lc y = (makeGHCLHName (GHC.getName GHC.consDataCon) (symbol GHC.consDataCon) <$ lc, [x, y])

-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP :: Parser [(LHName, BareTypeParsed)]
dataConFieldsP
   = map (first (makeUnresolvedLHName LHLogicNameBinder)) <$>
     (explicitCommaBlock predTypeDDP -- braces (sepBy predTypeDDP comma)
       <|> many dataConFieldP
       <?> "dataConFieldP"
     )

dataConFieldP :: Parser (Symbol, BareTypeParsed)
dataConFieldP
   =  parens (try predTypeDDP <|> dbTypeP)
  <|> dbTyArgP -- unparenthesised constructor fields must be "atomic"
  <?> "dataConFieldP"
  where
    dbTypeP = (,) <$> dummyBindP <*> bareTypeP
    dbTyArgP = (,) <$> dummyBindP <*> bareTyArgP

predTypeDDP :: Parser (Symbol, BareTypeParsed)
predTypeDDP = (,) <$> bbindP <*> bareTypeP

bbindP   :: Parser Symbol
bbindP   = lowerIdP <* reservedOp "::"

tyConBindLHNameP :: Parser (Located LHName)
tyConBindLHNameP = locUpperIdLHNameP LHTcName

dataConP :: [Symbol] -> Parser DataCtorParsed
dataConP as = do
  x   <- dataConLHNameP
  xts <- dataConFieldsP
  return $ DataCtor x as [] xts Nothing

adtDataConP :: [Symbol] -> Parser DataCtorParsed
adtDataConP as = do
  x     <- dataConLHNameP
  reservedOp "::"
  tr    <- toRTypeRep <$> bareTypeP
  return $ DataCtor x (tRepVars as tr) [] (tRepFields tr) (Just $ ty_res tr)

tRepVars :: Symbolic a => [Symbol] -> RTypeRepV v c a r -> [Symbol]
tRepVars as tr = case fst <$> ty_vars tr of
  [] -> as
  vs -> symbol . ty_var_value <$> vs

tRepFields :: RTypeRepV v c tv r -> [(LHName, RTypeV v c tv r)]
tRepFields tr = zip (map (makeUnresolvedLHName LHLogicNameBinder) $ ty_binds tr) (ty_args tr)

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
     pwr s  = symbol s

dataConLHNameP :: Parser (Located LHName)
dataConLHNameP = fmap (makeUnresolvedLHName (LHDataConName LHAnyModuleNameF)) <$> dataConNameP

dataSizeP :: Parser (Maybe (SizeFunV LocSymbol))
dataSizeP
  = brackets (Just . SymSizeFun <$> located locLowerIdP)
  <|> return Nothing

relationalP :: Parser (Located LHName, Located LHName, LocBareTypeParsed, LocBareTypeParsed, RelExprV LocSymbol, RelExprV LocSymbol)
relationalP = do
   x <- locBinderLHNameP
   reserved "~"
   y <- locBinderLHNameP
   reserved "::"
   braces $ do
    tx <- located genBareTypeP
    reserved "~"
    ty <- located genBareTypeP
    reserved "|"
    assm <- try (relrefaP <* reserved "|-") <|> return (ERBasic PTrue)
    ex <- relrefaP
    return (x,y,tx,ty,assm,ex)

dataDeclP :: Parser DataDeclParsed
dataDeclP = do
  pos <- getSourcePos
  x   <- locUpperOrInfixIdP
  fsize <- dataSizeP
  dataDeclBodyP pos x fsize <|> return (emptyDecl x pos fsize)

emptyDecl :: LocSymbol -> SourcePos -> Maybe (SizeFunV LocSymbol) -> DataDeclParsed
emptyDecl x pos fsize@(Just _)
  = DataDecl (DnName $ makeUnresolvedLHName LHTcName <$> x) [] [] Nothing pos fsize Nothing DataUser
emptyDecl x pos _
  = uError (ErrBadData (sourcePosSrcSpan pos) (pprint (val x)) msg)
  where
    msg = "You should specify either a default [size] or one or more fields in the data declaration"

dataDeclBodyP :: SourcePos -> LocSymbol -> Maybe (SizeFunV LocSymbol) -> Parser DataDeclParsed
dataDeclBodyP pos x fsize = do
  vanilla    <- null <$> many locUpperIdP
  as         <- many noWhere -- TODO: check this again
  ps         <- predVarDefsP
  (pTy, dcs) <- dataCtorsP as
  let dn      = dataDeclName pos x vanilla dcs
  return      $ DataDecl dn as ps (Just dcs) pos fsize pTy DataUser

dataDeclName :: SourcePos -> LocSymbol -> Bool -> [DataCtorParsed] -> DataName
dataDeclName _ x True  _     = DnName $ makeUnresolvedLHName LHTcName <$> x  -- vanilla data    declaration
dataDeclName _ _ False (d:_) = DnCon  $ dcName d                             -- family instance declaration
dataDeclName p x _  _        = uError (ErrBadData (sourcePosSrcSpan p) (pprint (val x)) msg)
  where
    msg                  = "You should specify at least one data constructor for a family instance"

-- | Parse the constructors of a datatype, allowing both classic and GADT-style syntax.
--
-- Note that as of 2020-10-14, we changed the syntax of GADT-style datatype declarations
-- to match Haskell more closely and parse all constructors in a layout-sensitive block,
-- whereas before we required them to be separated by @|@.
--
dataCtorsP :: [Symbol] -> Parser (Maybe BareTypeParsed, [DataCtorParsed])
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

dataPropTyP :: Parser (Maybe BareTypeParsed)
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
