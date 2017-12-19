{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TupleSections    #-}

-- | This module contains (most of) the code needed to lift Haskell entitites,
--   . code- (CoreBind), and data- (Tycon) definitions into the spec level.

module Language.Haskell.Liquid.Bare.Measure
  ( makeHaskellDataDecls
  , makeHaskellMeasures
  , makeHaskellInlines
  , makeHaskellBounds
  , makeMeasureSpec
  , makeMeasureSpec'
  , makeClassMeasureSpec
  , makeMeasureSelectors
  , strengthenHaskellMeasures
  , strengthenHaskellInlines
  , varMeasures
  ) where

import CoreSyn
import DataCon
import TyCon
import Id
import Type hiding (isFunTy)
-- import qualified Type
import Var

import Data.Default
-- import Data.Either (either)
import Prelude hiding (mapM, error)
import Control.Monad hiding (forM, mapM)
import Control.Monad.Except hiding (forM, mapM)
import Control.Monad.State hiding (forM, mapM)
import Data.Bifunctor
import Data.Maybe
import Data.Char (toUpper)

import TysWiredIn (boolTyCon) -- , wiredInTyCons)

import Data.Traversable (forM, mapM)
import Text.PrettyPrint.HughesPJ (text)
import Text.Parsec.Pos (SourcePos)

import qualified Data.List as L

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Fixpoint.Misc (mlookup, sortNub, groupList, mapSnd, mapFst)
import Language.Fixpoint.Types (Symbol, dummySymbol, symbolString, symbol, Expr(..), meet)
import Language.Fixpoint.SortCheck (isFirstOrder)

import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Language.Haskell.Liquid.Misc
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure       as Ms
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Misc       (simpleSymbolVar, hasBoolResult, makeDataConChecker, makeDataConSelector)
import           Language.Haskell.Liquid.Bare.Expand
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Bare.OfType
import           Language.Haskell.Liquid.Bare.Resolve
import           Language.Haskell.Liquid.Bare.ToBare

--------------------------------------------------------------------------------
makeHaskellDataDecls :: Config -> Ms.BareSpec -> [TyCon] -> [DataDecl]
--------------------------------------------------------------------------------
makeHaskellDataDecls cfg spec tcs
  | exactDC cfg = mapMaybe tyConDataDecl
                . zipMap   (hasDataDecl spec . fst)
                . liftableTyCons
                . filter isReflectableTyCon
                $ tcs
  | otherwise   = []


isReflectableTyCon :: TyCon -> Bool
isReflectableTyCon  = isFamInstTyCon .||. isVanillaAlgTyCon

liftableTyCons :: [TyCon] -> [(TyCon, DataName)]
liftableTyCons = F.notracepp "LiftableTCs 3"
               . zipMapMaybe (tyConDataName True)
               . F.notracepp "LiftableTCs 2"
               . filter   (not . isBoxedTupleTyCon)
               . F.notracepp "LiftableTCs 1"
               -- . (`sortDiff` wiredInTyCons)
               -- . F.tracepp "LiftableTCs 0"

zipMap :: (a -> b) -> [a] -> [(a, b)]
zipMap f xs = zip xs (map f xs)

zipMapMaybe :: (a -> Maybe b) -> [a] -> [(a, b)]
zipMapMaybe f = mapMaybe (\x -> (x, ) <$> f x)

hasDataDecl :: Ms.BareSpec -> TyCon -> HasDataDecl
hasDataDecl spec = \tc -> M.lookupDefault def (tcName tc) decls
  where
    def          = NoDecl Nothing
    tcName       = tyConDataName False
    decls        = M.fromList [ (Just (tycName d), hasDecl d) | d <- Ms.dataDecls spec ]

{-tyConDataDecl :: {tc:TyCon | isAlgTyCon tc} -> Maybe DataDecl @-}
tyConDataDecl :: ((TyCon, DataName), HasDataDecl) -> Maybe DataDecl
tyConDataDecl (_, HasDecl)
  = Nothing
tyConDataDecl ((tc, dn), NoDecl szF)
  = Just $ D
      { tycName   = dn
      , tycTyVars = symbol <$> GM.tyConTyVarsDef tc
      , tycPVars  = []
      , tycTyLabs = []
      , tycDCons  = F.notracepp ("tyConDataDecl-DECLS: tc = " ++ show tc) $ decls tc
      , tycSrcPos = GM.getSourcePos tc
      , tycSFun   = szF
      , tycPropTy = Nothing
      , tycKind   = DataReflected
      }
      where decls = map dataConDecl . tyConDataCons

tyConDataName :: Bool -> TyCon -> Maybe DataName
tyConDataName full tc
  | vanillaTc  = Just (DnName ((post . symbol) <$> GM.locNamedThing tc))
  | d:_ <- dcs = Just (DnCon  ((post . symbol) <$> GM.locNamedThing d ))
  | otherwise  = Nothing
  where
    post       = if full then id else GM.dropModuleNamesAndUnique
    vanillaTc  = isVanillaAlgTyCon tc
    dcs        = F.notracepp msg $ tyConDataCons tc
    msg        = "tyConDataCons tc = " ++ F.showpp tc

dataConDecl :: DataCon -> DataCtor
dataConDecl d  = DataCtor dx xts Nothing
  where
    xts        = [(makeDataConSelector Nothing d i, RT.bareOfType t) | (i, t) <- its ]
    dx         = symbol <$> GM.locNamedThing d
    its        = zip [1..] ts
    (_,_,ts,_) = dataConSig d

--------------------------------------------------------------------------------
makeHaskellMeasures :: F.TCEmb TyCon -> [CoreBind] -> Ms.BareSpec
                    -> BareM [Measure (Located BareType) LocSymbol]
--------------------------------------------------------------------------------
makeHaskellMeasures tce cbs spec = do
    lmap <- gets logicEnv
    dm   <- gets dcEnv
    ms   <- mapM (makeMeasureDefinition tce lmap dm cbs') (S.toList $ Ms.hmeas spec)
    return (measureToBare <$> ms)
  where
    cbs'                  = concatMap unrec cbs
    unrec cb@(NonRec _ _) = [cb]
    unrec (Rec xes)       = [NonRec x e | (x, e) <- xes]

--------------------------------------------------------------------------------
makeHaskellInlines :: F.TCEmb TyCon -> [CoreBind] -> Ms.BareSpec
                   -> BareM [(LocSymbol, LMap)]
--------------------------------------------------------------------------------
makeHaskellInlines tce cbs spec = do
  lmap <- gets logicEnv
  mapM (makeMeasureInline tce lmap cbs') (S.toList $ Ms.inlines spec)
  where
    cbs'                  = concatMap unrec cbs
    unrec cb@(NonRec _ _) = [cb]
    unrec (Rec xes)       = [NonRec x e | (x, e) <- xes]

--------------------------------------------------------------------------------
makeMeasureInline :: F.TCEmb TyCon -> LogicMap -> [CoreBind] ->  LocSymbol
                  -> BareM (LocSymbol, LMap)
--------------------------------------------------------------------------------
makeMeasureInline tce lmap cbs x = maybe err chomp $ GM.findVarDef (val x) cbs
  where
    chomp (v, def)               = (vx, ) <$> coreToFun' tce lmap vx v def (ok vx)
                                      where vx = F.atLoc x (symbol v)
    err                          = throwError $ errHMeas x "Cannot inline haskell function"
    ok vx (xs, e)                = return (LMap vx (symbol <$> xs) (either id id e))

makeMeasureDefinition
  :: F.TCEmb TyCon -> LogicMap -> DataConMap -> [CoreBind] -> LocSymbol
  -> BareM (Measure LocSpecType DataCon)
makeMeasureDefinition tce lmap dm cbs x = maybe err chomp $ GM.findVarDef (val x) cbs
  where
    chomp (v, def)     = Ms.mkM vx (GM.varLocInfo logicType v) <$> coreToDef' vx v def
                         where vx = F.atLoc x (symbol v)
    coreToDef' x v def = case runToLogic tce lmap dm mkErr (coreToDef x v def) of
                           Right l -> return     l
                           Left e  -> throwError e

    mkErr :: String -> Error
    mkErr str = ErrHMeas (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)
    err       = throwError $ mkErr "Cannot extract measure from haskell function"

errHMeas :: LocSymbol -> String -> Error
errHMeas x str = ErrHMeas (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

strengthenHaskellInlines  :: S.HashSet (Located Var) -> [(Var, LocSpecType)] -> [(Var, LocSpecType)]
strengthenHaskellInlines  = strengthenHaskell strengthenResult

strengthenHaskellMeasures :: S.HashSet (Located Var) -> [(Var, LocSpecType)] -> [(Var, LocSpecType)]
strengthenHaskellMeasures = strengthenHaskell strengthenResult'

strengthenHaskell :: (Var -> SpecType) -> S.HashSet (Located Var) -> [(Var, LocSpecType)] -> [(Var, LocSpecType)]
strengthenHaskell strengthen hmeas sigs
  = go <$> groupList (reverse sigs ++ hsigs)
  where
    hsigs      = [(val x, x {val = strengthen $ val x}) | x <- S.toList hmeas]
    go (v, xs) = (v,) $ L.foldl1' (flip meetLoc) xs

meetLoc :: Located SpecType -> Located SpecType -> LocSpecType
meetLoc t1 t2 = t1 {val = val t1 `meet` val t2}

--------------------------------------------------------------------------------
-- | 'makeMeasureSelectors' converts the 'DataCon's and creates the measures for
--   the selectors and checkers that then enable reflection.
--------------------------------------------------------------------------------

makeMeasureSelectors :: Config -> DataConMap -> (DataCon, Located DataConP) -> [Measure SpecType DataCon]
makeMeasureSelectors cfg dm (dc, Loc l l' (DataConP _ _vs _ps _ _ xts _resTy isGadt _ _))
  = (condNull (exactDC cfg) $ checker : catMaybes (go' <$> fields)) --  internal measures, needed for reflection
 ++ (condNull (autofields)  $           catMaybes (go  <$> fields)) --  user-visible measures.
  where
    autofields = not (isGadt || noMeasureFields cfg)
    go ((x, t), i)
      -- do not make selectors for functional fields
      | isFunTy t && not (higherOrderFlag cfg)
      = Nothing
      | otherwise
      = Just $ makeMeasureSelector (Loc l l' x) (projT i) dc n i

    go' ((_,t), i)
      -- do not make selectors for functional fields
      | isFunTy t && not (higherOrderFlag cfg)
      = Nothing
      | otherwise
      = Just $ makeMeasureSelector (Loc l l' (makeDataConSelector (Just dm) dc i)) (projT i) dc n i

    fields   = zip (reverse xts) [1..]
    n        = length xts
    checker  = makeMeasureChecker (Loc l l' (makeDataConChecker dc)) checkT dc n
    projT i  = dataConSel dc n (Proj i)
    checkT   = dataConSel dc n Check

dataConSel :: DataCon -> Int -> DataConSel -> SpecType
dataConSel dc n Check    = mkArrow as [] [] [xt] bareBool
  where
    (as, _, xt)          = {- traceShow ("dataConSel: " ++ show dc) $ -} bkDataCon dc n

dataConSel dc n (Proj i) = mkArrow as [] [] [xt] (mempty <$> ti)
  where
    ti                   = fromMaybe err $ getNth (i-1) ts
    (as, ts, xt)         = {- F.tracepp ("bkDatacon dc = " ++ F.showpp (dc, n)) $ -} bkDataCon dc n
    err                  = panic Nothing $ "DataCon " ++ show dc ++ "does not have " ++ show i ++ " fields"

-- bkDataCon :: DataCon -> Int -> ([RTVar RTyVar RSort], [SpecType], (Symbol, SpecType, RReft))
bkDataCon :: (F.Reftable r) => DataCon -> Int -> ([RTVar RTyVar RSort], [RRType r], (Symbol, RRType r, r))
bkDataCon dc nFlds  = (as, ts, (dummySymbol, t, mempty))
  where
    ts                = RT.ofType <$> takeLast nFlds _ts
    t                 = {- traceShow ("bkDataConResult" ++ GM.showPpr (_t, t0)) $ -}
                        RT.ofType  $ mkTyConApp tc tArgs'
    as                = makeRTVar . RT.rTyVar <$> αs
    ((αs,_,_,_,_ts,_t), _t0) = hammer dc
    tArgs'            = take (nArgs - nVars) tArgs ++ (mkTyVarTy <$> αs)
    nVars             = length αs
    nArgs             = length tArgs
    (tc, tArgs)       = fromMaybe err (splitTyConApp_maybe _t)
    err               = GM.namedPanic dc ("Cannot split result type of DataCon " ++ show dc)
    hammer dc         = (dataConFullSig dc, Var.varType . dataConWorkId $ dc)

data DataConSel = Check | Proj Int

bareBool :: SpecType
bareBool = RApp (RTyCon boolTyCon [] def) [] [] mempty


{- | NOTE:Use DataconWorkId

      dcWorkId :: forall a1 ... aN. (a1 ~ X1 ...) => T1 -> ... -> Tn -> T
      checkT   :: forall as. T -> Bool
      projT t  :: forall as. T -> t

-}

makeMeasureSelector :: (Show a1)
                    => LocSymbol -> SpecType -> DataCon -> Int -> a1 -> Measure SpecType DataCon
makeMeasureSelector x s dc n i = M {name = x, sort = s, eqns = [eqn]}
  where
    eqn                        = Def x [] dc Nothing args (E (EVar $ mkx i))
    args                       = ((, Nothing) . mkx) <$> [1 .. n]
    mkx j                      = symbol ("xx" ++ show j)

makeMeasureChecker :: LocSymbol -> SpecType -> DataCon -> Int -> Measure SpecType DataCon
makeMeasureChecker x s0 dc n = M {name = x, sort = s, eqns = eqn : (eqns <$> filter (/= dc) dcs)}
  where
    s       = F.notracepp ("makeMeasureChecker: " ++ show x) s0
    eqn     = Def x [] dc Nothing (((, Nothing) . mkx) <$> [1 .. n])       (P F.PTrue)
    eqns d  = Def x [] d  Nothing (((, Nothing) . mkx) <$> [1 .. nArgs d]) (P F.PFalse)
    nArgs d = length (dataConOrigArgTys d)
    mkx j   = symbol ("xx" ++ show j)
    dcs     = tyConDataCons (dataConTyCon dc)

makeMeasureSpec :: (ModName, Ms.BareSpec) -> BareM (Ms.MSpec SpecType DataCon)
makeMeasureSpec (mod, spec) = inModule mod mkSpec
  where
    mkSpec = mkMeasureDCon =<< mkMeasureSort =<< first val <$> m
    m      = Ms.mkMSpec <$> mapM expandMeasure (Ms.measures spec)
                        <*> return (Ms.cmeasures spec)
                        <*> mapM expandMeasure (Ms.imeasures spec)

makeMeasureSpec' :: MSpec SpecType DataCon
                 -> ([(Var, SpecType)], [(LocSymbol, RRType F.Reft)])
makeMeasureSpec' = mapFst (mapSnd RT.uRType <$>) . Ms.dataConTypes . first (mapReft ur_reft)

makeClassMeasureSpec :: MSpec (RType c tv (UReft r2)) t
                     -> [(LocSymbol, CMeasure (RType c tv r2))]
makeClassMeasureSpec (Ms.MSpec {..}) = tx <$> M.elems cmeasMap
  where
    tx (M n s _) = (n, CM n (mapReft ur_reft s))


mkMeasureDCon :: Ms.MSpec t LocSymbol -> BareM (Ms.MSpec t DataCon)
mkMeasureDCon m
  = mkMeasureDCon_ m <$> forM (measureCtors m)
                           (\n -> (val n,) <$> lookupGhcDataCon n)

mkMeasureDCon_ :: Ms.MSpec t LocSymbol -> [(Symbol, DataCon)] -> Ms.MSpec t DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where
    m'                = fmap (tx.val) m
    cm'               = hashMapMapKeys (symbol . tx) $ Ms.ctorMap m'
    tx                = mlookup (M.fromList ndcs)

measureCtors ::  Ms.MSpec t LocSymbol -> [LocSymbol]
measureCtors = sortNub . fmap ctor . concat . M.elems . Ms.ctorMap

mkMeasureSort ::  Ms.MSpec BareType LocSymbol -> BareM (Ms.MSpec SpecType LocSymbol)
mkMeasureSort (Ms.MSpec c mm cm im)
  = Ms.MSpec <$> forM c (mapM txDef) <*> forM mm tx <*> forM cm tx <*> forM im tx
    where
      tx :: Measure BareType ctor -> BareM (Measure SpecType ctor)
      tx (M n s eqs) = M n <$> ofMeaSort s <*> mapM txDef eqs

      txDef :: Def BareType ctor -> BareM (Def SpecType ctor)
      txDef def = liftM3 (\xs t bds-> def{ dparams = xs, dsort = t, binds = bds})
                  (mapM (mapSndM ofMeaSort) (dparams def))
                  (mapM ofMeaSort $ dsort def)
                  (mapM (mapSndM $ mapM ofMeaSort) (binds def))


varMeasures :: (Monoid r) => [Var] -> [(Symbol, Located (RRType r))]
varMeasures vars = [ (symbol v, varSpecType v)  | v <- vars
                                                , GM.isDataConId v
                                                , isSimpleType $ varType v ]

isSimpleType :: Type -> Bool
isSimpleType = isFirstOrder . RT.typeSort M.empty

varSpecType :: (Monoid r) => Var -> Located (RRType r)
varSpecType = fmap (RT.ofType . varType) . GM.locNamedThing

makeHaskellBounds :: F.TCEmb TyCon -> CoreProgram -> S.HashSet (Var, LocSymbol) -> BareM RBEnv
makeHaskellBounds tce cbs xs = do
  lmap <- gets logicEnv
  M.fromList <$> mapM (makeHaskellBound tce lmap cbs) (S.toList xs)

makeHaskellBound :: F.TCEmb TyCon
                 -> LogicMap
                 -> [Bind Var]
                 -> (Var, Located Symbol)
                 -> BareM (LocSymbol, RBound)
makeHaskellBound tce lmap  cbs (v, x) =
  case filter ((v  `elem`) . GM.binders) cbs of
    (NonRec v def:_)   -> toBound v x <$> coreToFun' tce lmap x v def return
    (Rec [(v, def)]:_) -> toBound v x <$> coreToFun' tce lmap x v def return
    _                  -> throwError $ errHMeas x "Cannot make bound of haskell function"

coreToFun' :: F.TCEmb TyCon
           -> LogicMap
           -> LocSymbol
           -> Var
           -> CoreExpr
           -> (([Var], Either F.Expr F.Expr) -> BareM a)
           -> BareM a
coreToFun' tce lmap x v def ok = do
  dm <- gets dcEnv
  either throwError ok $ runToLogic tce lmap dm (errHMeas x) (coreToFun x v def)

toBound :: Var -> LocSymbol -> ([Var], Either F.Expr F.Expr) -> (LocSymbol, RBound)
toBound v x (vs, Left p) = (x', Bound x' fvs ps xs p)
  where
    x'         = capitalizeBound x
    (ps', xs') = L.partition (hasBoolResult . varType) vs
    (ps , xs)  = (txp <$> ps', txx <$> xs')
    txp v      = (dummyLoc $ simpleSymbolVar v, RT.ofType $ varType v)
    txx v      = (dummyLoc $ symbol v,          RT.ofType $ varType v)
    fvs        = (((`RVar` mempty) . RTV) <$> fst (splitForAllTys $ varType v)) :: [RSort]

toBound v x (vs, Right e) = toBound v x (vs, Left e)

capitalizeBound :: Located Symbol -> Located Symbol
capitalizeBound = fmap (symbol . toUpperHead . symbolString)
  where
    toUpperHead []     = []
    toUpperHead (x:xs) = toUpper x:xs

--------------------------------------------------------------------------------
-- | Expand Measures -----------------------------------------------------------
--------------------------------------------------------------------------------
type BareMeasure = Measure (Located BareType) LocSymbol

expandMeasure :: BareMeasure -> BareM BareMeasure
expandMeasure m = do
  eqns <- sequence $ expandMeasureDef <$> eqns m
  return $ m { sort = RT.generalize <$> sort m
             , eqns = eqns }

expandMeasureDef :: Def t LocSymbol -> BareM (Def t LocSymbol)
expandMeasureDef d
  = do body <- expandMeasureBody (loc $ measure d) $ body d
       return $ d { body = body }

expandMeasureBody :: SourcePos -> Body -> BareM Body
expandMeasureBody l (P p)   = P   <$> (resolve l =<< expand l p)
expandMeasureBody l (R x p) = R x <$> (resolve l =<< expand l p)
expandMeasureBody l (E e)   = E   <$> resolve l e
