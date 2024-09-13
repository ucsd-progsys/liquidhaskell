{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TupleSections    #-}

-- | This module contains (most of) the code needed to lift Haskell entitites,
--   . code- (CoreBind), and data- (Tycon) definitions into the spec level.

module Language.Haskell.Liquid.Bare.Measure
  ( makeHaskellMeasures
  , makeHaskellInlines
  , makeHaskellDataDecls
  , makeMeasureSelectors
  , makeMeasureSpec
  , makeMeasureSpec'
  , getLocReflects
  , makeOpaqueReflMeasures
  , getReflDCs
  , varMeasures
  , getMeasVars
  , makeClassMeasureSpec
  -- , makeHaskellBounds
  , varLocSym
  ) where

import Data.Default
import qualified Control.Exception as Ex
import Prelude hiding (mapM, error)
import Data.Bifunctor
import qualified Data.Maybe as Mb
import Text.PrettyPrint.HughesPJ (text)
-- import Text.Printf     (printf)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import           Language.Fixpoint.SortCheck (isFirstOrder)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import qualified Language.Fixpoint.Misc                as Misc
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Haskell.Liquid.Misc             ((.||.))
import qualified Liquid.GHC.API       as Ghc
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types
-- import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure       as Ms

import qualified Language.Haskell.Liquid.Bare.Types    as Bare
import qualified Language.Haskell.Liquid.Bare.Resolve  as Bare
import qualified Language.Haskell.Liquid.Bare.Expand   as Bare
import qualified Language.Haskell.Liquid.Bare.DataType as Bare
import qualified Language.Haskell.Liquid.Bare.ToBare   as Bare
import Control.Monad (mapM)
import qualified GHC.List as L

--------------------------------------------------------------------------------
makeHaskellMeasures :: Bool -> GhcSrc -> Bare.TycEnv -> LogicMap -> Ms.BareSpec
                    -> [Measure (Located BareType) LocSymbol]
--------------------------------------------------------------------------------
makeHaskellMeasures allowTC src tycEnv lmap spec
          = Bare.measureToBare <$> ms
  where
    ms    = makeMeasureDefinition allowTC tycEnv lmap cbs <$> mSyms
    cbs   = nonRecCoreBinds   (_giCbs src)
    mSyms = S.toList (Ms.hmeas spec)

makeMeasureDefinition :: Bool -> Bare.TycEnv -> LogicMap -> [Ghc.CoreBind] -> LocSymbol
                      -> Measure LocSpecType Ghc.DataCon
makeMeasureDefinition allowTC tycEnv lmap cbs x =
  case GM.findVarDef (val x) cbs of
    Nothing        -> Ex.throw $ errHMeas x "Cannot extract measure from haskell function"
    Just (v, cexp) -> Ms.mkM vx vinfo mdef MsLifted (makeUnSorted allowTC (Ghc.varType v) mdef)
                     where
                       vx           = F.atLoc x (F.symbol v)
                       mdef         = coreToDef' allowTC tycEnv lmap vx v cexp
                       vinfo        = GM.varLocInfo (logicType allowTC) v

makeUnSorted :: Bool -> Ghc.Type -> [Def LocSpecType Ghc.DataCon] -> UnSortedExprs
makeUnSorted allowTC ty defs
  | isMeasureType ta
  = mempty
  | otherwise
  = map defToUnSortedExpr defs
  where
    ta = go $ Ghc.expandTypeSynonyms ty

    go (Ghc.ForAllTy _ t) = go t
    go Ghc.FunTy{ Ghc.ft_arg = p, Ghc.ft_res = t} | isErasable p = go t
    go Ghc.FunTy{ Ghc.ft_arg = t } = t
    go t                  = t -- this should never happen!

    isMeasureType (Ghc.TyConApp _ ts) = all Ghc.isTyVarTy ts
    isMeasureType _                   = False

    defToUnSortedExpr defn = (xx:(fst <$> binds defn),
                             Ms.bodyPred (F.mkEApp (measure defn) [F.expr xx]) (body defn))

    xx = F.vv $ Just 10000
    isErasable = if allowTC then GM.isEmbeddedDictType else Ghc.isClassPred

coreToDef' :: Bool -> Bare.TycEnv -> LogicMap -> LocSymbol -> Ghc.Var -> Ghc.CoreExpr
           -> [Def LocSpecType Ghc.DataCon]
coreToDef' allowTC tycEnv lmap vx v defn =
  case runToLogic embs lmap dm (errHMeas vx) (coreToDef allowTC vx v defn) of
    Right l -> l
    Left e  -> Ex.throw e
  where
    embs    = Bare.tcEmbs       tycEnv
    dm      = Bare.tcDataConMap tycEnv

errHMeas :: LocSymbol -> String -> Error
errHMeas x str = ErrHMeas (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

--------------------------------------------------------------------------------
makeHaskellInlines :: Bool -> GhcSrc -> F.TCEmb Ghc.TyCon -> LogicMap -> Ms.BareSpec
                   -> [(LocSymbol, LMap)]
--------------------------------------------------------------------------------
makeHaskellInlines allowTC src embs lmap spec
         = makeMeasureInline allowTC embs lmap cbs <$> inls
  where
    cbs  = nonRecCoreBinds (_giCbs src)
    inls = S.toList        (Ms.inlines spec)

makeMeasureInline :: Bool -> F.TCEmb Ghc.TyCon -> LogicMap -> [Ghc.CoreBind] -> LocSymbol
                  -> (LocSymbol, LMap)
makeMeasureInline allowTC embs lmap cbs x =
  case GM.findVarDef (val x) cbs of
    Nothing        -> Ex.throw $ errHMeas x "Cannot inline haskell function"
    Just (v, defn) -> (vx, coreToFun' allowTC embs Nothing lmap vx v defn ok)
                     where
                       vx         = F.atLoc x (F.symbol v)
                       ok (xs, e) = LMap vx (F.symbol <$> xs) (either id id e)

-- | @coreToFun'@ takes a @Maybe DataConMap@: we need a proper map when lifting
--   measures and reflects (which have case-of, and hence, need the projection symbols),
--   but NOT when lifting inlines (which do not have case-of).
--   For details, see [NOTE:Lifting-Stages]

coreToFun' :: Bool -> F.TCEmb Ghc.TyCon -> Maybe Bare.DataConMap -> LogicMap -> LocSymbol -> Ghc.Var -> Ghc.CoreExpr
           -> (([Ghc.Var], Either F.Expr F.Expr) -> a) -> a
coreToFun' allowTC embs dmMb lmap x v defn ok = either Ex.throw ok act
  where
    act  = runToLogic embs lmap dm err xFun
    xFun = coreToFun allowTC x v defn
    err  = errHMeas x
    dm   = Mb.fromMaybe mempty dmMb


nonRecCoreBinds :: [Ghc.CoreBind] -> [Ghc.CoreBind]
nonRecCoreBinds            = concatMap go
  where
    go cb@(Ghc.NonRec _ _) = [cb]
    go    (Ghc.Rec xes)    = [Ghc.NonRec x e | (x, e) <- xes]

-------------------------------------------------------------------------------
makeHaskellDataDecls :: Config -> ModName -> Ms.BareSpec -> [Ghc.TyCon]
                     -> [DataDecl]
--------------------------------------------------------------------------------
makeHaskellDataDecls cfg name spec tcs
  | exactDCFlag cfg = Bare.dataDeclSize spec
                    . Mb.mapMaybe tyConDataDecl
                    -- . F.tracepp "makeHaskellDataDecls-3"
                    . zipMap   (hasDataDecl name spec . fst)
                    -- . F.tracepp "makeHaskellDataDecls-2"
                    . liftableTyCons
                    -- . F.tracepp "makeHaskellDataDecls-1"
                    . filter isReflectableTyCon
                    $ tcs
  | otherwise       = []


isReflectableTyCon :: Ghc.TyCon -> Bool
isReflectableTyCon  = Ghc.isFamInstTyCon .||. Ghc.isVanillaAlgTyCon

liftableTyCons :: [Ghc.TyCon] -> [(Ghc.TyCon, DataName)]
liftableTyCons
  = F.notracepp "LiftableTCs 3"
  . zipMapMaybe (tyConDataName True)
  . F.notracepp "LiftableTCs 2"
  . filter   (not . Ghc.isBoxedTupleTyCon)
  . F.notracepp "LiftableTCs 1"
  -- . (`sortDiff` wiredInTyCons)
  -- . F.tracepp "LiftableTCs 0"

zipMap :: (a -> b) -> [a] -> [(a, b)]
zipMap f xs = zip xs (map f xs)

zipMapMaybe :: (a -> Maybe b) -> [a] -> [(a, b)]
zipMapMaybe f = Mb.mapMaybe (\x -> (x, ) <$> f x)

hasDataDecl :: ModName -> Ms.BareSpec -> Ghc.TyCon -> HasDataDecl
hasDataDecl modName spec
                 = \tc -> F.notracepp (msg tc) $ M.lookupDefault defn (tcName tc) decls
  where
    msg tc       = "hasDataDecl " ++ show (tcName tc)
    defn         = NoDecl Nothing
    tcName       = fmap (qualifiedDataName modName) . tyConDataName True
    dcName       =       qualifiedDataName modName  . tycName
    decls        = M.fromList [ (Just dn, hasDecl d)
                                | d     <- Ms.dataDecls spec
                                , let dn = dcName d]

qualifiedDataName :: ModName -> DataName -> DataName
qualifiedDataName modName (DnName lx) = DnName (qualifyModName modName <$> lx)
qualifiedDataName modName (DnCon  lx) = DnCon  (qualifyModName modName <$> lx)

{-tyConDataDecl :: {tc:TyCon | isAlgTyCon tc} -> Maybe DataDecl @-}
tyConDataDecl :: ((Ghc.TyCon, DataName), HasDataDecl) -> Maybe DataDecl
tyConDataDecl (_, HasDecl)
  = Nothing
tyConDataDecl ((tc, dn), NoDecl szF)
  = Just $ DataDecl
      { tycName   = dn
      , tycTyVars = F.symbol <$> GM.tyConTyVarsDef tc
      , tycPVars  = []
      , tycDCons  = Just (decls tc)
      , tycSrcPos = GM.getSourcePos tc
      , tycSFun   = szF
      , tycPropTy = Nothing
      , tycKind   = DataReflected
      }
      where decls = map dataConDecl . Ghc.tyConDataCons

tyConDataName :: Bool -> Ghc.TyCon -> Maybe DataName
tyConDataName full tc
  | vanillaTc  = Just (DnName (post . F.symbol <$> GM.locNamedThing tc))
  | d:_ <- dcs = Just (DnCon  (post . F.symbol <$> GM.locNamedThing d ))
  | otherwise  = Nothing
  where
    post       = if full then id else GM.dropModuleNamesAndUnique
    vanillaTc  = Ghc.isVanillaAlgTyCon tc
    dcs        = Misc.sortOn F.symbol (Ghc.tyConDataCons tc)

dataConDecl :: Ghc.DataCon -> DataCtor
dataConDecl d     = {- F.notracepp msg $ -} DataCtor dx (F.symbol <$> as) [] xts outT
  where
    isGadt        = not (Ghc.isVanillaDataCon d)
    -- msg           = printf "dataConDecl (gadt = %s)" (show isGadt)
    xts           = [(Bare.makeDataConSelector Nothing d i, RT.bareOfType t) | (i, t) <- its ]
    dx            = F.symbol <$> GM.locNamedThing d
    its           = zip [1..] ts
    (as,_ps,ts,ty)  = Ghc.dataConSig d
    outT          = Just (RT.bareOfType ty :: BareType)
    _outT :: Maybe BareType
    _outT
      | isGadt    = Just (RT.bareOfType ty)
      | otherwise = Nothing





--------------------------------------------------------------------------------
-- | 'makeMeasureSelectors' converts the 'DataCon's and creates the measures for
--   the selectors and checkers that then enable reflection.
--------------------------------------------------------------------------------

makeMeasureSelectors :: Config -> Bare.DataConMap -> Located DataConP -> [Measure SpecType Ghc.DataCon]
makeMeasureSelectors cfg dm (Loc l l' c)
  = Misc.condNull (exactDCFlag cfg) (checker : Mb.mapMaybe go' fields) --  internal measures, needed for reflection
 ++ Misc.condNull autofields (Mb.mapMaybe go fields) --  user-visible measures.
  where
    dc         = dcpCon    c
    isGadt     = dcpIsGadt c
    xts        = dcpTyArgs c
    autofields = not isGadt
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
      = Just $ makeMeasureSelector (Loc l l' (Bare.makeDataConSelector (Just dm) dc i)) (projT i) dc n i

    fields   = zip (reverse xts) [1..]
    n        = length xts
    checker  = makeMeasureChecker (Loc l l' (Bare.makeDataConChecker dc)) checkT dc n
    projT i  = dataConSel permitTC dc n (Proj i)
    checkT   = dataConSel permitTC dc n Check
    permitTC = typeclass cfg

dataConSel :: Bool -> Ghc.DataCon -> Int -> DataConSel -> SpecType
dataConSel permitTC dc n Check    = mkArrow (map (, mempty) as) [] [xt] bareBool
  where
    (as, _, xt)          = {- traceShow ("dataConSel: " ++ show dc) $ -} bkDataCon permitTC dc n

dataConSel permitTC dc n (Proj i) = mkArrow (map (, mempty) as) [] [xt] (mempty <$> ti)
  where
    ti                   = Mb.fromMaybe err $ Misc.getNth (i-1) ts
    (as, ts, xt)         = {- F.tracepp ("bkDatacon dc = " ++ F.showpp (dc, n)) $ -} bkDataCon permitTC dc n
    err                  = panic Nothing $ "DataCon " ++ show dc ++ "does not have " ++ show i ++ " fields"

-- bkDataCon :: DataCon -> Int -> ([RTVar RTyVar RSort], [SpecType], (Symbol, SpecType, RReft))
bkDataCon :: (F.Reftable (RTProp RTyCon RTyVar r), PPrint r, F.Reftable r) => Bool -> Ghc.DataCon -> Int -> ([RTVar RTyVar RSort], [RRType r], (F.Symbol, RFInfo, RRType r, r))
bkDataCon permitTC dcn nFlds  = (as, ts, (F.dummySymbol, classRFInfo permitTC, t, mempty))
  where
    ts                = RT.ofType <$> Misc.takeLast nFlds (map Ghc.irrelevantMult _ts)
    t                 = -- Misc.traceShow ("bkDataConResult" ++ GM.showPpr (dc, _t, _t0)) $
                          RT.ofType  $ Ghc.mkTyConApp tc tArgs'
    as                = makeRTVar . RT.rTyVar <$> (αs ++ αs')
    ((αs,αs',_,_,_ts,_t), _t0) = hammer dcn
    tArgs'            = take (nArgs - nVars) tArgs ++ (Ghc.mkTyVarTy <$> αs)
    nVars             = length αs
    nArgs             = length tArgs
    (tc, tArgs)       = Mb.fromMaybe err (Ghc.splitTyConApp_maybe _t)
    err               = GM.namedPanic dcn ("Cannot split result type of DataCon " ++ show dcn)
    hammer dc         = (Ghc.dataConFullSig dc, Ghc.varType . Ghc.dataConWorkId $ dc)

data DataConSel = Check | Proj Int

bareBool :: SpecType
bareBool = RApp (RTyCon Ghc.boolTyCon [] def) [] [] mempty


{- | NOTE:Use DataconWorkId

      dcWorkId :: forall a1 ... aN. (a1 ~ X1 ...) => T1 -> ... -> Tn -> T
      checkT   :: forall as. T -> Bool
      projT t  :: forall as. T -> t

-}

makeMeasureSelector :: (Show a1) => LocSymbol -> SpecType -> Ghc.DataCon -> Int -> a1 -> Measure SpecType Ghc.DataCon
makeMeasureSelector x s dc n i = M { msName = x, msSort = s, msEqns = [eqn], msKind = MsSelector, msUnSorted = mempty}
  where
    eqn                        = Def x dc Nothing args (E (F.EVar $ mkx i))
    args                       = (, Nothing) . mkx <$> [1 .. n]
    mkx j                      = F.symbol ("xx" ++ show j)

makeMeasureChecker :: LocSymbol -> SpecType -> Ghc.DataCon -> Int -> Measure SpecType Ghc.DataCon
makeMeasureChecker x s0 dc n = M { msName = x, msSort = s, msEqns = eqn : (eqns <$> filter (/= dc) dcs), msKind = MsChecker, msUnSorted = mempty }
  where
    s       = F.notracepp ("makeMeasureChecker: " ++ show x) s0
    eqn     = Def x dc Nothing ((, Nothing) . mkx <$> [1 .. n])       (P F.PTrue)
    eqns d  = Def x d  Nothing ((, Nothing) . mkx <$> [1 .. nArgs d]) (P F.PFalse)
    nArgs d = length (Ghc.dataConOrigArgTys d)
    mkx j   = F.symbol ("xx" ++ show j)
    dcs     = Ghc.tyConDataCons (Ghc.dataConTyCon dc)


----------------------------------------------------------------------------------------------
makeMeasureSpec' :: Bool -> MSpec SpecType Ghc.DataCon -> ([(Ghc.Var, SpecType)], [(LocSymbol, RRType F.Reft)])
----------------------------------------------------------------------------------------------
makeMeasureSpec' allowTC mspec0 = (ctorTys, measTys)
  where
    ctorTys             = Misc.mapSnd RT.uRType <$> ctorTys0
    (ctorTys0, measTys) = Ms.dataConTypes allowTC mspec
    mspec               = first (mapReft ur_reft) mspec0

----------------------------------------------------------------------------------------------
makeMeasureSpec :: Bare.Env -> Bare.SigEnv -> ModName -> (ModName, Ms.BareSpec) ->
                   Bare.Lookup (Ms.MSpec SpecType Ghc.DataCon)
----------------------------------------------------------------------------------------------
makeMeasureSpec env sigEnv myName (name, spec)
  = mkMeasureDCon env               name
  . mkMeasureSort env               name
  . first val
  . bareMSpec     env sigEnv myName name
  $ spec

--- Returns all the reflected symbols.
--- If Env is provided, the symbols are qualified using the environment.
getLocReflects :: Maybe Bare.Env -> Bare.ModSpecs -> S.HashSet F.LocSymbol
getLocReflects mbEnv = S.unions . fmap (uncurry $ names mbEnv) . M.toList
  where
    names (Just env) modName modSpec = Bare.qualifyLocSymbolTop env modName `S.map` unqualified modSpec
    names Nothing _ modSpec = unqualified modSpec
    unqualified modSpec = S.unions
      [ Ms.reflects modSpec
      , S.fromList (snd <$> Ms.asmReflectSigs modSpec)
      , S.fromList (fst <$> Ms.asmReflectSigs modSpec)
      , Ms.inlines modSpec, Ms.hmeas modSpec
      ]

-- Get all the symbols that are defined in the logic, based on the environment and the specs.
-- Also, fully qualify the defined symbols by the way (for those for which it's possible and not already done).
getDefinedSymbolsInLogic :: Bare.Env -> Bare.MeasEnv -> Bare.ModSpecs -> S.HashSet F.LocSymbol
getDefinedSymbolsInLogic env measEnv specs = 
  S.unions (uncurry getFromAxioms <$> specsList) -- reflections that ended up in equations
    `S.union` getLocReflects (Just env) specs -- reflected symbols
    `S.union` measVars -- Get the data constructors, ex. for Lit00.0
    `S.union` S.unions (uncurry getDataDecls <$> specsList) -- get the Predicated type defs, ex. for T1669.CSemigroup
    `S.union` S.unions (getAliases . snd <$> specsList) -- aliases, ex. for T1738Lib.incr
  where
    specsList = M.toList specs
    getFromAxioms modName spec = S.fromList $
      Bare.qualifyLocSymbolTop env modName . localize . F.eqName <$> Ms.axeqs spec
    measVars     = S.fromList $ localize . fst <$> getMeasVars env measEnv
    getDataDecls modName spec = S.unions $
      getFromDataCtor modName <$>
        concat (tycDCons `Mb.mapMaybe` (dataDecls spec ++ newtyDecls spec))
    getFromDataCtor modName decl = S.fromList $
      Bare.qualifyLocSymbolTop env modName <$>
        (dcName decl : (localize . fst <$> dcFields decl))
    getAliases spec = S.fromList $ fmap rtName <$> Ms.ealiases spec
    localize :: F.Symbol -> F.LocSymbol
    localize sym = maybe (dummyLoc sym) varLocSym $ L.lookup sym (Bare.reSyms env)

-- Get the set of `DataCon`s (DCs) needed for the reflection of a given list of variables,
-- and which are not already present in the logic
getReflDCs :: Bare.MeasEnv -> [Ghc.Var] -> S.HashSet Ghc.DataCon
getReflDCs measEnv vars = dcsUndefinedInLogic
  where
    -- List of wired DCs that cannot be found in the measure environment as they are
    -- eliminated in the translation from core.
    -- Written as a list of symbols because that's easier than trying to get the corresponding DCs from GHC.
    wired = S.fromList $ F.symbol <$> ["GHC.Types.True", "GHC.Types.False", "GHC.Types.I#"]
    notWired dc = not $ GM.qualifiedNameSymbol (Ghc.getName dc) `S.member` wired
    -- Undefined ones are those that are not already defined in the measure environement and are not wired
    dcsUndefinedInLogic = S.filter notWired $ allDCInUnfoldings `S.difference` definedDCs
    -- Get the defined DataCons from the measure environement
    definedDCs = S.fromList $ (GM.idDataConM . fst) `Mb.mapMaybe` Bare.meDataCons measEnv
    allDCInUnfoldings = getDCsOfUnfoldingOfVars vars

----------------------------------------------------
-- Looks at the given list of equations and finds any undefined symbol in the logic,
-- for which we need to introduce an opaque reflection.
-- Returns the corresponding measures. Second part of the returned tuple is the information to save
-- to the `meOpaqueRefl` field of the measure environment.
makeOpaqueReflMeasures :: Bare.Env -> Bare.MeasEnv -> Bare.ModSpecs ->
              [(Ghc.Var, LocSpecType, F.Equation)] ->
              ([MSpec SpecType Ghc.DataCon], [(Ghc.Var, Measure LocBareType ctor)])
makeOpaqueReflMeasures env measEnv specs eqs =
  unzip $ createMeasureForVar <$> S.toList (varsUndefinedInLogic `S.union` requestedOpaqueRefl)
  where
    -- Get the set of variables for the requested opaque reflections
    requestedOpaqueRefl = S.unions
      . fmap (uncurry (S.map . getVar) . second Ms.opaqueReflects)
      . M.toList $ specs
    getVar name sym = case Bare.lookupGhcVar env name "opaque-reflection" sym of
      Right x -> x
      Left _ -> Ex.throw $ mkError sym $ "Not in scope: " ++ show (val sym)
    definedSymbols = getDefinedSymbolsInLogic env measEnv specs
    undefinedInLogic v = not (S.member (varLocSym v) definedSymbols)
    -- Variables to consider
    varsUndefinedInLogic = S.unions $
      S.filter undefinedInLogic .
      (\(v, _, eq) -> getFreeVarsOfReflectionOfVar v eq) <$> eqs
    -- Main function: creates a (dummy) measure about a given variable
    createMeasureForVar :: Ghc.Var -> (MSpec SpecType Ghc.DataCon, (Ghc.Var, Measure LocBareType ctor))
    createMeasureForVar var =
      (Ms.mkMSpec' [smeas], (var, bmeas))
      where
        locSym = F.atLoc (loc specType) (F.symbol var)
        specType = varSpecType var
        bareType = varBareType var
        bmeas = M locSym bareType [] MsReflect []
        smeas = M locSym (val specType) [] MsReflect []

mkError :: LocSymbol -> String -> Error
mkError x str = ErrHMeas (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

getUnfoldingOfVar :: Ghc.Var -> Maybe Ghc.CoreExpr
getUnfoldingOfVar = getExpr . Ghc.realUnfoldingInfo . Ghc.idInfo
  where
    getExpr :: Ghc.Unfolding -> Maybe Ghc.CoreExpr
    getExpr (Ghc.CoreUnfolding expr _ _ _ _) = Just expr
    getExpr _ = Nothing

-- Get the set of "free" symbols in the (reflection of the) unfolding of a given variable.
-- Free symbols are those that are not already in the logic and that appear in
-- the reflection of the unfolding.
-- For this purpose, you need to give the variable naming the definition to reflect
-- and its corresponding equation in the logic.
getFreeVarsOfReflectionOfVar  :: Ghc.Var -> F.Equation -> S.HashSet Ghc.Var
getFreeVarsOfReflectionOfVar var eq = 
    S.filter (\v -> F.symbol v `S.member` freeSymbolsInReflectedBody) freeVarsInCoreExpr
  where
    reflExpr = getUnfoldingOfVar var
    getAllFreeVars = Ghc.exprSomeFreeVarsList (const True)
    freeVarsInCoreExpr = maybe S.empty (S.fromList . getAllFreeVars) reflExpr
    freeSymbolsInReflectedBody = F.exprSymbolsSet (F.eqBody eq)

-- Collect all the DataCon that appear in the unfolding of a given variable.
getDCsOfUnfoldingOfVars :: [Ghc.Var] -> S.HashSet Ghc.DataCon
getDCsOfUnfoldingOfVars vars = S.unions $ collectDataCons <$> getUnfoldingOfVar `Mb.mapMaybe` vars

-- Collect all DataCon that occur in case split alternatives of an expression
collectDataCons :: Ghc.CoreExpr -> S.HashSet Ghc.DataCon
collectDataCons expr = go expr S.empty
  where
    go (Ghc.Var _) acc = acc
    go (Ghc.Lit _) acc = acc
    go (Ghc.App f e) acc = go f (go e acc)
    go (Ghc.Lam _ e) acc = go e acc
    go (Ghc.Let bind e) acc = go e (goBind bind acc)
    go (Ghc.Case e _ _ alts) acc = foldr goAlt (go e acc) alts
    go (Ghc.Cast e _) acc = go e acc
    go (Ghc.Tick _ e) acc = go e acc
    go (Ghc.Type _) acc = acc
    go (Ghc.Coercion _) acc = acc

    -- Special auxiliary function for `Alt` which is precisely where we get the datacons
    goAlt (Ghc.Alt (Ghc.DataAlt dc) _ e) acc = S.insert dc (go e acc)
    goAlt (Ghc.Alt _ _ e) acc = go e acc

    goBind (Ghc.NonRec _ e) acc = go e acc
    goBind (Ghc.Rec binds) acc = foldr (go . snd) acc binds

bareMSpec :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> Ms.BareSpec -> Ms.MSpec LocBareType LocSymbol
bareMSpec env sigEnv myName name spec = Ms.mkMSpec ms cms ims oms
  where
    cms        = F.notracepp "CMS" $ filter inScope1 $             Ms.cmeasures spec
    ms         = F.notracepp "UMS" $ filter inScope2 $ expMeas <$> Ms.measures  spec
    ims        = F.notracepp "IMS" $ filter inScope2 $ expMeas <$> Ms.imeasures spec
    oms        = F.notracepp "OMS" $ filter inScope2 $ expMeas <$> Ms.omeasures spec
    expMeas    = expandMeasure env name  rtEnv
    rtEnv      = Bare.sigRTEnv          sigEnv
    force      = name == myName
    inScope1 z = F.notracepp ("inScope1: " ++ F.showpp (msName z)) (force ||  okSort z)
    inScope2 z = F.notracepp ("inScope2: " ++ F.showpp (msName z)) (force || (okSort z && okCtors z))
    okSort     = Bare.knownGhcType env name . msSort
    okCtors    = all (Bare.knownGhcDataCon env name . ctor) . msEqns

mkMeasureDCon :: Bare.Env -> ModName -> Ms.MSpec t LocSymbol -> Bare.Lookup (Ms.MSpec t Ghc.DataCon)
mkMeasureDCon env name m = do
  let ns = measureCtors m
  dcs   <- mapM (Bare.lookupGhcDataCon env name "measure-datacon") ns
  return $ mkMeasureDCon_ m (zip (val <$> ns) dcs)

-- mkMeasureDCon env name m = mkMeasureDCon_ m [ (val n, symDC n) | n <- measureCtors m ]
--   where
--     symDC                = Bare.lookupGhcDataCon env name "measure-datacon"

mkMeasureDCon_ :: Ms.MSpec t LocSymbol -> [(F.Symbol, Ghc.DataCon)] -> Ms.MSpec t Ghc.DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where
    m'                = fmap (tx.val) m
    cm'               = Misc.hashMapMapKeys (F.symbol . tx) $ Ms.ctorMap m'
    tx                = Misc.mlookup (M.fromList ndcs)

measureCtors ::  Ms.MSpec t LocSymbol -> [LocSymbol]
measureCtors = Misc.sortNub . fmap ctor . concat . M.elems . Ms.ctorMap

mkMeasureSort :: Bare.Env -> ModName -> Ms.MSpec BareType LocSymbol
              -> Ms.MSpec SpecType LocSymbol
mkMeasureSort env name (Ms.MSpec c mm cm im) =
  Ms.MSpec (map txDef <$> c) (tx <$> mm) (tx <$> cm) (tx <$> im)
    where
      ofMeaSort :: F.SourcePos -> BareType -> SpecType
      ofMeaSort l = Bare.ofBareType env name l Nothing

      tx :: Measure BareType ctor -> Measure SpecType ctor
      tx (M n s eqs k u) = M n (ofMeaSort l s) (txDef <$> eqs) k u where l = GM.fSourcePos n

      txDef :: Def BareType ctor -> Def SpecType ctor
      txDef d = first (ofMeaSort l) d                              where l = GM.fSourcePos (measure d)



--------------------------------------------------------------------------------
-- | Expand Measures -----------------------------------------------------------
--------------------------------------------------------------------------------
-- type BareMeasure = Measure LocBareType LocSymbol

expandMeasure :: Bare.Env -> ModName -> BareRTEnv -> BareMeasure -> BareMeasure
expandMeasure env name rtEnv m = m
  { msSort = RT.generalize                   <$> msSort m
  , msEqns = expandMeasureDef env name rtEnv <$> msEqns m
  }

expandMeasureDef :: Bare.Env -> ModName -> BareRTEnv -> Def t LocSymbol -> Def t LocSymbol
expandMeasureDef env name rtEnv d = d
  { body  = F.notracepp msg $ Bare.qualifyExpand env name rtEnv l bs (body d) }
  where
    l     = loc (measure d)
    bs    = fst <$> binds d
    msg   = "QUALIFY-EXPAND-BODY" ++ F.showpp (bs, body d)

------------------------------------------------------------------------------
varMeasures :: (Monoid r) => Bare.Env -> [(F.Symbol, Located (RRType r))]
------------------------------------------------------------------------------
varMeasures env =
  [ (F.symbol v, varSpecType v)
      | v <- knownVars env
      , GM.isDataConId v
      , isSimpleType (Ghc.varType v) ]

getMeasVars :: Bare.Env -> Bare.MeasEnv -> [(F.Symbol, Located (RRType F.Reft))]
getMeasVars env measEnv = Bare.meSyms measEnv -- ms'
                            ++ Bare.meClassSyms measEnv -- cms'
                            ++ varMeasures env

knownVars :: Bare.Env -> [Ghc.Var]
knownVars env = [ v | (_, xThings)   <- M.toList (Bare._reTyThings env)
                    , (_,Ghc.AnId v) <- xThings
                ]

varSpecType :: (Monoid r) => Ghc.Var -> Located (RRType r)
varSpecType = fmap (RT.ofType . Ghc.varType) . GM.locNamedThing

varBareType :: (Monoid r) => Ghc.Var -> Located (BRType r)
varBareType = fmap (RT.bareOfType . Ghc.varType) . GM.locNamedThing

varLocSym :: Ghc.Var -> LocSymbol
varLocSym v = F.symbol <$> GM.locNamedThing v

isSimpleType :: Ghc.Type -> Bool
isSimpleType = isFirstOrder . RT.typeSort mempty

makeClassMeasureSpec :: MSpec (RType c tv (UReft r2)) t
                     -> [(LocSymbol, CMeasure (RType c tv r2))]
makeClassMeasureSpec Ms.MSpec{..} = tx <$> M.elems cmeasMap
  where
    tx (M n s _ _ _) = (n, CM n (mapReft ur_reft s))


{-
expandMeasureBody :: Bare.Env -> ModName -> BareRTEnv -> SourcePos -> Body -> Body
expandMeasureBody env name rtEnv l (P   p) = P   (Bare.expandQualify env name rtEnv l p)
expandMeasureBody env name rtEnv l (R x p) = R x (Bare.expandQualify env name rtEnv l p)
expandMeasureBody env name rtEnv l (E   e) = E   (Bare.expandQualify env name rtEnv l e)


makeHaskellBounds :: F.TCEmb TyCon -> CoreProgram -> S.HashSet (Var, LocSymbol) -> BareM RBEnv  -- TODO-REBARE
makeHaskellBounds embs cbs xs = do
  lmap <- gets logicEnv
  M.fromList <$> mapM (makeHaskellBound embs lmap cbs) (S.toList xs)

makeHaskellBound :: F.TCEmb TyCon
                 -> LogicMap
                 -> [Bind Var]
                 -> (Var, Located Symbol)
                 -> BareM (LocSymbol, RBound)
makeHaskellBound embs lmap  cbs (v, x) =
  case filter ((v  `elem`) . GM.binders) cbs of
    (NonRec v def:_)   -> toBound v x <$> coreToFun' embs lmap x v def return
    (Rec [(v, def)]:_) -> toBound v x <$> coreToFun' embs lmap x v def return
    _                  -> throwError $ errHMeas x "Cannot make bound of haskell function"



toBound :: Var -> LocSymbol -> ([Var], Either F.Expr F.Expr) -> (LocSymbol, RBound)
toBound v x (vs, Left p) = (x', Bound x' fvs ps xs p)
  where
    x'         = capitalizeBound x
    (ps', xs') = L.partition (hasBoolResult . varType) vs
    (ps , xs)  = (txp <$> ps', txx <$> xs')
    txp v      = (dummyLoc $ simpleSymbolVar v, RT.ofType $ varType v)
    txx v      = (dummyLoc $ symbol v,          RT.ofType $ varType v)
    fvs        = (((`RVar` mempty) . RTV) <$> fst (splitForAllTyCoVars $ varType v)) :: [RSort]

toBound v x (vs, Right e) = toBound v x (vs, Left e)

capitalizeBound :: Located Symbol -> Located Symbol
capitalizeBound = fmap (symbol . toUpperHead . symbolString)
  where
    toUpperHead []     = []
    toUpperHead (x:xs) = toUpper x:xs

-}

