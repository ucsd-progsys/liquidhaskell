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
  , strengthenHaskellMeasures
  , strengthenHaskellInlines
  , makeMeasureSpec
  , makeMeasureSpec'
  , varMeasures
  -- , makeHaskellBounds
  -- , makeClassMeasureSpec
  ) where

-- import CoreSyn
-- import DataCon
-- import TyCon
-- import Id
-- import Type hiding (isFunTy)
-- import Var
-- import TysWiredIn (boolTyCon) -- , wiredInTyCons)

import Data.Default
-- import Data.Either (either)
import qualified Control.Exception as Ex
import Prelude hiding (mapM, error)
import Control.Monad hiding (forM, mapM)
import Control.Monad.Except hiding (forM, mapM)
import Control.Monad.State hiding (forM, mapM)
import Data.Bifunctor
import qualified Data.Maybe as Mb
import Data.Char (toUpper)


import Data.Traversable (forM, mapM)
import Text.PrettyPrint.HughesPJ (text)
import Text.Parsec.Pos (SourcePos)
import Text.Printf     (printf)
import qualified Data.List as L

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import           Language.Fixpoint.Types (Symbol, dummySymbol, symbolString, symbol, Expr(..), meet)
import           Language.Fixpoint.SortCheck (isFirstOrder)

import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.Transforms.CoreToLogic
import qualified Language.Fixpoint.Misc                as Misc
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Haskell.Liquid.Misc             ((.||.))
import qualified Language.Haskell.Liquid.GHC.API       as Ghc 
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Bounds
import qualified Language.Haskell.Liquid.Measure       as Ms

import qualified Language.Haskell.Liquid.Bare.Types    as Bare 
import qualified Language.Haskell.Liquid.Bare.Resolve  as Bare 
import qualified Language.Haskell.Liquid.Bare.Expand   as Bare 
import qualified Language.Haskell.Liquid.Bare.DataType as Bare 
import qualified Language.Haskell.Liquid.Bare.ToBare   as Bare 

-- import           Language.Haskell.Liquid.Bare.Env
-- import           Language.Haskell.Liquid.Bare.Misc       (simpleSymbolVar, hasBoolResult, makeDataConChecker, makeDataConSelector)
-- import           Language.Haskell.Liquid.Bare.Expand
-- import           Language.Haskell.Liquid.Bare.Lookup
-- import           Language.Haskell.Liquid.Bare.OfType
-- import           Language.Haskell.Liquid.Bare.Resolve
-- import           Language.Haskell.Liquid.Bare.ToBare

  -- let tds          = [(name, tc, dd) | (name, tc, _, Just dd) <- tcDds]
  -- let adts         = makeDataDecls cfg embs myName tds datacons
--------------------------------------------------------------------------------
makeHaskellMeasures :: GhcSrc -> Bare.TycEnv -> LogicMap -> Ms.BareSpec
                    -> [Measure (Located BareType) LocSymbol]
--------------------------------------------------------------------------------
makeHaskellMeasures src tycEnv lmap spec 
          = Bare.measureToBare <$> ms
  where 
    ms    = makeMeasureDefinition tycEnv lmap cbs <$> mSyms 
    cbs   = nonRecCoreBinds   (giCbs src) 
    mSyms = S.toList (Ms.hmeas spec)

  
makeMeasureDefinition :: Bare.TycEnv -> LogicMap -> [Ghc.CoreBind] -> LocSymbol 
                      -> Measure LocSpecType Ghc.DataCon
makeMeasureDefinition tycEnv lmap cbs x = 
  case GM.findVarDef (val x) cbs of
    Nothing       -> Ex.throw $ errHMeas x "Cannot extract measure from haskell function"
    Just (v, def) -> Ms.mkM vx vinfo mdef MsLifted
                     where 
                       vx           = F.atLoc x (symbol v)
                       mdef         = coreToDef' tycEnv lmap vx v def
                       vinfo        = GM.varLocInfo logicType v

coreToDef' :: Bare.TycEnv -> LogicMap -> LocSymbol -> Ghc.Var -> Ghc.CoreExpr 
           -> [Def LocSpecType Ghc.DataCon] 
coreToDef' tycEnv lmap vx v def = 
  case runToLogic embs lmap dm (errHMeas vx) (coreToDef vx v def) of
    Right l -> l
    Left e  -> Ex.throw e
  where 
    embs    = Bare.tcEmbs       tycEnv 
    dm      = Bare.tcDataConMap tycEnv  

errHMeas :: LocSymbol -> String -> Error
errHMeas x str = ErrHMeas (GM.sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

--------------------------------------------------------------------------------
makeHaskellInlines :: GhcSrc -> Bare.TycEnv -> LogicMap -> Ms.BareSpec 
                   -> [(LocSymbol, LMap)]
--------------------------------------------------------------------------------
makeHaskellInlines src tycEnv lmap spec 
         = makeMeasureInline tycEnv lmap cbs <$> inls 
  where
    cbs  = nonRecCoreBinds (giCbs src) 
    inls = S.toList        (Ms.inlines spec)

makeMeasureInline :: Bare.TycEnv -> LogicMap -> [Ghc.CoreBind] -> LocSymbol
                  -> (LocSymbol, LMap)
makeMeasureInline tycEnv lmap cbs x = 
  case GM.findVarDef (val x) cbs of 
    Nothing       -> Ex.throw $ errHMeas x "Cannot inline haskell function"
    Just (v, def) -> (vx, coreToFun' tycEnv lmap vx v def ok)
                     where 
                       vx         = F.atLoc x (symbol v)
                       ok (xs, e) = LMap vx (symbol <$> xs) (either id id e)

coreToFun' :: Bare.TycEnv -> LogicMap -> LocSymbol -> Ghc.Var -> Ghc.CoreExpr
           -> (([Ghc.Var], Either F.Expr F.Expr) -> a) -> a
coreToFun' tycEnv lmap x v def ok = either Ex.throw ok act 
  where 
    act  = runToLogic embs lmap dm err xFun 
    xFun = coreToFun x v def  
    err  = errHMeas x  
    dm   = Bare.tcDataConMap tycEnv 
    embs = Bare.tcEmbs       tycEnv 


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
  | exactDCFlag cfg = Mb.mapMaybe tyConDataDecl
                    . F.notracepp "makeHaskellDataDecls-1"
                    . zipMap   (hasDataDecl name spec . fst)
                    . liftableTyCons
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
hasDataDecl mod spec
                 = \tc -> F.notracepp (msg tc) $ M.lookupDefault def (tcName tc) decls
  where
    msg tc       = "hasDataDecl " ++ show (tcName tc)
    def          = NoDecl Nothing
    tcName       = fmap (qualifiedDataName mod) . tyConDataName True -- False
    dcName       =       qualifiedDataName mod  . tycName
    decls        = M.fromList [ (Just dn, hasDecl d)
                                | d     <- Ms.dataDecls spec
                                , let dn = dcName d]

qualifiedDataName :: ModName -> DataName -> DataName
qualifiedDataName mod (DnName lx) = DnName (qualifyModName mod <$> lx)
qualifiedDataName mod (DnCon  lx) = DnCon  (qualifyModName mod <$> lx)

{-tyConDataDecl :: {tc:TyCon | isAlgTyCon tc} -> Maybe DataDecl @-}
tyConDataDecl :: ((Ghc.TyCon, DataName), HasDataDecl) -> Maybe DataDecl
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
      where decls = map dataConDecl . Ghc.tyConDataCons

tyConDataName :: Bool -> Ghc.TyCon -> Maybe DataName
tyConDataName full tc
  | vanillaTc  = Just (DnName ((post . symbol) <$> GM.locNamedThing tc))
  | d:_ <- dcs = Just (DnCon  ((post . symbol) <$> GM.locNamedThing d ))
  | otherwise  = Nothing
  where
    post       = if full then id else GM.dropModuleNamesAndUnique
    vanillaTc  = Ghc.isVanillaAlgTyCon tc
    dcs        = Misc.sortOn symbol (Ghc.tyConDataCons tc)

dataConDecl :: Ghc.DataCon -> DataCtor
dataConDecl d     = F.notracepp msg $ DataCtor dx [] xts Nothing
-- dataConDecl d     = F.tracepp msg $ DataCtor dx (RT.bareOfType <$> ps) xts outT
  where
    isGadt        = not (Ghc.isVanillaDataCon d)
    msg           = printf "dataConDecl (gadt = %s)" (show isGadt)
    xts           = [(Bare.makeDataConSelector Nothing d i, RT.bareOfType t) | (i, t) <- its ]
    dx            = symbol <$> GM.locNamedThing d
    its           = zip [1..] ts
    (_,_ps,ts,t)   = Ghc.dataConSig d
    _outT :: Maybe BareType
    _outT
      | isGadt    = Just (RT.bareOfType t)
      | otherwise = Nothing



----------------------------------------------------------------------------------------------
-- | 'makeMeasureSelectors' converts the 'DataCon's and creates the measures for
--   the selectors and checkers that then enable reflection.
----------------------------------------------------------------------------------------------

strengthenHaskellInlines  :: S.HashSet (Located Ghc.Var) -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskellInlines  = strengthenHaskell strengthenResult

strengthenHaskellMeasures :: S.HashSet (Located Ghc.Var) -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskellMeasures = strengthenHaskell strengthenResult'

strengthenHaskell :: (Ghc.Var -> SpecType) -> S.HashSet (Located Ghc.Var) -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskell strengthen hmeas sigs
  = go <$> Misc.groupList (reverse sigs ++ hsigs)
  where
    hsigs      = [(val x, x {val = strengthen $ val x}) | x <- S.toList hmeas]
    go (v, xs) = (v,) $ L.foldl1' (flip meetLoc) xs

meetLoc :: Located SpecType -> Located SpecType -> LocSpecType
meetLoc t1 t2 = t1 {val = val t1 `meet` val t2}

--------------------------------------------------------------------------------
-- | 'makeMeasureSelectors' converts the 'DataCon's and creates the measures for
--   the selectors and checkers that then enable reflection.
--------------------------------------------------------------------------------

makeMeasureSelectors :: Config -> Bare.DataConMap -> (Ghc.DataCon, Located DataConP) -> [Measure SpecType Ghc.DataCon]
makeMeasureSelectors cfg dm (dc, Loc l l' (DataConP _ _vs _ps _ _ xts _resTy isGadt _ _))
  = (Misc.condNull (exactDCFlag cfg) $ checker : Mb.catMaybes (go' <$> fields)) --  internal measures, needed for reflection
 ++ (Misc.condNull (autofields)      $           Mb.catMaybes (go  <$> fields)) --  user-visible measures.
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
      = Just $ makeMeasureSelector (Loc l l' (Bare.makeDataConSelector (Just dm) dc i)) (projT i) dc n i

    fields   = zip (reverse xts) [1..]
    n        = length xts
    checker  = makeMeasureChecker (Loc l l' (Bare.makeDataConChecker dc)) checkT dc n
    projT i  = dataConSel dc n (Proj i)
    checkT   = dataConSel dc n Check

dataConSel :: Ghc.DataCon -> Int -> DataConSel -> SpecType
dataConSel dc n Check    = mkArrow as [] [] [] [xt] bareBool
  where
    (as, _, xt)          = {- traceShow ("dataConSel: " ++ show dc) $ -} bkDataCon dc n

dataConSel dc n (Proj i) = mkArrow as [] [] [] [xt] (mempty <$> ti)
  where
    ti                   = Mb.fromMaybe err $ Misc.getNth (i-1) ts
    (as, ts, xt)         = {- F.tracepp ("bkDatacon dc = " ++ F.showpp (dc, n)) $ -} bkDataCon dc n
    err                  = panic Nothing $ "DataCon " ++ show dc ++ "does not have " ++ show i ++ " fields"

-- bkDataCon :: DataCon -> Int -> ([RTVar RTyVar RSort], [SpecType], (Symbol, SpecType, RReft))
bkDataCon :: (F.Reftable r) => Ghc.DataCon -> Int -> ([RTVar RTyVar RSort], [RRType r], (Symbol, RRType r, r))
bkDataCon dc nFlds  = (as, ts, (dummySymbol, t, mempty))
  where
    ts                = RT.ofType <$> Misc.takeLast nFlds _ts
    t                 = {- traceShow ("bkDataConResult" ++ GM.showPpr (_t, t0)) $ -}
                        RT.ofType  $ Ghc.mkTyConApp tc tArgs'
    as                = makeRTVar . RT.rTyVar <$> αs
    ((αs,_,_,_,_ts,_t), _t0) = hammer dc
    tArgs'            = take (nArgs - nVars) tArgs ++ (Ghc.mkTyVarTy <$> αs)
    nVars             = length αs
    nArgs             = length tArgs
    (tc, tArgs)       = Mb.fromMaybe err (Ghc.splitTyConApp_maybe _t)
    err               = GM.namedPanic dc ("Cannot split result type of DataCon " ++ show dc)
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
makeMeasureSelector x s dc n i = M { msName = x, msSort = s, msEqns = [eqn], msKind = MsSelector }
  where
    eqn                        = Def x dc Nothing args (E (EVar $ mkx i))
    args                       = ((, Nothing) . mkx) <$> [1 .. n]
    mkx j                      = symbol ("xx" ++ show j)

makeMeasureChecker :: LocSymbol -> SpecType -> Ghc.DataCon -> Int -> Measure SpecType Ghc.DataCon
makeMeasureChecker x s0 dc n = M { msName = x, msSort = s, msEqns = eqn : (eqns <$> filter (/= dc) dcs), msKind = MsChecker }
  where
    s       = F.notracepp ("makeMeasureChecker: " ++ show x) s0
    eqn     = Def x dc Nothing (((, Nothing) . mkx) <$> [1 .. n])       (P F.PTrue)
    eqns d  = Def x d  Nothing (((, Nothing) . mkx) <$> [1 .. nArgs d]) (P F.PFalse)
    nArgs d = length (Ghc.dataConOrigArgTys d)
    mkx j   = symbol ("xx" ++ show j)
    dcs     = Ghc.tyConDataCons (Ghc.dataConTyCon dc)


----------------------------------------------------------------------------------------------
makeMeasureSpec' :: MSpec SpecType Ghc.DataCon -> ([(Ghc.Var, SpecType)], [(LocSymbol, RRType F.Reft)])
----------------------------------------------------------------------------------------------
makeMeasureSpec' mspec0 = (ctorTys, measTys) 
  where 
    ctorTys             = Misc.mapSnd RT.uRType <$> ctorTys0
    (ctorTys0, measTys) = Ms.dataConTypes mspec 
    mspec               = first (mapReft ur_reft) mspec0

----------------------------------------------------------------------------------------------
makeMeasureSpec :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> Ms.MSpec SpecType Ghc.DataCon
----------------------------------------------------------------------------------------------
makeMeasureSpec env sigEnv (name, spec) 
  = mkMeasureDCon env        name 
  . mkMeasureSort env sigEnv name 
  . first val 
  . bareMSpec     env sigEnv name 
  $ spec 

bareMSpec :: Bare.Env -> Bare.SigEnv -> ModName -> Ms.BareSpec -> Ms.MSpec LocBareType LocSymbol 
bareMSpec env sigEnv name spec = Ms.mkMSpec ms cms ims 
  where
    cms     = filter inScope $ Ms.cmeasures spec
    ms      = filter inScope $ expMeas <$> Ms.measures  spec
    ims     = filter inScope $ expMeas <$> Ms.imeasures spec
    expMeas = expandMeasure env name  rtEnv
    rtEnv   = Bare.sigRTEnv          sigEnv
    inScope = Bare.knownGhcVar env name . msName 

mkMeasureDCon :: Bare.Env -> ModName -> Ms.MSpec t LocSymbol -> Ms.MSpec t Ghc.DataCon
mkMeasureDCon env name m = mkMeasureDCon_ m [ (val n, symDC n) | n <- measureCtors m ]
  where 
    symDC                = Bare.lookupGhcDataCon env name "measure-datacon"

mkMeasureDCon_ :: Ms.MSpec t LocSymbol -> [(Symbol, Ghc.DataCon)] -> Ms.MSpec t Ghc.DataCon
mkMeasureDCon_ m ndcs = m' {Ms.ctorMap = cm'}
  where
    m'                = fmap (tx.val) m
    cm'               = Misc.hashMapMapKeys (symbol . tx) $ Ms.ctorMap m'
    tx                = Misc.mlookup (M.fromList ndcs)

measureCtors ::  Ms.MSpec t LocSymbol -> [LocSymbol]
measureCtors = Misc.sortNub . fmap ctor . concat . M.elems . Ms.ctorMap

mkMeasureSort :: Bare.Env -> Bare.SigEnv -> ModName -> Ms.MSpec BareType LocSymbol 
              -> Ms.MSpec SpecType LocSymbol
mkMeasureSort env sigEnv name (Ms.MSpec c mm cm im) = 
  Ms.MSpec (map txDef <$> c) (tx <$> mm) (tx <$> cm) (tx <$> im) 
    where
      ofMeaSort :: F.SourcePos -> BareType -> SpecType
      ofMeaSort = Bare.ofBareType env name  

      tx :: Measure BareType ctor -> Measure SpecType ctor
      tx (M n s eqs k) = M n (ofMeaSort l s) (txDef <$> eqs) k     where l = GM.fSourcePos n

      txDef :: Def BareType ctor -> Def SpecType ctor
      txDef d = first (ofMeaSort l) d                              where l = GM.fSourcePos (measure d) 

--------------------------------------------------------------------------------
-- | Expand Measures -----------------------------------------------------------
--------------------------------------------------------------------------------
type BareMeasure = Measure (Located BareType) LocSymbol

expandMeasure :: Bare.Env -> ModName -> BareRTEnv -> BareMeasure -> BareMeasure
expandMeasure env name rtEnv m = m 
  { msSort = RT.generalize                   <$> msSort m
  , msEqns = expandMeasureDef env name rtEnv <$> msEqns m 
  }

expandMeasureDef :: Bare.Env -> ModName -> BareRTEnv -> Def t LocSymbol -> Def t LocSymbol
expandMeasureDef env name rtEnv d = d 
  { body  = Bare.expandQualify env name rtEnv l (body d) }
  where l = loc (measure d) 

------------------------------------------------------------------------------
varMeasures :: (Monoid r) => [Ghc.Var] -> [(Ghc.Var, Located (RRType r))]
------------------------------------------------------------------------------
varMeasures vars = 
  [ (v, varSpecType v) 
      | v <- vars
      , GM.isDataConId v
      , isSimpleType (Ghc.varType v) ]

varSpecType :: (Monoid r) => Ghc.Var -> Located (RRType r)
varSpecType = fmap (RT.ofType . Ghc.varType) . GM.locNamedThing

isSimpleType :: Ghc.Type -> Bool
isSimpleType = isFirstOrder . RT.typeSort mempty


{- 
expandMeasureBody :: Bare.Env -> ModName -> BareRTEnv -> SourcePos -> Body -> Body
expandMeasureBody env name rtEnv l (P   p) = P   (Bare.expandQualify env name rtEnv l p) 
expandMeasureBody env name rtEnv l (R x p) = R x (Bare.expandQualify env name rtEnv l p) 
expandMeasureBody env name rtEnv l (E   e) = E   (Bare.expandQualify env name rtEnv l e) 

makeClassMeasureSpec :: MSpec (RType c tv (UReft r2)) t
                     -> [(LocSymbol, CMeasure (RType c tv r2))]
makeClassMeasureSpec (Ms.MSpec {..}) = tx <$> M.elems cmeasMap
  where
    tx (M n s _ _) = (n, CM n (mapReft ur_reft s))

makeHaskellBounds :: F.TCEmb TyCon -> CoreProgram -> S.HashSet (Var, LocSymbol) -> BareM RBEnv
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
    fvs        = (((`RVar` mempty) . RTV) <$> fst (splitForAllTys $ varType v)) :: [RSort]

toBound v x (vs, Right e) = toBound v x (vs, Left e)

capitalizeBound :: Located Symbol -> Located Symbol
capitalizeBound = fmap (symbol . toUpperHead . symbolString)
  where
    toUpperHead []     = []
    toUpperHead (x:xs) = toUpper x:xs

-}
