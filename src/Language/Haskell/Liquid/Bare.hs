{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ViewPatterns              #-}

-- | This module contains the functions that convert /from/ descriptions of
-- symbols, names and types (over freshly parsed /bare/ Strings),
-- /to/ representations connected to GHC vars, names, and types.
-- The actual /representations/ of bare and real (refinement) types are all
-- in `RefType` -- they are different instances of `RType`

module Language.Haskell.Liquid.Bare (
    GhcSpec(..)
  , makeGhcSpec

  -- * Lifted Spec
  , loadLiftedSpec
  , saveLiftedSpec
  ) where


import           Prelude                                    hiding (error)
import           CoreSyn                                    hiding (Expr)
import qualified CoreSyn
import           HscTypes
import           Id
import           NameSet
import           Name
import           TyCon
import           Var
import           TysWiredIn
import           DataCon                                    (DataCon)
import           InstEnv

import           Control.Monad.Reader
import           Control.Monad.State
-- import           Control.Monad.Except                       (throwError)
import           Data.Bifunctor
import qualified Data.Binary                                as B
import           Data.Maybe

import           Text.PrettyPrint.HughesPJ (text, (<+>))

import qualified Control.Exception                          as Ex
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S
import           System.Directory                           (doesFileExist)

import           Language.Fixpoint.Utils.Files              -- (extFileName)
import           Language.Fixpoint.Misc                     (applyNonNull, ensurePath, thd3, mapFst, mapSnd)
import           Language.Fixpoint.Types                    hiding (Error)

import           Language.Haskell.Liquid.Types.Dictionaries
import           Language.Haskell.Liquid.Misc               (nubHashOn)
import qualified Language.Haskell.Liquid.GHC.Misc  as GM
import           Language.Haskell.Liquid.Types.PredType     (makeTyConInfo)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure            as Ms

import           Language.Haskell.Liquid.Bare.Check
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Existential
import           Language.Haskell.Liquid.Bare.Measure
import           Language.Haskell.Liquid.Bare.Axiom
import           Language.Haskell.Liquid.Bare.Misc         (freeSymbols, makeSymbols, mkVarExpr)
import           Language.Haskell.Liquid.Bare.Plugged
import           Language.Haskell.Liquid.Bare.RTEnv
import           Language.Haskell.Liquid.Bare.Spec
import           Language.Haskell.Liquid.Bare.Expand
import           Language.Haskell.Liquid.Bare.SymSort
import           Language.Haskell.Liquid.Bare.Lookup        (lookupGhcTyCon)
import           Language.Haskell.Liquid.Bare.ToBare

--------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> FilePath
            -> ModName
            -> [CoreBind]
            -> Maybe [ClsInst]
            -> [Var]
            -> [Var]
            -> NameSet
            -> HscEnv
            -> Either Error LogicMap
            -> [(ModName, Ms.BareSpec)]
            -> IO GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec cfg file name cbs instenv vars defVars exports env lmap specs = do
  sp      <- throwLeft =<< execBare act initEnv
  let renv =  ghcSpecEnv sp
  throwLeft . checkGhcSpec specs renv $ postProcess cbs renv sp
  where
    act       = makeGhcSpec' cfg file cbs instenv vars defVars exports specs
    throwLeft = either Ex.throw return
    lmap'     = case lmap of { Left e -> Ex.throw e; Right x -> x `mappend` listLMap}
    axs       = tracepp "INIT-AXS" $ initAxSymbols name defVars specs
    initEnv   = BE name mempty mempty mempty env lmap' mempty mempty axs

initAxSymbols :: ModName -> [Var] -> [(ModName, Ms.BareSpec)] -> M.HashMap Symbol LocSymbol
initAxSymbols name vs = locMap .  Ms.reflects . fromMaybe mempty . lookup name
  where
    locMap xs         = M.fromList [ (val x, x) | x <- fmap tx <$> S.toList xs ]
    tx                = qualifySymbol' vs

importedSymbols :: ModName -> [(ModName, Ms.BareSpec)] -> S.HashSet LocSymbol
importedSymbols name specs = S.unions [ exportedSymbols sp |  (m, sp) <- specs, m /= name ]

exportedSymbols :: Ms.BareSpec -> S.HashSet LocSymbol
exportedSymbols spec = S.unions
  [ Ms.reflects spec
  , Ms.hmeas    spec
  , Ms.inlines  spec ]


listLMap :: LogicMap
listLMap  = toLogicMap [ (dummyLoc nilName , []     , hNil)
                       , (dummyLoc consName, [x, xs], hCons (EVar <$> [x, xs])) ]
  where
    x     = symbol "x"
    xs    = symbol "xs"
    hNil  = mkEApp (dcSym nilDataCon ) []
    hCons = mkEApp (dcSym consDataCon)
    dcSym = dummyLoc . GM.dropModuleUnique . symbol

postProcess :: [CoreBind] -> SEnv SortedReft -> GhcSpec -> GhcSpec
postProcess cbs specEnv sp@(SP {..})
  = sp { gsTySigs     = tracepp "GSTYSIGS" (mapSnd addTCI <$> sigs)
       , gsInSigs     = mapSnd addTCI <$> insigs
       , gsAsmSigs    = mapSnd addTCI <$> assms
       , gsInvariants = mapSnd addTCI <$> gsInvariants
       , gsLits       = txSort        <$> gsLits
       , gsMeas       = tracepp "GSMEAS"   (txSort        <$> gsMeas)
       , gsDicts      = dmapty addTCI'    gsDicts
       , gsTexprs     = ts
       }
  where
    (sigs,   ts')     = replaceLocBinds gsTySigs  gsTexprs
    (assms,  ts'')    = replaceLocBinds gsAsmSigs ts'
    (insigs, ts)      = replaceLocBinds gsInSigs  ts''
    replaceLocBinds   = replaceLocalBinds allowHO gsTcEmbeds gsTyconEnv specEnv cbs
    txSort            = mapSnd (addTCI . txRefSort gsTyconEnv gsTcEmbeds)
    addTCI            = (addTCI' <$>)
    addTCI'           = addTyConInfo gsTcEmbeds gsTyconEnv
    allowHO           = higherOrderFlag gsConfig

ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp = fromListSEnv binds
  where
    emb              = gsTcEmbeds sp
    binds            =  [(x,        rSort t) | (x, Loc _ _ t) <- gsMeas sp]
                     ++ [(symbol v, rSort t) | (v, Loc _ _ t) <- gsCtors sp]
                     ++ [(x,        vSort v) | (x, v)         <- gsFreeSyms sp, isConLikeId v ] -- // || S.member x refls ]
    rSort            = rTypeSortedReft emb
    vSort            = rSort . varRSort
    varRSort         :: Var -> RSort
    varRSort         = ofType . varType

--------------------------------------------------------------------------------
-- | [NOTE]: REFLECT-IMPORTS
--
-- 1. MAKE the full LiftedSpec, which will eventually, contain:
--      makeHaskell{Inlines, Measures, Axioms, Bounds}
-- 2. SAVE the LiftedSpec, which will be reloaded

-- | This step creates the aliases and inlines etc. It must be done BEFORE
--   we compute the `SpecType` for (all, including the reflected binders),
--   as we need the inlines and aliases to properly `expand` the SpecTypes.
--------------------------------------------------------------------------------

makeLiftedSpec0 :: TCEmb TyCon -> [CoreBind] -> Ms.BareSpec -> BareM Ms.BareSpec
makeLiftedSpec0 embs cbs mySpec = do
  xils   <- makeHaskellInlines  embs cbs mySpec
  ms     <- makeHaskellMeasures embs cbs mySpec
  return  $ mempty { Ms.ealiases = lmapEAlias . snd <$> xils
                   , Ms.measures = ms
                   , Ms.reflects = Ms.reflects mySpec
                   }

makeLiftedSpec1
  :: FilePath -> ModName -> Ms.BareSpec -> [(Var, LocSpecType)] -> [AxiomEq]
  -> BareM ()
makeLiftedSpec1 file name lSpec0 xts axs
  = liftIO $ saveLiftedSpec file name lSpec1
  where
    xbs    = [ (varLocSym x, specToBare <$> t) | (x, t) <- xts ]
    lSpec1 = lSpec0 { Ms.asmSigs  = xbs
                    , Ms.reflSigs = xbs
                    , Ms.axeqs    = axs }

varLocSym :: Var -> LocSymbol
varLocSym v = symbol <$> GM.locNamedThing v

saveLiftedSpec :: FilePath -> ModName -> Ms.BareSpec -> IO ()
saveLiftedSpec srcF _ lspec = do
  -- putStrLn $ "Saving Binary Lifted Spec: " ++ specF
  ensurePath specF
  B.encodeFile specF lspec
  where
    specF = extFileName BinSpec srcF

loadLiftedSpec :: Config -> FilePath -> IO Ms.BareSpec
loadLiftedSpec cfg srcF
  | noLiftedImport cfg = return mempty
  | otherwise          = do
      let specF = extFileName BinSpec srcF
      ex  <- doesFileExist specF
      -- putStrLn $ "Loading Binary Lifted Spec: " ++ specF ++ " " ++ show ex
      lSp <- if ex then B.decodeFile specF else return mempty
      -- putStrLn $ "Loaded Spec: " ++ showpp (Ms.reflSigs lSp)
      return lSp

insert :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
insert k v []              = [(k, v)]
insert k v ((k', v') : kvs)
  | k == k'                = (k, v)   : kvs
  | otherwise              = (k', v') : insert k v kvs

_dumpSigs :: [(ModName, Ms.BareSpec)] -> IO ()
_dumpSigs specs0 = putStrLn $ "DUMPSIGS:" ++  showpp [ (m, dump sp) | (m, sp) <- specs0 ]
  where
    dump sp = Ms.asmSigs sp ++ Ms.sigs sp ++ Ms.localSigs sp

--------------------------------------------------------------------------------
-- | symbolVarMap resolves each Symbol occuring in the spec to its Var;---------
--------------------------------------------------------------------------------

symbolVarMap :: (Id -> Bool) -> [Id] -> [LocSymbol] -> BareM [(Symbol, Var)]
symbolVarMap f vs xs' = do
  let xs0   = nubHashOn val [ x' | x <- xs', not (isWiredIn x), x' <- [x, GM.dropModuleNames <$> x] ]
  let xs    = tracepp "SYMS" xs0
  syms1    <- tracepp "SVM1" <$> (M.fromList <$> makeSymbols f vs (val <$> xs))
  syms2    <- tracepp "SVM2" <$> lookupIds True [ (lx, ()) | lx <- xs, not (M.member (val lx) syms1) ]
  -- let syms3 = tracepp "SVM3" $ mapMaybe (hackySymbolVar vs . val) xs
  return $ tracepp "reflect-datacons:symbolVarMap" (M.toList syms1 ++ [ (val lx, v) | (v, lx, _) <- syms2]) -- ++ syms3)

-- `liftedVarMap` is a special case of `symbolVarMap` that checks that all
-- lifted binders are in fact exported by the given module. We cannot use
-- GHC's isExportedId because it marks things exported even when they are not;
-- see tests/error_messages/ExportReflects.hs

liftedVarMap :: (Id -> Bool) -> [LocSymbol] -> BareM [(Symbol, Var)]
liftedVarMap f xs = do
  syms    <- symbolVarMap f [] xs
  let symm = M.fromList syms
  let es   = [ x | x <- xs, not (checkLifted symm x) ]
  applyNonNull (return syms) (Ex.throw . fmap mkErr) es
  where
    mkErr :: LocSymbol -> Error
    mkErr x = ErrLiftExp (GM.sourcePosSrcSpan $ loc x) (pprint $ val x)

checkLifted :: M.HashMap Symbol Var -> LocSymbol -> Bool
checkLifted symm x = M.member (val x) symm

_hackySymbolVar :: [Id] -> Symbol -> Maybe (Symbol, Var)
_hackySymbolVar vs x = (x, ) <$> L.find (isSymbolOfVar x) vs


--------------------------------------------------------------------------------
makeGhcSpec'
  :: Config -> FilePath -> [CoreBind] -> Maybe [ClsInst] -> [Var] -> [Var]
  -> NameSet -> [(ModName, Ms.BareSpec)]
  -> BareM GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec' cfg file cbs instenv vars defVars exports specs0 = do
  -- liftIO $ dumpSigs specs0
  name           <- modName <$> get
  let mySpec      = fromMaybe mempty (lookup name specs0)
  embs           <- makeNumericInfo instenv <$> (mconcat <$> mapM makeTyConEmbeds specs0)
  lSpec0         <- makeLiftedSpec0 embs cbs mySpec
  let fullSpec    = mySpec `mappend` lSpec0
  lmap           <- lmSymDefs . logicEnv    <$> get
  let specs       = insert name fullSpec specs0
  makeRTEnv name lSpec0 specs lmap
  syms0 <- liftedVarMap (varInModule name)      (S.toList $ exportedSymbols mySpec      )
  syms1 <- symbolVarMap (varInModule name) vars (S.toList $ importedSymbols name   specs)
  (tycons, datacons, dcSs, recSs, tyi) <- makeGhcSpecCHOP1 cfg specs embs (syms0 ++ syms1)
  makeBounds embs name defVars cbs specs
  modify                                   $ \be -> be { tcEnv = tyi }
  (cls, mts)                              <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
  (measures, cms', ms', cs', xs')         <- makeGhcSpecCHOP2 specs dcSs datacons cls embs
  (invs, ntys, ialias, sigs, asms)        <- makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
  quals    <- mconcat <$> mapM makeQualifiers specs
  let fSyms =  freeSymbols (tracepp "WHOAMI" xs') (sigs ++ asms ++ cs') ms' ((snd <$> invs) ++ (snd <$> ialias))
            ++ measureSymbols measures
  syms2    <- symbolVarMap (varInModule name) (vars ++ map fst cs') fSyms
  let syms  = syms0 ++ syms1 ++ syms2
  let su    = mkSubst [ (x, mkVarExpr v) | (x, v) <- syms ]
  makeGhcSpec0 cfg defVars exports name (emptySpec cfg)
    >>= makeGhcSpec1 syms vars defVars embs tyi exports name sigs (recSs ++ asms) cs'  ms' cms' su
    >>= makeGhcSpec2 invs ntys ialias measures su syms
    >>= makeGhcSpec3 (datacons ++ cls) tycons embs syms
    >>= makeSpecDictionaries embs vars specs
    -- The lifted-spec is saved in the next step
    >>= makeGhcAxioms file name embs cbs su specs lSpec0
    >>= makeLogicMap
    >>= makeExactDataCons name (exactDC cfg) (snd <$> syms)
    -- This step needs the UPDATED logic map, ie should happen AFTER makeLogicMap
    >>= makeGhcSpec4 quals defVars specs name su syms
    >>= addRTEnv

measureSymbols :: MSpec SpecType DataCon -> [LocSymbol]
measureSymbols measures = [ name m | m <- M.elems (Ms.measMap measures) ++ Ms.imeas measures ]

addRTEnv :: GhcSpec -> BareM GhcSpec
addRTEnv spec = do
  rt <- rtEnv <$> get
  return $ spec { gsRTAliases = rt }

makeExactDataCons :: ModName -> Bool -> [Var] -> GhcSpec -> BareM GhcSpec
makeExactDataCons _n flag vs spec
  | flag      = return $ spec { gsTySigs = gsTySigs spec ++ xts}
  | otherwise = return spec
  where
    xts       = makeExact <$> filter f vs
    f v       = GM.isDataConId v -- TODO:reflect-datacons && varInModule _n v

varInModule :: (Show a, Show a1) => a -> a1 -> Bool
varInModule n v = L.isPrefixOf (show n) $ show v

makeExact :: Var -> (Var, LocSpecType)
makeExact x = (x, dummyLoc . fromRTypeRep $ trep{ty_res = res, ty_binds = xs})
  where
    t    :: SpecType
    t    = ofType $ varType x
    trep = toRTypeRep t
    xs   = zipWith (\_ i -> (symbol ("x" ++ show i))) (ty_args trep) [1..]

    res  = ty_res trep `strengthen` MkUReft ref mempty mempty
    vv   = vv_
    x'   = symbol x --  simpleSymbolVar x
    ref  = Reft (vv, PAtom Eq (EVar vv) eq)
    eq   | null (ty_vars trep) && null xs = EVar x'
         | otherwise = mkEApp (dummyLoc x') (EVar <$> xs)

getReflects :: [(ModName, Ms.BareSpec)] -> [Symbol]
getReflects  = fmap val . S.toList . S.unions . fmap (names . snd)
  where
    names  z = S.unions [ Ms.reflects z, Ms.inlines z, Ms.hmeas z ]

getAxiomEqs :: [(ModName, Ms.BareSpec)] -> [AxiomEq]
getAxiomEqs = concatMap (Ms.axeqs . snd)

_getReflSigs :: [(ModName, Ms.BareSpec)] -> [(LocSymbol, LocBareType)]
_getReflSigs = concatMap (Ms.reflSigs . snd)

-- TODO: pull the `makeLiftedSpec1` out; a function should do ONE thing.
makeGhcAxioms
  :: FilePath -> ModName -> TCEmb TyCon -> [CoreBind] -> Subst
  -> [(ModName, Ms.BareSpec)] -> Ms.BareSpec
  -> GhcSpec -> BareM GhcSpec
makeGhcAxioms file name embs cbs su specs lSpec0 sp = do
  let mSpc = fromMaybe mempty (lookup name specs)
  let rfls = S.fromList (getReflects specs)
  xtes    <- makeHaskellAxioms embs cbs sp mSpc
  let xts  = [ (x, subst su t)       | (x, t, _) <- xtes ]
  let mAxs = [ qualifyAxiomEq x su e | (x, _, e) <- xtes ]  -- axiom-eqs in THIS module
  let iAxs = getAxiomEqs specs                              -- axiom-eqs from IMPORTED modules
  let axs  = mAxs ++ iAxs
  _       <- makeLiftedSpec1 file name lSpec0 xts mAxs
  let xts' = xts ++ gsAsmSigs sp
  let vts  = [ (v, t)        | (v, t) <- xts', let vx = GM.dropModuleNames $ symbol v, S.member vx rfls ]
  let msR  = [ (symbol v, t) | (v, t) <- vts ]
  let vs   = [ v             | (v, _) <- vts ]
  return   $ sp { gsAsmSigs  = xts'                   -- the IMPORTED refl-sigs are in gsAsmSigs sp
                , gsMeas     = tracepp "gsMeas" $ msR ++ gsMeas     sp   -- we must add them to gsMeas to allow the names in specifications
                , gsReflects = vs  ++ gsReflects sp
                , gsAxioms   = {- tracepp "GSAXIOMS" $ -} axs ++ gsAxioms   sp
                }

qualifyAxiomEq :: Var -> Subst -> AxiomEq -> AxiomEq
qualifyAxiomEq v su eq = subst su eq { axiomName = symbol v}

makeLogicMap :: GhcSpec -> BareM GhcSpec
makeLogicMap sp = do
  lmap  <- logicEnv <$> get
  return $ sp { gsLogicMap = lmap }

emptySpec     :: Config -> GhcSpec
emptySpec cfg = SP
  { gsTySigs     = mempty
  , gsAsmSigs    = mempty
  , gsInSigs     = mempty
  , gsCtors      = mempty
  , gsLits       = mempty
  , gsMeas       = mempty
  , gsInvariants = mempty
  , gsIaliases   = mempty
  , gsDconsP     = mempty
  , gsTconsP     = mempty
  , gsFreeSyms   = mempty
  , gsTcEmbeds   = mempty
  , gsQualifiers = mempty
  , gsTgtVars    = mempty
  , gsDecr       = mempty
  , gsTexprs     = mempty
  , gsNewTypes   = mempty
  , gsLvars      = mempty
  , gsLazy       = mempty
  , gsAutoInst   = mempty
  , gsAutosize   = mempty
  , gsConfig     = cfg
  , gsExports    = mempty
  , gsMeasures   = mempty
  , gsTyconEnv   = mempty
  , gsDicts      = mempty
  , gsAxioms     = mempty
  , gsReflects   = mempty
  , gsLogicMap   = mempty
  , gsProofType  = Nothing
  , gsRTAliases  = mempty
  }


makeGhcSpec0 :: Config
             -> [Var]
             -> NameSet
             -> ModName
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec0 cfg defVars exports name sp
  = do targetVars <- makeTargetVars name defVars $ checks cfg
       return      $ sp { gsConfig  = cfg
                        , gsExports = exports
                        , gsTgtVars = targetVars }

makeGhcSpec1 :: [(Symbol, Var)]
             -> [Var]
             -> [Var]
             -> TCEmb TyCon
             -> M.HashMap TyCon RTyCon
             -> NameSet
             -> ModName
             -> [(Var,    LocSpecType)]
             -> [(Var,    LocSpecType)]
             -> [(Var,    LocSpecType)]
             -> [(Symbol, Located (RRType Reft))]
             -> [(Symbol, Located (RRType Reft))]
             -> Subst
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec1 syms vars defVars embs tyi exports name sigs asms cs' ms' cms' su sp
  = do tySigs      <- makePluggedSigs name embs tyi exports $ tx sigs
       asmSigs     <- makePluggedAsmSigs embs tyi           $ tx asms
       ctors       <- makePluggedAsmSigs embs tyi           $ tx cs'
       return $ sp { gsTySigs   = filter (\(v,_) -> v `elem` vs) tySigs
                   , gsAsmSigs  = filter (\(v,_) -> v `elem` vs) asmSigs
                   , gsCtors    = filter (\(v,_) -> v `elem` vs) ctors
                   , gsMeas     = tracepp "MEASSYMS" measSyms
                   , gsLits     = measSyms -- RJ: we will be adding *more* things to `meas` but not `lits`
                   }
    where
      tx       = fmap . mapSnd . subst $ su
      tx'      = fmap (mapSnd $ fmap uRType)
      tx''     = fmap . mapFst . qualifySymbol $ syms
      vs       = S.fromList $ vars ++ defVars ++ (snd <$> syms)
      measSyms = tx'' . tx' . tx $ ms' ++ (varMeasures vars) ++ cms'

qualifyDefs :: [(Symbol, Var)] -> S.HashSet (Var, Symbol) -> S.HashSet (Var, Symbol)
qualifyDefs syms = S.fromList . fmap (mapSnd (qualifySymbol syms)) . S.toList

qualifyMeasure :: [(Symbol, Var)] -> Measure a b -> Measure a b
qualifyMeasure syms m = m { name = qualifyLocSymbol (qualifySymbol syms) (name m) }

qualifyRTyCon :: (Symbol -> Symbol) -> RTyCon -> RTyCon
qualifyRTyCon f rtc = rtc { rtc_info = qualifyTyConInfo f (rtc_info rtc) }

qualifyTyConInfo :: (Symbol -> Symbol) -> TyConInfo -> TyConInfo
qualifyTyConInfo f tci = tci { sizeFunction = qualifySizeFun f <$> sizeFunction tci }

qualifyLocSymbol :: (Symbol -> Symbol) -> LocSymbol -> LocSymbol
qualifyLocSymbol f lx = atLoc lx (f (val lx))

qualifyTyConP :: (Symbol -> Symbol) -> TyConP -> TyConP
qualifyTyConP f tcp = tcp { sizeFun = qualifySizeFun f <$> sizeFun tcp }

qualifySizeFun :: (Symbol -> Symbol) -> SizeFun -> SizeFun
qualifySizeFun f (SymSizeFun lx) = SymSizeFun (qualifyLocSymbol f lx)
qualifySizeFun _  sf              = sf

qualifySymbol :: [(Symbol, Var)] -> Symbol -> Symbol
qualifySymbol syms x = maybe x symbol (lookup x syms)

qualifySymbol' :: [Var] -> Symbol -> Symbol
qualifySymbol' vs x = tracepp ("qualifySymbol: x = " ++ show x) $ maybe x symbol (L.find (isSymbolOfVar x) vs)

makeGhcSpec2 :: Monad m
             => [(Maybe Var  , LocSpecType)]
             -> [(TyCon      , LocSpecType)]
             -> [(LocSpecType, LocSpecType)]
             -> MSpec SpecType DataCon
             -> Subst
             -> [(Symbol, Var)]
             -> GhcSpec
             -> m GhcSpec
makeGhcSpec2 invs ntys ialias measures su syms sp
  = return $ sp { gsInvariants = mapSnd (subst su) <$> invs
                , gsNewTypes   = mapSnd (subst su) <$> ntys
                , gsIaliases   = subst su ialias
                , gsMeasures   = tracepp "gs-measures"
                                ((qualifyMeasure syms . subst su)
                                 <$> (M.elems (Ms.measMap measures)
                                   ++ Ms.imeas measures)
                                   )
                }

makeGhcSpec3 :: [(DataCon, DataConP)] -> [(TyCon, TyConP)] -> TCEmb TyCon -> [(Symbol, Var)]
             -> GhcSpec -> BareM GhcSpec
makeGhcSpec3 datacons tycons embs syms sp = do
  tcEnv  <- tcEnv    <$> get
  return  $ sp { gsTyconEnv = tcEnv
               , gsDconsP   = [ Loc (dc_loc z) (dc_locE z) dc | (dc, z) <- datacons]
               , gsTcEmbeds = embs
               , gsTconsP   = [(tc, qualifyTyConP (qualifySymbol syms) tcp) | (tc, tcp) <- tycons]
               , gsFreeSyms = [(symbol v, v) | (_, v) <- syms]
               }

makeGhcSpec4 :: [Qualifier]
             -> [Var]
             -> [(ModName, Ms.Spec ty bndr)]
             -> ModName
             -> Subst
             -> [(Symbol, Var)]
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec4 quals defVars specs name su syms sp = do
  decr'     <- mconcat <$> mapM (makeHints defVars . snd) specs
  gsTexprs' <- mconcat <$> mapM (makeTExpr defVars . snd) specs
  lazies    <- mkThing makeLazy
  lvars'    <- mkThing makeLVar
  autois    <- mkThing makeAutoInsts
  addDefs  =<< (qualifyDefs syms <$> mkThing makeDefs)
  asize'    <- S.fromList <$> makeASize
  hmeas     <- mkThing makeHMeas
  hinls     <- mkThing makeHInlines
  mapM_ (\(v, _) -> insertAxiom (val v) Nothing) $ S.toList hmeas
  mapM_ (\(v, _) -> insertAxiom (val v) Nothing) $ S.toList hinls
  mapM_ insertHMeasLogicEnv $ S.toList hmeas
  mapM_ insertHMeasLogicEnv $ S.toList hinls
  lmap'       <- logicEnv <$> get
  isgs        <- expand $ strengthenHaskellInlines  (S.map fst hinls) (gsTySigs sp)
  gsTySigs'   <- expand $ strengthenHaskellMeasures (S.map fst hmeas) isgs
  gsMeasures' <- expand $ gsMeasures   sp
  gsAsmSigs'  <- expand $ gsAsmSigs    sp
  gsInSigs'   <- expand $ gsInSigs     sp
  gsInvarnts' <- expand $ gsInvariants sp
  gsCtors'    <- expand $ gsCtors      sp
  gsIaliases' <- expand $ gsIaliases   sp
  -- gsDconsP'   <- expand $ gsDconsP     sp
  return   $ sp { gsQualifiers = subst su quals
                , gsDecr       = decr'
                , gsLvars      = lvars'
                , gsAutoInst   = M.fromList $ S.toList autois
                , gsAutosize   = asize'
                , gsLazy       = S.insert dictionaryVar lazies
                , gsLogicMap   = lmap'
                , gsTySigs     = gsTySigs'
                , gsTexprs     = [ (v, subst su es) | (v, es) <- gsTexprs' ]
                , gsMeasures   = tracepp "GS-MEASURES-HERE" gsMeasures'
                , gsAsmSigs    = gsAsmSigs'
                , gsInSigs     = gsInSigs'
                , gsInvariants = gsInvarnts'
                , gsCtors      = gsCtors'
                , gsIaliases   = gsIaliases'
                -- , gsDconsP     = gsDconsP'
                }
  where
    mkThing mk      = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs, m == name ]
    makeASize       = mapM (lookupGhcTyCon "makeASize") [v | (m, s) <- specs, m == name, v <- S.toList (Ms.autosize s)]



insertHMeasLogicEnv :: (Located Var, LocSymbol) -> BareM ()
insertHMeasLogicEnv (x, s)
  -- / | isBool res
  = insertLogicEnv "insertHMeasLogicENV" s (fst <$> vxs) $ mkEApp s ((EVar . fst) <$> vxs)
  where
    -- res = ty_res rep
    rep = toRTypeRep  t
    t   = (ofType $ varType $ val x) :: SpecType
    xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs = dropWhile (isClassType.snd) $ zip xs (ty_args rep)
-- insertHMeasLogicEnv _
--   = return ()

makeGhcSpecCHOP1
  :: Config -> [(ModName,Ms.Spec ty bndr)] -> TCEmb TyCon -> [(Symbol, Var)]
  -> BareM ( [(TyCon,TyConP)]
           , [(DataCon,DataConP)]
           , [Measure SpecType DataCon]
           , [(Var, Located SpecType)]
           , M.HashMap TyCon RTyCon     )
makeGhcSpecCHOP1 cfg specs embs syms = do
  (tcs, dcs)      <- mconcat <$> mapM makeConTypes specs
  let tycons       = tcs        ++ wiredTyCons
  let tyi          = qualifyRTyCon (qualifySymbol syms) <$> makeTyConInfo tycons
  datacons        <- makePluggedDataCons embs tyi (concat dcs ++ wiredDataCons)
  let dcSelectors  = concatMap (makeMeasureSelectors (exactDC cfg) (not $ noMeasureFields cfg)) datacons
  recSels         <- makeRecordSelectorSigs datacons
  return             (tycons, second val <$> datacons, dcSelectors, recSels, tyi)

makeGhcSpecCHOP3 :: Config -> [Var] -> [Var] -> [(ModName, Ms.BareSpec)]
                 -> ModName -> [(ModName, Var, LocSpecType)]
                 -> TCEmb TyCon
                 -> BareM ( [(Maybe Var, LocSpecType)]
                          , [(TyCon, LocSpecType)]
                          , [(LocSpecType, LocSpecType)]
                          , [(Var, LocSpecType)]
                          , [(Var, LocSpecType)] )
makeGhcSpecCHOP3 cfg vars defVars specs name mts embs = do
  sigs'    <- mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs
  asms'    <- mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
  invs     <- mconcat <$> mapM makeInvariants specs
  ialias   <- mconcat <$> mapM makeIAliases   specs
  ntys     <- mconcat <$> mapM makeNewTypes   specs
  let dms   = makeDefaultMethods vars mts
  tyi      <- gets tcEnv
  let sigs  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
  let asms  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- asms' ]
  let hms   = concatMap (S.toList . Ms.hmeas . snd) (filter ((==name) . fst) specs)
  let minvs = makeMeasureInvariants sigs hms
  return     (invs ++ minvs, ntys, ialias, sigs, asms)

makeMeasureInvariants :: [(Var, LocSpecType)] -> [LocSymbol] -> [(Maybe Var, LocSpecType)]
makeMeasureInvariants sigs xs = measureTypeToInv <$> [(x, (y, ty)) | x <- xs, (y, ty) <- sigs, isSymbolOfVar (val x) y ]

isSymbolOfVar :: Symbol -> Var -> Bool
isSymbolOfVar x v = x == symbol' v
  where
    symbol' :: Var -> Symbol
    symbol' = GM.dropModuleNames . symbol . getName

measureTypeToInv :: (LocSymbol, (Var, LocSpecType)) -> (Maybe Var, LocSpecType)
measureTypeToInv (x, (v, t)) = (Just v, t {val = mtype})
  where
    trep = toRTypeRep $ val t
    ts   = ty_args trep
    mtype
      | isBool $ ty_res trep
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Specification of boolean measures is not allowed")
{-
      | [tx] <- ts, not (isTauto tx)
      = uError $ ErrHMeas (sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Measures' types cannot have preconditions")
-}
      | [tx] <- ts
      = mkInvariant (head $ ty_binds trep) tx $ ty_res trep
      | otherwise
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Measures has more than one arguments")


    mkInvariant :: Symbol -> SpecType -> SpecType -> SpecType
    mkInvariant z t tr = strengthen (top <$> t) (MkUReft reft mempty mempty)
      where
        Reft (v, p) = toReft $ fromMaybe mempty $ stripRTypeBase tr
        su    = mkSubst [(v, mkEApp x [EVar v])]
        reft  = Reft (v, subst su p')

        p'    = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p

makeGhcSpecCHOP2 :: [(ModName, Ms.BareSpec)]
                 -> [Measure SpecType DataCon]
                 -> [(DataCon, DataConP)]
                 -> [(DataCon, DataConP)]
                 -> TCEmb TyCon
                 -> BareM ( MSpec SpecType DataCon
                          , [(Symbol, Located (RRType Reft))]
                          , [(Symbol, Located (RRType Reft))]
                          , [(Var,    LocSpecType)]
                          , [Symbol] )
makeGhcSpecCHOP2 specs dcSelectors datacons cls embs = do
  measures'   <- mconcat <$> mapM makeMeasureSpec specs
  tyi         <- gets tcEnv
  let measures = tracepp "MADE-MSPEC" $ mconcat [measures' , Ms.mkMSpec' dcSelectors]
  let (cs, ms) = makeMeasureSpec' measures
  let cms      = makeClassMeasureSpec measures
  let cms'     = [ (x, Loc l l' $ cSort t) | (Loc l l' x, t) <- cms ]
  let ms'      = [ (x, Loc l l' t) | (Loc l l' x, t) <- ms, isNothing $ lookup x cms' ]
  let cs'      = [ (v, txRefSort' v tyi embs t) | (v, t) <- meetDataConSpec cs (datacons ++ cls)]
  let xs'      = fst <$> ms'
  return (measures, cms', tracepp "MADE-MSPEC-MS'" ms', cs', xs')

txRefSort' :: NamedThing a => a -> TCEnv -> TCEmb TyCon -> SpecType -> LocSpecType
txRefSort' v tyi embs t = txRefSort tyi embs (const t <$> GM.locNamedThing v) -- (atLoc' v t)

-- atLoc' :: NamedThing t => t -> a -> Located a
-- atLoc' v t = Loc (getSourcePos v) (getSourcePosE v)

data ReplaceEnv = RE
  { _reEnv  :: M.HashMap Symbol Symbol
  , _reFEnv :: SEnv SortedReft
  , _reEmb  :: TCEmb TyCon
  , _reTyi  :: M.HashMap TyCon RTyCon
  }

type ReplaceState = ( M.HashMap Var LocSpecType
                    , M.HashMap Var [Located Expr]
                    )

type ReplaceM = ReaderT ReplaceEnv (State ReplaceState)

-- ASKNIKI: WHAT DOES THIS FUNCTION DO?!!!!
replaceLocalBinds :: Bool
                  -> TCEmb TyCon
                  -> M.HashMap TyCon RTyCon
                  -> SEnv SortedReft
                  -> CoreProgram
                  -> [(Var, LocSpecType)]
                  -> [(Var, [Located Expr])]
                  -> ([(Var, LocSpecType)], [(Var, [Located Expr])])
replaceLocalBinds allowHO emb tyi senv cbs sigs texprs
  = (M.toList s, M.toList t)
  where
    (s, t) = execState (runReaderT (mapM_ (\x -> traverseBinds allowHO x (return ())) cbs)
                                   (RE M.empty senv emb tyi))
                       (M.fromList sigs,  M.fromList texprs)

traverseExprs :: Bool -> CoreSyn.Expr Var -> ReplaceM ()
traverseExprs allowHO (Let b e)
  = traverseBinds allowHO b (traverseExprs allowHO e)
traverseExprs allowHO (Lam b e)
  = withExtendedEnv allowHO [b] (traverseExprs allowHO e)
traverseExprs allowHO (App x y)
  = traverseExprs allowHO x >> traverseExprs allowHO y
traverseExprs allowHO (Case e _ _ as)
  = traverseExprs allowHO e >> mapM_ (traverseExprs allowHO . thd3) as
traverseExprs allowHO (Cast e _)
  = traverseExprs allowHO e
traverseExprs allowHO (Tick _ e)
  = traverseExprs allowHO e
traverseExprs _ _
  = return ()

traverseBinds :: Bool -> Bind Var -> ReplaceM b -> ReplaceM b
traverseBinds allowHO b k = withExtendedEnv allowHO (bindersOf b) $ do
  mapM_ (traverseExprs allowHO) (rhssOfBind b)
  k

-- RJ: this function is incomprehensible, what does it do?!
withExtendedEnv :: Bool -> [Var] -> ReplaceM b -> ReplaceM b
withExtendedEnv allowHO vs k = do
  RE env' fenv' emb tyi <- ask
  let env  = L.foldl' (\m v -> M.insert (varShortSymbol v) (symbol v) m) env' vs
      fenv = L.foldl' (\m v -> insertSEnv (symbol v) (rTypeSortedReft emb (ofType $ varType v :: RSort)) m) fenv' vs
  withReaderT (const (RE env fenv emb tyi)) $ do
    mapM_ (replaceLocalBindsOne allowHO) vs
    k

varShortSymbol :: Var -> Symbol
varShortSymbol = symbol . takeWhile (/= '#') . GM.showPpr . getName

-- RJ: this function is incomprehensible, what does it do?!
replaceLocalBindsOne :: Bool -> Var -> ReplaceM ()
replaceLocalBindsOne allowHO v
  = do mt <- gets (M.lookup v . fst)
       case mt of
         Nothing -> return ()
         Just (Loc l l' (toRTypeRep -> t@(RTypeRep {..}))) -> do
           (RE env' fenv emb tyi) <- ask
           let f m k = M.lookupDefault k k m
           let (env,args) = L.mapAccumL (\e (v, t) -> (M.insert v v e, substa (f e) t))
                             env' (zip ty_binds ty_args)
           let res  = substa (f env) ty_res
           let t'   = fromRTypeRep $ t { ty_args = args, ty_res = res }
           let msg  = ErrTySpec (GM.sourcePosSrcSpan l) (text "replaceLocalBindsOne" <+> pprint v) t'
           case checkTy allowHO msg emb tyi fenv (Loc l l' t') of
             Just err -> Ex.throw err
             Nothing  -> modify (first $ M.insert v (Loc l l' t'))
           mes <- gets (M.lookup v . snd)
           case mes of
             Nothing -> return ()
             Just es -> do
               let es'  = substa (f env) es
               case checkTerminationExpr emb fenv (v, Loc l l' t', es') of
                 Just err -> Ex.throw err
                 Nothing  -> modify (second $ M.insert v es')
