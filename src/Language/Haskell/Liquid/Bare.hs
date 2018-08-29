{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE OverloadedStrings         #-}

-- | This module contains the functions that convert /from/ descriptions of
--   symbols, names and types (over freshly parsed /bare/ Strings),
--   /to/ representations connected to GHC vars, names, and types.
--   The actual /representations/ of bare and real (refinement) types are all
--   in `RefType` -- they are different instances of `RType`

module Language.Haskell.Liquid.Bare (
    GhcSpec(..)
  , makeGhcSpec

  -- * Lifted Spec
  , loadLiftedSpec
  , saveLiftedSpec
  ) where


import           Prelude                                    hiding (error)
-- import qualified Control.Exception                          as Ex
-- import           Data.Bifunctor
import qualified Data.Binary                                as B
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S
-- import           Text.PrettyPrint.HughesPJ                  hiding (first, (<>)) -- (text, (<+>))
import           System.Directory                           (doesFileExist)
import           Language.Fixpoint.Utils.Files              -- (extFileName)
import           Language.Fixpoint.Misc                     as Misc 
import           Language.Fixpoint.Types                    hiding (DataDecl, Error, panic)
import qualified Language.Fixpoint.Types                    as F
-- import           Language.Haskell.Liquid.Types.Dictionaries
import qualified Language.Haskell.Liquid.Misc               as Misc -- (nubHashOn)
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Language.Haskell.Liquid.GHC.API            as Ghc 
-- import           Language.Haskell.Liquid.Types.PredType     (makeTyConInfo)
-- import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn
import qualified Language.Haskell.Liquid.Measure            as Ms

import qualified Language.Haskell.Liquid.Bare.Types         as Bare 
import qualified Language.Haskell.Liquid.Bare.Resolve       as Bare 
import qualified Language.Haskell.Liquid.Bare.DataType      as Bare 
import qualified Language.Haskell.Liquid.Bare.Expand        as Bare 
import qualified Language.Haskell.Liquid.Bare.Measure       as Bare 
import qualified Language.Haskell.Liquid.Bare.Plugged       as Bare 
import qualified Language.Haskell.Liquid.Bare.Axiom         as Bare 
import qualified Language.Haskell.Liquid.Bare.ToBare        as Bare 
import qualified Language.Haskell.Liquid.Bare.Spec          as Bare 
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as CoreToLogic 

{- 
import           Language.Haskell.Liquid.Bare.Check
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.Bare.Existential
import           Language.Haskell.Liquid.Bare.Axiom
import           Language.Haskell.Liquid.Bare.Misc         (freeSymbols, makeSymbols, mkVarExpr, simpleSymbolVar)
import           Language.Haskell.Liquid.Bare.Plugged
import           Language.Haskell.Liquid.Bare.RTEnv
import           Language.Haskell.Liquid.Bare.Spec
import           Language.Haskell.Liquid.Bare.Expand
import           Language.Haskell.Liquid.Bare.SymSort
import           Language.Haskell.Liquid.Bare.Lookup        (lookupGhcTyCon)
import           Language.Haskell.Liquid.Bare.ToBare
-- import Debug.Trace (trace)
-}

--------------------------------------------------------------------------------
-- | De/Serializing Spec files -------------------------------------------------
--------------------------------------------------------------------------------

loadLiftedSpec :: Config -> FilePath -> IO Ms.BareSpec
loadLiftedSpec cfg srcF
  | noLiftedImport cfg = return mempty
  | otherwise          = do
      let specF = extFileName BinSpec srcF
      ex  <- doesFileExist specF
      -- putStrLn $ "Loading Binary Lifted Spec: " ++ specF ++ " " ++ show ex
      lSp <- if ex then B.decodeFile specF else return mempty
      -- putStrLn $ "Loaded Spec: " ++ showpp (Ms.asmSigs lSp)
      -- putStrLn $ "Loaded Spec: " ++ showpp (Ms.invariants lSp)
      return lSp

-- saveLiftedSpec :: FilePath -> ModName -> Ms.BareSpec -> IO ()
saveLiftedSpec :: GhcSrc -> GhcSpec -> IO () 
saveLiftedSpec src sp = do
  ensurePath specF
  B.encodeFile specF lspec
  where
    srcF  = giTarget src 
    lspec = gsLSpec  sp 
    specF = extFileName BinSpec srcF

-- TODO-REBARE: `postProcess`

-------------------------------------------------------------------------------------
-- | @makeGhcSpec@ slurps up all the relevant information needed to generate 
--   constraints for a target module and packages them into a @GhcSpec@ 
--   See [NOTE] LIFTING-STAGES to see why we split into lSpec0, lSpec1, etc.
--   essentially, to get to the `BareRTEnv` as soon as possible, as thats what
--   lets us use aliases inside data-constructor definitions.
-------------------------------------------------------------------------------------
makeGhcSpec :: Config -> GhcSrc ->  LogicMap -> [(ModName, Ms.BareSpec)] -> GhcSpec
makeGhcSpec cfg src lmap mspecs = SP 
  { gsConfig = cfg 
  , gsSig    = addReflSigs refl sig 
  , gsRefl   = refl 
  , gsQual   = makeSpecQual cfg env rtEnv measEnv specs 
  , gsData   = sData 
  , gsName   = makeSpecName env tycEnv measEnv   name 
  , gsVars   = makeSpecVars cfg src mySpec env 
  , gsTerm   = makeSpecTerm cfg     mySpec env   name 
  , gsLSpec  = makeLiftedSpec refl sData lSpec1 
  }
  where
    -- build up spec components 
    sData    = makeSpecData src env sigEnv measEnv sig specs 
    refl     = makeSpecRefl src specs env name sig tycEnv 
    sig      = makeSpecSig name specs env sigEnv  measEnv 
    measEnv  = makeMeasEnv      env tycEnv sigEnv       specs 
    -- build up environments
    specs    = M.insert name mySpec iSpecs2
    mySpec   = mySpec2 <> lSpec1 
    lSpec1   = lSpec0 <> makeLiftedSpec1 cfg src tycEnv lmap mySpec1 
    sigEnv   = makeSigEnv  embs tyi (gsExports src) rtEnv 
    tyi      = Bare.tcTyConMap   tycEnv 
    tycEnv   = makeTycEnv   cfg name env embs mySpec2 iSpecs2 
    mySpec2  = Bare.qualifyExpand env name rtEnv l mySpec1    where l = F.dummyPos "expand-mySpec2"
    iSpecs2  = Bare.qualifyExpand env name rtEnv l iSpecs0    where l = F.dummyPos "expand-iSpecs2"
    rtEnv    = F.notracepp "RTENV" $ Bare.makeRTEnv env name mySpec1 iSpecs0 lmap  
    mySpec1  = mySpec0 <> lSpec0    
    lSpec0   = makeLiftedSpec0 cfg src embs lmap mySpec0 
    embs     = makeEmbeds          src env ((name, mySpec0) : M.toList iSpecs0)
    -- extract name and specs
    env      = Bare.makeEnv cfg src lmap  
    (mySpec0, iSpecs0) = splitSpecs name mspecs 
    name     = F.notracepp ("ALL-SPECS" ++ zzz) $ giTargetMod  src 
    zzz      = F.showpp (fst <$> mspecs)

splitSpecs :: ModName -> [(ModName, Ms.BareSpec)] -> (Ms.BareSpec, Bare.ModSpecs) 
splitSpecs name specs = (mySpec, iSpecm) 
  where 
    mySpec            = mconcat (snd <$> mySpecs)
    (mySpecs, iSpecs) = L.partition ((name ==) . fst) specs 
    iSpecm            = fmap mconcat . Misc.group $ iSpecs

makeEmbeds :: GhcSrc -> Bare.Env -> [(ModName, Ms.BareSpec)] -> F.TCEmb Ghc.TyCon 
makeEmbeds src env 
  = Bare.addClassEmbeds (gsCls src) (gsFiTcs src) 
  . mconcat 
  . map (makeTyConEmbeds env)

makeTyConEmbeds :: Bare.Env -> (ModName, Ms.BareSpec) -> F.TCEmb Ghc.TyCon
makeTyConEmbeds env (name, spec) 
  = F.tceFromList [ (tc, t) | (c,t) <- F.tceToList (Ms.embeds spec), tc <- symTc c ]
    where
      symTc = Mb.maybeToList . Bare.maybeResolveSym env name "embed-tycon" 

{- TODO-REBARE: postProcess

HEREHEREHERE 

--------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> FilePath
            -> ModName
            -> [CoreBind]
            -> [TyCon]
            -> Maybe [ClsInst]
            -> [Var]
            -> [Var]
            -> NameSet
            -> HscEnv
            -> Either Error LogicMap
            -> [(ModName, Ms.BareSpec)]
            -> IO GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec cfg file name cbs tcs instenv vars defVars exports env lmap specs = do
  (fiTcs, fie) <- makeFamInstEnv env
  let act       = makeGhcSpec' cfg file cbs fiTcs tcs instenv vars defVars exports specs
  sp           <- throwLeft =<< execBare act (initEnv fie)
  let renv      = L.foldl' (\e (x, s) -> insertSEnv x (RR s mempty) e) (ghcSpecEnv sp defVars) wiredSortedSyms
  throwLeft . checkGhcSpec specs renv $ postProcess cbs renv sp
  where
    throwLeft   = either Ex.throw return
    lmap'       = case lmap of { Left e -> Ex.throw e; Right x -> x `mappend` listLMap}
    initEnv fie = BE { modName  = name
                     , tcEnv    = mempty
                     , rtEnv    = mempty
                     , varEnv   = mempty
                     , hscEnv   = env
                     , famEnv   = fie
                     , logicEnv = lmap'
                     , dcEnv    = mempty
                     , bounds   = mempty
                     , embeds   = mempty
                     , axSyms   = initAxSymbols name defVars specs
                     , propSyms = initPropSymbols specs
                     , beConfig = cfg
                     , beIndex  = 0
                     }


initAxSymbols :: ModName -> [Var] -> [(ModName, Ms.BareSpec)] -> M.HashMap Symbol LocSymbol
initAxSymbols name vs = locMap .  Ms.reflects . fromMaybe mempty . lookup name
  where
    locMap xs         = M.fromList [ (val x, x) | x <- fmap tx <$> S.toList xs ]
    tx                = qualifySymbol' vs

-- | see NOTE:AUTO-INDPRED in Bare/DataType.hs
initPropSymbols :: [(ModName, Ms.BareSpec)] -> M.HashMap Symbol LocSymbol
initPropSymbols _ = M.empty

importedSymbols :: ModName -> [(ModName, Ms.BareSpec)] -> S.HashSet LocSymbol
importedSymbols name specs = S.unions [ exportedSymbols sp |  (m, sp) <- specs, m /= name ]

exportedSymbols :: Ms.BareSpec -> S.HashSet LocSymbol
exportedSymbols spec = S.unions
  [ Ms.reflects spec
  , Ms.hmeas    spec
  , Ms.inlines  spec ]

postProcess :: [CoreBind] -> SEnv SortedReft -> GhcSpec -> GhcSpec
postProcess cbs specEnv sp@(SP {..})
  = sp { gsTySigs     = mapSnd addTCI  <$> sigs
       , gsInSigs     = mapSnd addTCI  <$> insigs
       , gsAsmSigs    = mapSnd addTCI  <$> assms
       , gsInvariants = mapSnd addTCI  <$> gsInvariants
       , gsLits       = txSort         <$> gsLits
       , gsMeas       = txSort         <$> gsMeas
       , gsDicts      =        addTCI' <$>   gsDicts
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

ghcSpecEnv :: GhcSpec -> [Var] -> SEnv SortedReft
ghcSpecEnv sp _defs  = fromListSEnv binds
  where
    emb              = gsTcEmbeds sp
    binds            =  ([(x,       rSort t) | (x, Loc _ _ t) <- gsMeas sp])
                     ++ [(symbol v, rSort t) | (v, Loc _ _ t) <- gsCtors sp]
                     ++ [(x,        vSort v) | (x, v)         <- gsFreeSyms sp, isConLikeId v ]

                     -- WHY?!! ++ [(symbol x, vSort x) |  x  <- defs]

    rSort t          = rTypeSortedReft emb t
    vSort            = rSort . varRSort
    varRSort         :: Var -> RSort
varRSort = ofType . varType


 -}


--------------------------------------------------------------------------------
-- | [NOTE]: REFLECT-IMPORTS
--
-- 1. MAKE the full LiftedSpec, which will eventually, contain:
--      makeHaskell{Inlines, Measures, Axioms, Bounds}
-- 2. SAVE the LiftedSpec, which will be reloaded
-- 
--   This step creates the aliases and inlines etc. It must be done BEFORE
--   we compute the `SpecType` for (all, including the reflected binders),
--   as we need the inlines and aliases to properly `expand` the SpecTypes.
--------------------------------------------------------------------------------
makeLiftedSpec1 :: Config -> GhcSrc -> Bare.TycEnv -> LogicMap -> Ms.BareSpec 
                -> Ms.BareSpec
makeLiftedSpec1 _cfg src tycEnv lmap mySpec = mempty
            { Ms.measures  = ms
            -- , Ms.reflects  = Ms.reflects mySpec                              [REBARE: moved to makeLiftedSpec0]
            -- , Ms.dataDecls = Bare.makeHaskellDataDecls cfg name mySpec tcs   [REBARE: moved to makeLifedtSpec0]
            }
  where 
    ms      = Bare.makeHaskellMeasures src tycEnv lmap mySpec
    -- embs    = Bare.tcEmbs tycEnv 
    -- tcs     = uniqNub (gsTcs src ++ refTcs)
    -- refTcs  = reflectedTyCons cfg embs cbs             mySpec
    -- cbs     = giCbs       src
    -- name    = giTargetMod src





--------------------------------------------------------------------------------
-- | [NOTE]: LIFTING-STAGES 
-- 
-- We split the lifting up into stage:
-- 0. Where we only lift inlines,
-- 1. Where we lift reflects and measures.
-- 
-- This is because we need the inlines to build the @BareRTEnv@ which then
-- does the alias @expand@ business, that in turn, lets us build the DataConP,
-- i.e. the refined datatypes and their associate selectors, projectors etc,
-- that are needed for subsequent stages of the lifting.
--------------------------------------------------------------------------------
makeLiftedSpec0 :: Config -> GhcSrc -> F.TCEmb Ghc.TyCon -> LogicMap -> Ms.BareSpec 
                -> Ms.BareSpec
makeLiftedSpec0 cfg src embs lmap mySpec = mempty
  { Ms.ealiases  = lmapEAlias . snd <$> Bare.makeHaskellInlines src embs lmap mySpec 
  , Ms.reflects  = Ms.reflects mySpec
  , Ms.dataDecls = Bare.makeHaskellDataDecls cfg name mySpec tcs  
  }
  where 
    tcs          = uniqNub (gsTcs src ++ refTcs)
    refTcs       = reflectedTyCons cfg embs cbs  mySpec
    cbs          = giCbs       src
    name         = giTargetMod src

uniqNub :: (Ghc.Uniquable a) => [a] -> [a]
uniqNub xs = M.elems $ M.fromList [ (index x, x) | x <- xs ]
  where
    index  = Ghc.getKey . Ghc.getUnique

-- | 'reflectedTyCons' returns the list of `[TyCon]` that must be reflected but
--   which are defined *outside* the current module e.g. in Base or somewhere
--   that we don't have access to the code.

reflectedTyCons :: Config -> TCEmb Ghc.TyCon -> [Ghc.CoreBind] -> Ms.BareSpec -> [Ghc.TyCon]
reflectedTyCons cfg embs cbs spec
  | exactDCFlag cfg = filter (not . isEmbedded embs)
                    $ concatMap varTyCons
                    $ reflectedVars spec cbs
  | otherwise       = []

-- | We cannot reflect embedded tycons (e.g. Bool) as that gives you a sort
--   conflict: e.g. what is the type of is-True? does it take a GHC.Types.Bool
--   or its embedding, a bool?
isEmbedded :: TCEmb Ghc.TyCon -> Ghc.TyCon -> Bool
isEmbedded embs c = F.tceMember c embs

varTyCons :: Ghc.Var -> [Ghc.TyCon]
varTyCons = specTypeCons . ofType . Ghc.varType

specTypeCons           :: SpecType -> [Ghc.TyCon]
specTypeCons           = foldRType tc []
  where
    tc acc t@(RApp {}) = (rtc_tc $ rt_tycon t) : acc
    tc acc _           = acc

reflectedVars :: Ms.BareSpec -> [Ghc.CoreBind] -> [Ghc.Var]
reflectedVars spec cbs = (fst <$> xDefs)
  where
    xDefs              = Mb.mapMaybe (`GM.findVarDef` cbs) reflSyms
    reflSyms           = fmap val . S.toList . Ms.reflects $ spec

------------------------------------------------------------------------------------------
makeSpecVars :: Config -> GhcSrc -> Ms.BareSpec -> Bare.Env -> GhcSpecVars 
------------------------------------------------------------------------------------------
makeSpecVars cfg src mySpec env = SpVar 
  { gsTgtVars    =   map (resolveStringVar  env name)              (checks     cfg) 
  , gsIgnoreVars = S.map (Bare.lookupGhcVar env name "gs-ignores") (Ms.ignores mySpec) 
  , gsLvars      = S.map (Bare.lookupGhcVar env name "gs-lvars"  ) (Ms.lvars   mySpec)
  }
  where name     = giTargetMod src 

qualifySymbolic :: (F.Symbolic a) => ModName -> a -> F.Symbol 
qualifySymbolic name s = GM.qualifySymbol (F.symbol name) (F.symbol s)

resolveStringVar :: Bare.Env -> ModName -> String -> Ghc.Var
resolveStringVar env name s = Bare.lookupGhcVar env name "resolve-string-var" lx
  where 
    lx                      = dummyLoc (qualifySymbolic name s)

-- resolveLocSymbolVar :: Bare.Env -> ModName -> LocSymbol -> Ghc.Var
-- resolveLocSymbolVar env name lx = Bare.lookupGhcVar env name "Var" lx 


------------------------------------------------------------------------------------------
makeSpecQual :: Config -> Bare.Env -> BareRTEnv -> Bare.MeasEnv -> Bare.ModSpecs 
             -> GhcSpecQual 
------------------------------------------------------------------------------------------
makeSpecQual _cfg env rtEnv measEnv specs = SpQual 
  { gsQualifiers = filter okQual quals 
  , gsRTAliases  = makeSpecRTAliases env rtEnv 
  } 
  where 
    quals        = concatMap (makeQualifiers env) (M.toList specs) 
    mSyms        = M.fromList (Bare.meSyms measEnv ++ Bare.meClassSyms measEnv)
    okQual q     = all (`M.member` mSyms) (F.syms q)

makeSpecRTAliases :: Bare.Env -> BareRTEnv -> [Located SpecRTAlias]
makeSpecRTAliases _env _rtEnv = [] -- TODO-REBARE 
-- REBARE: toSpec . M.elems . typeAliases
-- REBARE: where toSpec = BareRTAlias -> SpecRTAlias 
-- REBARE: specAliases :: GhcInfo -> [Located BareRTAlias]
-- REBARE: specAliases = M.elems . typeAliases . gsRTAliases . gsQual . giSpec

makeQualifiers :: Bare.Env -> (ModName, Ms.Spec ty bndr) -> [F.Qualifier]
makeQualifiers env (mod, spec) = Bare.qualifyTop env mod <$> Ms.qualifiers spec 

------------------------------------------------------------------------------------------
makeSpecTerm :: Config -> Ms.BareSpec -> Bare.Env -> ModName -> GhcSpecTerm 
------------------------------------------------------------------------------------------
makeSpecTerm cfg mySpec env name = SpTerm 
  { gsTexprs     = makeTExpr env name mySpec 
  , gsLazy       = S.insert dictionaryVar (lazies `mappend` sizes)
  , gsStTerm     = sizes
  , gsAutosize   = autos 
  }
  where  
    lazies       = makeLazy     env name mySpec
    autos        = makeAutoSize env name mySpec
    noStrT       = nostructuralT cfg 
    sizes 
     | noStrT    = mempty 
     | otherwise = makeSize env name mySpec 

makeTExpr :: Bare.Env -> ModName -> Ms.BareSpec -> [(Ghc.Var, [Located F.Expr])]
makeTExpr env name spec = 
  [ (Bare.lookupGhcVar env name "Var" x, es) 
      | (x, es) <- Ms.termexprs spec           ]

makeLazy :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet Ghc.Var
makeLazy env name spec = 
  S.map (Bare.lookupGhcVar env name "Var") (Ms.lazy spec)

makeAutoSize :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet Ghc.TyCon
makeAutoSize env name spec =
  S.map (Bare.lookupGhcTyCon env name "TyCon") (Ms.autosize spec) 

makeSize :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet Ghc.Var
makeSize env name spec = 
  S.map (Bare.lookupGhcVar env name "Var") (S.fromList lzs)
  where
    lzs = Mb.catMaybes (getSizeFuns <$> Ms.dataDecls spec)
    getSizeFuns decl
      | Just x       <- tycSFun decl
      , SymSizeFun f <- x
      = Just f
      | otherwise
      = Nothing

------------------------------------------------------------------------------------------
makeSpecRefl :: GhcSrc -> Bare.ModSpecs -> Bare.Env -> ModName -> GhcSpecSig -> Bare.TycEnv 
             -> GhcSpecRefl 
------------------------------------------------------------------------------------------
makeSpecRefl src specs env name sig tycEnv = SpRefl 
  { gsLogicMap   = lmap 
  , gsAutoInst   = makeAutoInst env name mySpec 
  , gsImpAxioms  = concatMap (Ms.axeqs . snd) (M.toList specs)
  , gsMyAxioms   = myAxioms 
  , gsReflects   = F.notracepp "REFLECTS" $ filter (isReflectVar rflSyms) sigVars
  , gsHAxioms    = xtes 
  }
  where
    mySpec       = M.lookupDefault mempty name specs 
    xtes         = Bare.makeHaskellAxioms src env tycEnv name lmap sig mySpec
    myAxioms     = [ Bare.qualifyTop env name (e {eqName = symbol x}) | (x,_,e) <- xtes]  
    rflSyms      = S.fromList (getReflects specs)
    sigVars      = F.notracepp "SIGVARS" $ (fst3 <$> xtes)            -- reflects
                                        ++ (fst  <$> gsAsmSigs sig)   -- assumes
                                      -- ++ (fst  <$> gsTySigs  sig)   -- measures 

    lmap         = Bare.reLMap env

isReflectVar :: S.HashSet F.Symbol -> Ghc.Var -> Bool 
isReflectVar reflSyms v = S.member vx reflSyms
  where
    vx                  = GM.dropModuleNames (symbol v)

getReflects :: Bare.ModSpecs -> [Symbol]
getReflects  = fmap val . S.toList . S.unions . fmap (names . snd) . M.toList
  where
    names  z = S.unions [ Ms.reflects z, Ms.inlines z, Ms.hmeas z ]
    
------------------------------------------------------------------------------------------
-- | @updateReflSpecSig@ uses the information about reflected functions to update the 
--   "assumed" signatures. 
------------------------------------------------------------------------------------------
addReflSigs :: GhcSpecRefl -> GhcSpecSig -> GhcSpecSig
------------------------------------------------------------------------------------------
addReflSigs refl sig = sig { gsAsmSigs = reflSigs ++ gsAsmSigs sig }
  where 
    reflSigs         = [ (x, t) | (x, t, _) <- gsHAxioms refl ]   

makeAutoInst :: Bare.Env -> ModName -> Ms.BareSpec -> M.HashMap Ghc.Var (Maybe Int)
makeAutoInst env name spec = 
  Misc.hashMapMapKeys (Bare.lookupGhcVar env name "Var") (Ms.autois spec)

----------------------------------------------------------------------------------------
makeSpecSig :: ModName -> Bare.ModSpecs -> Bare.Env -> Bare.SigEnv -> Bare.MeasEnv 
            -> GhcSpecSig 
----------------------------------------------------------------------------------------
makeSpecSig name specs env sigEnv measEnv = SpSig 
  { gsTySigs   = F.tracepp "SIGS"     tySigs 
  , gsAsmSigs  = F.notracepp "ASM-SIGS" $ makeAsmSigs env sigEnv name specs 
  , gsInSigs   = mempty -- TODO-REBARE :: ![(Var, LocSpecType)]  
  , gsNewTypes = mempty -- TODO-REBARE :: ![(TyCon, LocSpecType)]
  , gsDicts    = _fixme_gsDicts -- TODO-REBARE :: !(DEnv Var SpecType)    
  }
  where 
    mySpec     = M.lookupDefault mempty name specs
    tySigs     = strengthenSigs . concat $
                  [ makeTySigs  env sigEnv name mySpec
                  , makeInlSigs env rtEnv allSpecs 
                  , makeMsrSigs env rtEnv allSpecs 
                  , makeMthSigs                    measEnv 
                  ]
    allSpecs   = M.toList specs 
    rtEnv      = Bare.sigRTEnv sigEnv 
    -- hmeas      = makeHMeas    env allSpecs 


strengthenSigs :: [(Ghc.Var, LocSpecType)] ->[(Ghc.Var, LocSpecType)]
strengthenSigs sigs = go <$> Misc.groupList sigs 
  where
    go (v, xs)      = (v,) $ L.foldl1' (flip meetLoc) xs
    meetLoc :: LocSpecType -> LocSpecType -> LocSpecType
    meetLoc t1 t2   = t1 {val = val t1 `F.meet` val t2}

makeMthSigs :: Bare.MeasEnv -> [(Ghc.Var, LocSpecType)]
makeMthSigs measEnv = [ (v, t) | (_, v, t) <- Bare.meMethods measEnv ]

makeInlSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)] 
makeInlSigs env rtEnv 
  = makeLiftedSigs rtEnv CoreToLogic.inlineSpecType 
  . makeFromSet "hinlines" Ms.inlines env 

makeMsrSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)] 
makeMsrSigs env rtEnv 
  = makeLiftedSigs rtEnv CoreToLogic.measureSpecType 
  . makeFromSet "hmeas" Ms.hmeas env 

makeLiftedSigs :: BareRTEnv -> (Ghc.Var -> SpecType) -> [Ghc.Var] -> [(Ghc.Var, LocSpecType)]
makeLiftedSigs rtEnv f xs 
  = [(x, lt) | x <- xs
             , let lx = GM.locNamedThing x
             , let lt = expand $ lx {val = f x}
    ]
  where
    expand   = Bare.specExpandType rtEnv 

makeFromSet :: String -> (Ms.BareSpec -> S.HashSet LocSymbol) -> Bare.Env -> [(ModName, Ms.BareSpec)] 
            -> [Ghc.Var] 
makeFromSet msg f env specs = concat [ mk n xs | (n, s) <- specs, let xs = S.toList (f s)] 
  where 
    mk name                 = Mb.mapMaybe (Bare.maybeResolveSym env name msg) 


{- OLD-REBARE 

strengthenHaskellInlines  :: Bare.SigEnv -> [Ghc.Var] -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskellInlines  sigEnv = strengthenHaskell sigEnv strengthenInlineResult

strengthenHaskellMeasures :: Bare.SigEnv -> [Ghc.Var] -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskellMeasures sigEnv = strengthenHaskell sigEnv strengthenMeasureResult

strengthenHaskell :: Bare.SigEnv -> (Ghc.Var -> SpecType) -> [Ghc.Var] -> [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
strengthenHaskell sigEnv strengthen hmeas sigs
  = go <$> Misc.groupList (reverse sigs ++ hsigs)
  where
    hsigs      = [(x, expand $ lx {val = strengthen x}) | x <- hmeas, let lx = GM.locNamedThing x]
    go (v, xs) = (v,) $ L.foldl1' (flip meetLoc) xs
    expand     = Bare.specExpandType rtEnv 
    rtEnv      = Bare.sigRTEnv sigEnv

-}

makeTySigs :: Bare.Env -> Bare.SigEnv -> ModName -> Ms.BareSpec -> [(Ghc.Var, LocSpecType)]
makeTySigs env sigEnv name spec = 
  [ (x, t) | (x, bt) <- rawTySigs env name spec 
           , let t    = Bare.cookSpecType env sigEnv name (Just x) bt 
  ] 

rawTySigs :: Bare.Env -> ModName -> Ms.BareSpec -> [(Ghc.Var, LocBareType)]
rawTySigs env name spec = 
  [ (v, t) | (x, t) <- Ms.sigs spec ++ Ms.localSigs spec  
           , let v   = Bare.lookupGhcVar env name "rawTySigs" x 
  ] 

makeAsmSigs :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs -> [(Ghc.Var, LocSpecType)]
makeAsmSigs env sigEnv myName specs = 
  [ (x, t) | (name, x, bt) <- rawAsmSigs env myName specs
           , let t = Bare.cookSpecType env sigEnv name (Just x) bt
  ] 

rawAsmSigs :: Bare.Env -> ModName -> Bare.ModSpecs -> [(ModName, Ghc.Var, LocBareType)]
rawAsmSigs env myName specs =  
  [ (name, v, t)  | (name, spec) <- M.toList specs
                  , (x   , t)    <- getAsmSigs myName name spec
                  , v            <- symVar name x 
  ] 
  where symVar n x = F.notracepp ("RAW-ASM-SIGS: " ++ F.showpp x) 
                   . Mb.maybeToList 
                   . Bare.maybeResolveSym env n "rawAsmVar" 
                   $ x 

getAsmSigs :: ModName -> ModName -> Ms.BareSpec -> [(LocSymbol, LocBareType)]  
getAsmSigs myName name spec 
  | myName == name = Ms.asmSigs spec
  | otherwise      = Ms.asmSigs spec ++ Ms.sigs spec

makeSigEnv :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> Ghc.NameSet -> BareRTEnv -> Bare.SigEnv 
makeSigEnv embs tyi exports rtEnv = Bare.SigEnv
  { sigEmbs     = embs 
  , sigTyRTyMap = tyi 
  , sigExports  = exports 
  , sigRTEnv    = rtEnv
  } 

{- TODO-REBARE: 
fixCoercions :: txCoerce 

mkVarSpec :: (Var, LocSymbol, Located BareType) -> BareM (Var, Located SpecType)
mkVarSpec (v, _, b) = (v,) . fmap (txCoerce . generalize) <$> mkLSpecType b
  where
    coSub           = {- F.tracepp _msg $ -} M.fromList [ (F.symbol a, F.FObj (specTvSymbol a)) | a <- tvs ]
    _msg            = "mkVarSpec v = " ++ F.showpp (v, b)
    tvs             = bareTypeVars (val b)
    specTvSymbol    = F.symbol . bareRTyVar
    txCoerce        = mapExprReft (\_ -> F.applyCoSub coSub)

bareTypeVars :: BareType -> [BTyVar]
bareTypeVars t = Misc.sortNub . fmap ty_var_value $ vs ++ vs'
  where
    vs         = fst4 . bkUniv $ t
    vs'        = freeTyVars    $ t

makeLocalSpec :: Config -> ModName -> [Var] -> [Var]
              -> [(LocSymbol, Located BareType)]
              -> [(LocSymbol, Located BareType)]
              -> BareM [(ModName, Var, Located SpecType)]

     vs = impVs ++ defVs
  = makeLocalSpec cfg cmod vs lvs (grepClassAsserts (Ms.rinstance spec)) (Ms.sigs spec ++ Ms.localSigs spec)
  sigs'    <- F.notracepp "MAKE-ASSERT-SPEC-1" <$> (mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs)
  hmeas     <- mkThing' True makeHMeas
  hinls     <- mkThing makeHInlines

  (cls, mts)   <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
  let dms   = makeDefaultMethods vars mts
  let sigs  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
  = do tySigs  <- makePluggedSigs name embs tyi exports $ tx sigs
       tx       = fmap . mapSnd . subst $ su
       sp { gsTySigs   = filter (\(v,_) -> v `elem` vs) tySigs
  isgs        <- expand' $ strengthenHaskellInlines  (S.map fst hinls) (gsTySigs sp)
  gsTySigs'   <- expand' $ strengthenHaskellMeasures (S.map fst hmeas) isgs

makeHInlines :: [Var] -> Ms.Spec ty bndr -> BareM [(Located Var, LocSymbol)]
makeHInlines = makeHIMeas Ms.inlines

makeHMeas :: [Var] -> Ms.Spec ty bndr -> BareM [(Located Var, LocSymbol)]
makeHMeas = makeHIMeas Ms.hmeas

makeHIMeas :: (Ms.Spec ty bndr -> S.HashSet LocSymbol)
           -> [Var]
           -> Ms.Spec ty bndr
           -> BareM [(Located Var, LocSymbol)]
makeHIMeas f vs spec
  = fmap tx <$> varSymbols id vs [(v, (loc v, locE v, v)) | v <- S.toList (f spec)]
  where
    tx (x, (l, l', s))  = (Loc l l' x, s)
-}

------------------------------------------------------------------------------------------
makeSpecData :: GhcSrc -> Bare.Env -> Bare.SigEnv -> Bare.MeasEnv -> GhcSpecSig -> Bare.ModSpecs
             -> GhcSpecData
------------------------------------------------------------------------------------------
makeSpecData src env sigEnv measEnv sig specs = SpData 
  { gsCtors      = [ (x, tt) 
                       | (x, t) <- Bare.meDataCons measEnv
                       , let tt = Bare.plugHoles sigEnv name x t 
                   ]
  , gsMeas       = [ (F.symbol x, uRType <$> t) | (x, t) <- measVars ] 
  , gsMeasures   = Bare.qualifyTop env name <$> (ms1 ++ ms2)
  , gsInvariants = makeMeasureInvariants env name sig mySpec 
                ++ concat (makeInvariants env sigEnv <$> M.toList specs)
  , gsIaliases   = mempty    -- TODO-REBARE :: ![(LocSpecType, LocSpecType)] -- ^ Data type invariant aliases 
  }
  where
    measVars     = Bare.meSyms      measEnv -- ms'
                ++ Bare.meClassSyms measEnv -- cms' 
                ++ Bare.varMeasures vars 
    vars         = Bare.srcVars src
    measures     = Bare.meMeasureSpec measEnv  
    ms1          = M.elems (Ms.measMap measures)
    ms2          =          Ms.imeas   measures
    mySpec       = M.lookupDefault mempty name specs
    name         = giTargetMod      src


makeInvariants :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> [(Maybe Ghc.Var, Located SpecType)]
makeInvariants env sigEnv (name, spec) = 
  [ (Nothing, t) 
    | (_, bt) <- Ms.invariants spec 
    , Bare.knownGhcType env name bt
    -- , Bare.knownGhcVar env name lx 
    , let t = Bare.cookSpecType env sigEnv name Nothing bt
  ]

makeMeasureInvariants :: Bare.Env -> ModName -> GhcSpecSig -> Ms.BareSpec -> [(Maybe Ghc.Var, LocSpecType)]
makeMeasureInvariants env name sig mySpec 
  = measureTypeToInv env name <$> [(x, (y, ty)) | x <- xs, (y, ty) <- sigs
                                       , isSymbolOfVar (val x) y ]
  where 
    sigs = gsTySigs sig 
    xs   = S.toList (Ms.hmeas  mySpec) 


isSymbolOfVar :: Symbol -> Ghc.Var -> Bool
isSymbolOfVar x v = x == symbol' v
  where
    symbol' :: Ghc.Var -> Symbol
    symbol' = GM.dropModuleNames . symbol . Ghc.getName

measureTypeToInv :: Bare.Env -> ModName -> (LocSymbol, (Ghc.Var, LocSpecType)) -> (Maybe Ghc.Var, LocSpecType)
measureTypeToInv env name (x, (v, t)) = (Just v, t {val = Bare.qualifyTop env name mtype})
  where
    trep = toRTypeRep (val t)
    ts   = ty_args  trep
    args = ty_binds trep
    res  = ty_res   trep
    mtype
      | null ts 
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x) "Measure has no arguments!"
      | otherwise 
      = mkInvariant x (last args) (last ts) res 

{-
      | isBool $ ty_res trep
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Specification of Boolean measures is not allowed")

      | [tx] <- ts, not (isTauto tx)
      = uError $ ErrHMeas (sourcePosSrcSpan $ loc t) (pprint x)
                          (text "Measures' types cannot have preconditions")
      | [tx] <- ts
      = mkInvariant x (head $ ty_binds trep) tx $ ty_res trep
      | otherwise
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x)
                          (text $ "Measure has more than one arguments: " ++ F.showpp ts)
-}

mkInvariant :: LocSymbol -> Symbol -> SpecType -> SpecType -> SpecType
mkInvariant x z t tr = strengthen (top <$> t) (MkUReft reft mempty mempty)
      where
        Reft (v, p)    = toReft $ Mb.fromMaybe mempty $ stripRTypeBase tr
        su             = mkSubst [(v, mkEApp x [EVar v])]
        reft           = Reft (v, subst su p')
        p'             = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p



    -- measSyms = tx'' . tx' . tx $ ms'
                               -- ++ (varMeasures vars)
                               -- ++ cms'

--      tx       = fmap . mapSnd . subst $ su
--      tx'      = fmap (mapSnd $ fmap uRType)
--      tx''     = fmap . mapFst . qualifySymbol $ syms
{- 
  let mSpc = fromMaybe mempty (lookup name specs)
  let rfls = S.fromList (getReflects specs)
  xtes    <- makeHaskellAxioms embs cbs sp mSpc adts
  let xts  = [ (x, subst su t)       | (x, t, _) <- xtes ]
  let xts' = xts ++ F.notracepp "GS-ASMSIGS" (gsAsmSigs sp)
  let vts  = [ (v, t)        | (v, t) <- xts', let vx = GM.dropModuleNames $ symbol v, S.member vx rfls ]
  let msR  = [ (symbol v, t) | (v, t) <- vts ]
-}

-- REBARE: formerly, makeGhcSpec3
-------------------------------------------------------------------------------------------
makeSpecName :: Bare.Env -> Bare.TycEnv -> Bare.MeasEnv -> ModName -> GhcSpecNames
-------------------------------------------------------------------------------------------
makeSpecName env tycEnv measEnv name = SpNames 
  { gsFreeSyms = Bare.reSyms env 
  , gsDconsP   = [ F.atLoc dc (dcpCon dc) | dc <- datacons ++ cls ] -- TODO-REBARE 
  , gsTconsP   = Bare.qualifyTop env name <$> tycons                -- TODO-REBARE: redundant with  
  -- , gsLits = mempty                                              -- TODO-REBARE, redundant with gsMeas
  , gsTcEmbeds = Bare.tcEmbs     tycEnv   
  , gsADTs     = Bare.tcAdts     tycEnv 
  , gsTyconEnv = Bare.tcTyConMap tycEnv  
  }
  where 
    datacons, cls :: [DataConP]
    datacons   = Bare.tcDataCons tycEnv 
    cls        = Bare.meClasses measEnv 
    tycons     = Bare.tcTyCons   tycEnv 

--                   , gsLits     = measSyms -- RJ: we will be adding *more* things to `meas` but not `lits`
-- >>= makeGhcSpec3 (datacons ++ cls) tycons embs syms
-- , gsDconsP   = [ Loc (dc_loc z) (dc_locE z) dc | (dc, z) <- datacons]
-- , gsTconsP   = [(tc, qualifyTyConP (qualifySymbol syms) tcp) | (tc, tcp) <- tycons]

-- REBARE: formerly, makeGhcCHOP1
-------------------------------------------------------------------------------------------
makeTycEnv :: Config -> ModName -> Bare.Env -> TCEmb Ghc.TyCon -> Ms.BareSpec -> Bare.ModSpecs 
           -> Bare.TycEnv 
-------------------------------------------------------------------------------------------
makeTycEnv cfg myName env embs mySpec iSpecs = Bare.TycEnv 
  { tcTyCons      = tycons                  
  , tcDataCons    = val <$> datacons 
  , tcSelMeasures = dcSelectors             
  , tcSelVars     = recSelectors            
  , tcTyConMap    = tyi                     
  , tcAdts        = adts                    
  , tcDataConMap  = dm
  , tcEmbs        = embs
  , tcName        = myName
  }
  where 
    (tcDds, dcs)  = F.notracepp "MAKECONTYPES" $ Misc.concatUnzip $ Bare.makeConTypes env <$> specs 
    specs         = (myName, mySpec) : M.toList iSpecs
    tcs           = Misc.snd3 <$> tcDds 
    tyi           = Bare.qualifyTop env myName <$> makeTyConInfo tycons
    -- tycons        = F.tracepp "TYCONS" $ Misc.replaceWith tcpCon tcs wiredTyCons
    -- datacons      =  Bare.makePluggedDataCons embs tyi (Misc.replaceWith (dcpCon . val) (F.tracepp "DATACONS" $ concat dcs) wiredDataCons)
    tycons        = tcs ++ knownWiredTyCons env myName 
    datacons      = Bare.makePluggedDataCon embs tyi <$> (concat dcs ++ knownWiredDataCons env myName)
    tds           = [(name, tcpCon tcp, dd) | (name, tcp, Just dd) <- tcDds]
    adts          = Bare.makeDataDecls cfg embs myName tds       datacons
    dm            = Bare.dataConMap adts
    dcSelectors   = concatMap (Bare.makeMeasureSelectors cfg dm) datacons
    recSelectors  = Bare.makeRecordSelectorSigs env myName       datacons
   
{- 

  DataCons --> tyi -->  

 -}    

knownWiredDataCons :: Bare.Env -> ModName -> [Located DataConP] 
knownWiredDataCons env name = filter isKnown wiredDataCons 
  where 
    isKnown                 = Bare.knownGhcDataCon env name . GM.namedLocSymbol . dcpCon . val

knownWiredTyCons :: Bare.Env -> ModName -> [TyConP] 
knownWiredTyCons env name = filter isKnown wiredTyCons 
  where 
    isKnown               = Bare.knownGhcTyCon env name . GM.namedLocSymbol . tcpCon 


-- REBARE: formerly, makeGhcCHOP2
-------------------------------------------------------------------------------------------
makeMeasEnv :: Bare.Env -> Bare.TycEnv -> Bare.SigEnv -> Bare.ModSpecs -> Bare.MeasEnv 
-------------------------------------------------------------------------------------------
makeMeasEnv env tycEnv sigEnv specs = Bare.MeasEnv 
  { meMeasureSpec = measures 
  , meClassSyms   = cms' 
  , meSyms        = ms' 
  , meDataCons    = cs' 
  , meClasses     = cls
  , meMethods     = mts -- TODO-REBARE: ++  let dms = makeDefaultMethods vars mts  
  }
  where 
    measures      = mconcat (Ms.mkMSpec' dcSelectors : (Bare.makeMeasureSpec env sigEnv <$> M.toList specs))
    (cs, ms)      = Bare.makeMeasureSpec'     measures
    cms           = Bare.makeClassMeasureSpec measures
    cms'          = [ (x, Loc l l' $ cSort t)  | (Loc l l' x, t) <- cms ]
    ms'           = [ (F.val lx, F.atLoc lx t) | (lx, t) <- ms
                                               -- , v       <- msVar lx 
                                               , Mb.isNothing (lookup (val lx) cms') ]
    cs'           = [ (v, txRefs v t) | (v, t) <- Bare.meetDataConSpec embs cs (datacons ++ cls)]
    txRefs v t    = Bare.txRefSort tyi embs (const t <$> GM.locNamedThing v) 
    -- msVar         = Mb.maybeToList . Bare.maybeResolveSym env name "measure-var" 
    -- unpacking the environement
    tyi           = Bare.tcTyConMap    tycEnv 
    dcSelectors   = Bare.tcSelMeasures tycEnv 
    datacons      = Bare.tcDataCons    tycEnv 
    embs          = Bare.tcEmbs        tycEnv 
    name          = Bare.tcName        tycEnv
    (cls, mts)    = Bare.makeClasses env sigEnv name specs
    -- TODO-REBARE: -- xs'      = fst <$> ms'


-----------------------------------------------------------------------------------------
-- | @makeLiftedSpec@ is used to generate the BareSpec object that should be serialized 
--   so that downstream files that import this target can access the lifted definitions, 
--   e.g. for measures, reflected functions etc.
-----------------------------------------------------------------------------------------
makeLiftedSpec :: GhcSpecRefl -> GhcSpecData -> Ms.BareSpec -> Ms.BareSpec 
-----------------------------------------------------------------------------------------
makeLiftedSpec refl sData lSpec0 
  = lSpec0 { Ms.asmSigs    = xbs
           , Ms.reflSigs   = F.notracepp "REFL-SIGS" xbs
           , Ms.axeqs      = gsMyAxioms refl 
           , Ms.invariants = xinvs
           }
  where 
    xbs    = [ (varLocSym x       , Bare.specToBare <$> t) | (x, t, _) <- gsHAxioms refl     ]
    xinvs  = [ ((varLocSym <$> x) , Bare.specToBare <$> t) | (x, t)    <- gsInvariants sData ]

varLocSym :: Ghc.Var -> LocSymbol
varLocSym v = F.symbol <$> GM.locNamedThing v


{- 
makeLiftedSpec1
  :: FilePath -> ModName -> Ms.BareSpec
  -> [(Var, LocSpecType)]
  -> [AxiomEq]
  -> [(Maybe Var, LocSpecType)]
  -> BareM ()
makeLiftedSpec1 file name lSpec0 xts axs invs
  = liftIO $ saveLiftedSpec file name lSpec1
  where
    xbs    = [ (varLocSym x       , specToBare <$> t) | (x, t) <- xts  ]
    xinvs  = [ ((varLocSym <$> x) , specToBare <$> t) | (x, t) <- invs ]
    lSpec1 = lSpec0 { Ms.asmSigs    = xbs
                    , Ms.reflSigs   = xbs
                    , Ms.axeqs      = axs
                    , Ms.invariants = xinvs
                    }

makeGhcSpec :: Config
            -> FilePath
            -> ModName
            -> [CoreBind]
            -> [TyCon]
            -> Maybe [ClsInst]
            -> [Var]
            -> [Var]
            -> NameSeClsInst] -> [Var] -> [Var]
  -> NameSet -> Bare.ModSpecs
  -> BareM GhcSpec
--------------------------------------------------------------------------------
makeGhcSpec' cfg file cbs fiTcs tcs instenv vars defVars exports specs0 = do
  -- liftIO $ _dumpSigs specs0
  name     <- modName <$> get
  let mySpec      = fromMaybe mempty (lookup name specs0)
  
  embs           <- addClassEmbeds instenv fiTcs <$> (mconcat <$> mapM makeTyConEmbeds specs0)
  
  lSpec0         <- makeLiftedSpec0 cfg name embs cbs tcs mySpec
  let fullSpec    = mySpec `mappend` lSpec0
  
  lmap           <- lmSymDefs . logicEnv    <$> get
  let specs       = insert name fullSpec specs0
  makeRTEnv name lSpec0 specs lmap

  let expSyms     = S.toList (exportedSymbols mySpec)
  syms0 <- liftedVarMap (varInModule name) expSyms
  syms1 <- symbolVarMap (varInModule name) vars (S.toList $ importedSymbols name   specs)

  (tycons, datacons, dcSs, recSs, tyi, adts) <- makeGhcSpecCHOP1 cfg specs embs (syms0 ++ syms1)
  
  checkShadowedSpecs dcSs (Ms.measures mySpec) syms0 defVars
  makeBounds embs name defVars cbs specs

  modify                                   $ \be -> be { tcEnv = tyi }
  (cls, mts)                              <- second mconcat . unzip . mconcat <$> mapM (makeClasses name cfg vars) specs
  (measures, cms', ms', cs', xs')         <- makeGhcSpecCHOP2 specs dcSs datacons cls embs
  (invs, ntys, ialias, sigs, asms)        <- makeGhcSpecCHOP3 cfg vars defVars specs name mts embs
  quals    <- mconcat <$> mapM makeQualifiers specs
  let fSyms =  freeSymbols xs' (sigs ++ asms ++ cs') ms' ((snd <$> invs) ++ (snd <$> ialias))
            ++ measureSymbols measures
  syms2    <- symbolVarMap (varInModule name) (vars ++ map fst cs') fSyms

  let syms  = syms0 ++ syms1 ++ syms2     -- BLOB-OF-FREE-SYMBOLS 


  let su    = mkSubst [ (x, mkVarExpr v) | (x, v) <- syms ]
  makeGhcSpec0 cfg defVars exports name adts (Ms.ignores fullSpec) (emptySpec cfg) 
    >>= makeGhcSpec1 syms vars defVars embs tyi exports name sigs (recSs ++ asms) cs'  ms' cms' su
    >>= makeGhcSpec2 invs ntys ialias measures su syms
    >>= makeGhcSpec3 (datacons ++ cls) tycons embs syms
    >>= makeSpecDictionaries embs vars specs
    -- The lifted-spec is saved in the next step
    >>= makeGhcAxioms file name embs cbs su specs lSpec0 invs adts
    >>= makeLogicMap
    -- RJ: AAAAAAARGHHH: this is duplicate of RT.strengthenDataConType
    -- >>= makeExactDataCons name cfg (snd <$> syms)
    -- This step needs the UPDATED logic map, ie should happen AFTER makeLogicMap
    >>= makeGhcSpec4 quals defVars specs name su syms
    >>= addRTEnv

measureSymbols :: MSpec SpecType DataCon -> [LocSymbol]
measureSymbols measures = zs
  where
    -- msg = "MEASURE-SYMBOLS" ++ showpp [(loc v, val v) | v <- zs]
    zs = [ msName m | m <- M.elems (Ms.measMap measures) ++ Ms.imeas measures ]

addRTEnv :: GhcSpec -> BareM GhcSpec
addRTEnv spec = do
  rt <- rtEnv <$> get
  return $ spec { gsRTAliases = rt }


varInModule :: (Show a, Show a1) => a -> a1 -> Bool
varInModule n v = L.isPrefixOf (show n) $ show v



-- TODO: pull the `makeLiftedSpec1` out; a function should do ONE thing.
makeGhcAxioms
  :: FilePath -> ModName -> TCEmb TyCon -> [CoreBind] -> Subst
  -> Bare.ModSpecs -> Ms.BareSpec
  -> [(Maybe Var, LocSpecType)] -> [F.DataDecl]
  -> GhcSpec
  -> BareM GhcSpec
makeGhcAxioms file name embs cbs su specs lSpec0 invs adts sp = do
  let mSpc = fromMaybe mempty (lookup name specs)
  let rfls = S.fromList (getReflects specs)
  xtes    <- makeHaskellAxioms embs cbs sp mSpc adts
  let xts  = [ (x, subst su t)       | (x, t, _) <- xtes ]

  let mAxs = [ qualifyAxiomEq x su e | (x, _, e) <- xtes ]  -- axiom-eqs in THIS module
  let iAxs = getAxiomEqs specs                              -- axiom-eqs from IMPORTED modules

  let axs  = mAxs ++ iAxs
  _       <- makeLiftedSpec1 file name lSpec0 xts mAxs invs
  let xts' = xts ++ F.notracepp "GS-ASMSIGS" (gsAsmSigs sp)
  let vts  = [ (v, t)        | (v, t) <- xts', let vx = GM.dropModuleNames $ symbol v, S.member vx rfls ]
  let msR  = [ (symbol v, t) | (v, t) <- vts ]
  let vs   = [ v             | (v, _) <- vts ]
  return   $ sp { gsAsmSigs  = xts'                   -- the IMPORTED refl-sigs are in gsAsmSigs sp
                , gsMeas     = msR ++ gsMeas     sp   -- we must add them to gsMeas to allow the names in specifications
                , gsReflects = vs  ++ gsReflects sp
                , gsAxioms   = axs ++ gsAxioms   sp
                }

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
  , gsADTs       = mempty
  , gsTgtVars    = mempty
  , gsIgnoreVars = mempty
  , gsDecr       = mempty
  , gsTexprs     = mempty
  , gsNewTypes   = mempty
  , gsLvars      = mempty
  , gsLazy       = mempty
  , gsStTerm     = mempty
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
             -> [F.DataDecl]
             -> S.HashSet LocSymbol
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec0 cfg defVars exports name adts ignoreVars sp = do
  targetVars <- makeTargetVars name defVars (checks cfg) 
  igVars     <- makeIgnoreVars name defVars ignoreVars 
  return      $ sp 
    { gsConfig     = cfg
    , gsExports    = exports
    , gsTgtVars    = targetVars
    , gsADTs       = adts
    , gsIgnoreVars = igVars 
    }


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
       asmSigs     <- F.notracepp "MAKE-ASSUME-SPEC-3" <$> (makePluggedAsmSigs embs tyi           $ tx asms)
       ctors       <- F.notracepp "MAKE-CTORS-SPEC"    <$> (makePluggedAsmSigs embs tyi           $ tx cs' )
       return $ sp { gsTySigs   = filter (\(v,_) -> v `elem` vs) tySigs
                   , gsAsmSigs  = filter (\(v,_) -> v `elem` vs) asmSigs
                   , gsCtors    = filter (\(v,_) -> v `elem` vs) ctors
                   , gsMeas     = measSyms
                   , gsLits     = measSyms -- RJ: we will be adding *more* things to `meas` but not `lits`
                   }
    where
      tx       = fmap . mapSnd . subst $ su
      tx'      = fmap (mapSnd $ fmap uRType)
      tx''     = fmap . mapFst . qualifySymbol $ syms
      vs       = S.fromList $ vars ++ defVars ++ (snd <$> syms)
      measSyms = tx'' . tx' . tx $ ms'
                                ++ (varMeasures vars)
                                ++ cms'



makeGhcSpec2 :: [(Maybe Var  , LocSpecType)]
             -> [(TyCon      , LocSpecType)]
             -> [(LocSpecType, LocSpecType)]
             -> MSpec SpecType DataCon
             -> Subst
             -> [(Symbol, Var)]
             -> GhcSpec
             -> BareM GhcSpec
makeGhcSpec2 invs ntys ialias measures su syms sp
  = return $ sp { gsInvariants = mapSnd (subst su) <$> invs
                , gsNewTypes   = mapSnd (subst su) <$> ntys
                , gsIaliases   = subst su ialias
                , gsMeasures   = ((qualifyMeasure syms . subst su) <$> (ms1 ++ ms2))
                }
    where
      ms1 = M.elems (Ms.measMap measures)
      ms2 =          Ms.imeas   measures

makeGhcSpec3 :: [(DataCon, DataConP)] -> [(TyCon, TyConP)] -> TCEmb TyCon -> [(Symbol, Var)]
             -> GhcSpec -> BareM GhcSpec
makeGhcSpec3 datacons tycons embs syms sp = do
  tce    <- tcEnv    <$> get
  return  $ sp { gsTyconEnv = tce
               , gsDconsP   = [ Loc (dc_loc z) (dc_locE z) dc | (dc, z) <- datacons]
               , gsTconsP   = [(tc, qualifyTyConP (qualifySymbol syms) tcp) | (tc, tcp) <- tycons]
               , gsTcEmbeds = embs
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
  sizes     <- if nostructuralT (getConfig sp) then return mempty else mkThing makeSize
  lazies    <- mkThing makeLazy
  lvars'    <- mkThing makeLVar
  autois    <- mkThing makeAutoInsts
  addDefs  =<< (qualifyDefs syms <$> mkThing makeDefs)
  asize'    <- S.fromList <$> makeASize
  hmeas     <- mkThing' True makeHMeas
  hinls     <- mkThing makeHInlines
  mapM_ (\(v, _) -> insertAxiom (val v) Nothing) $ S.toList hmeas
  mapM_ (\(v, _) -> insertAxiom (val v) Nothing) $ S.toList hinls
  mapM_ insertHMeasLogicEnv $ S.toList hmeas
  mapM_ insertHMeasLogicEnv $ S.toList hinls
  lmap'       <- logicEnv <$> get

  isgs        <- expand' $ strengthenHaskellInlines  (S.map fst hinls) (gsTySigs sp)
  gsTySigs'   <- expand' $ strengthenHaskellMeasures (S.map fst hmeas) isgs

  gsMeasures' <- expand' $ gsMeasures   sp
  gsAsmSigs'  <- expand' $ gsAsmSigs    sp
  gsInSigs'   <- expand' $ gsInSigs     sp
  gsInvarnts' <- expand' $ gsInvariants sp
  gsCtors'    <- expand' $ gsCtors      sp
  gsIaliases' <- expand' $ gsIaliases   sp
  let suUpdate v = makeSubst v (gsTySigs sp ++ gsAsmSigs sp ++ gsInSigs sp) (gsTySigs' ++ gsAsmSigs' ++ gsInSigs')
  return   $ sp { gsQualifiers = subst su quals
                , gsDecr       = decr'
                , gsLvars      = lvars'
                , gsAutoInst   = M.fromList $ S.toList autois
                , gsAutosize   = asize'
                , gsLazy       = S.insert dictionaryVar (lazies `mappend` sizes)
                , gsStTerm     = sizes
                , gsLogicMap   = lmap'
                , gsTySigs     = gsTySigs'
                , gsTexprs     = [ (v, subst (su `mappend` suUpdate v) es) | (v, es) <- gsTexprs' ]
                , gsMeasures   = gsMeasures'
                , gsAsmSigs    = gsAsmSigs'
                , gsInSigs     = gsInSigs'
                , gsInvariants = gsInvarnts'
                , gsCtors      = gsCtors'
                , gsIaliases   = gsIaliases'
                }
  where
    mkThing         = mkThing' False
    mkThing' b mk   = S.fromList . mconcat <$> sequence [ mk defVars s | (m, s) <- specs , b || m == name ]
    makeASize       = mapM (lookupGhcTyCon "makeASize") [v | (m, s) <- specs, m == name, v <- S.toList (Ms.autosize s)]
    makeSubst x old new
      | Just o <- L.lookup x old
      , Just n <- L.lookup x new
      = mkSubst (zip (getBinds o) (EVar <$> (getBinds n)))
    makeSubst _ _ _ = mkSubst []
    getBinds = ty_binds . toRTypeRep . val



insertHMeasLogicEnv :: (Located Var, LocSymbol) -> BareM ()
insertHMeasLogicEnv (x, s)
  = insertLogicEnv "insertHMeasLogicENV" s (fst <$> vxs) $ mkEApp s ((EVar . fst) <$> vxs)
  where
    -- res = ty_res rep
    rep = toRTypeRep  t
    t   = (ofType $ varType $ val x) :: SpecType
    xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs = dropWhile (isClassType.snd) $ zip xs (ty_args rep)


makeGhcSpecCHOP3 :: Config -> [Var] -> [Var] -> Bare.ModSpecs
                 -> ModName -> [(ModName, Var, LocSpecType)]
                 -> TCEmb TyCon
                 -> BareM ( [(Maybe Var, LocSpecType)]
                          , [(TyCon, LocSpecType)]
                          , [(LocSpecType, LocSpecType)]
                          , [(Var, LocSpecType)]
                          , [(Var, LocSpecType)] )
makeGhcSpecCHOP3 cfg vars defVars specs name mts embs = do
  sigs'    <- F.notracepp "MAKE-ASSERT-SPEC-1" <$> (mconcat <$> mapM (makeAssertSpec name cfg vars defVars) specs)
  asms'    <- F.notracepp "MAKE-ASSUME-SPEC-1" . Misc.fstByRank . mconcat <$> mapM (makeAssumeSpec name cfg vars defVars) specs
  invs     <- mconcat <$> mapM makeInvariants specs
  ialias   <- mconcat <$> mapM makeIAliases   specs
  ntys     <- mconcat <$> mapM makeNewTypes   specs
  let dms   = makeDefaultMethods vars mts
  tyi      <- gets tcEnv
  let sigs  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- sigs' ++ mts ++ dms ]
  let asms  = [ (x, txRefSort tyi embs $ fmap txExpToBind t) | (_, x, t) <- asms' ]
  let hms   = concatMap (S.toList . Ms.hmeas . snd) (filter ((== name) . fst) specs)
  let minvs = makeMeasureInvariants sigs hms
  checkDuplicateSigs sigs -- separate checks as assumes are supposed to "override" other sigs.
  return     (invs ++ minvs, ntys, ialias, sigs, asms)


checkDuplicateSigs :: [(Var, LocSpecType)] -> BareM ()
checkDuplicateSigs xts = case Misc.uniqueByKey symXs  of
  Left (k, ls) -> uError (errDupSpecs (pprint k) (GM.sourcePosSrcSpan <$> ls))
  Right _      -> return ()
  where
    symXs = [ (F.symbol x, F.loc t) | (x, t) <- xts ]

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

-- | GHC does a renaming step that assigns a Unique to each Id. It naturally
--   ensures that n in n = length xs and | i >= n are the SAME n, i.e. they have
--   the same Unique, but LH doesn't know anything about scopes when it
--   processes the RTypes, so the n in {Nat | i <= n} gets a random Unique
--   @replaceLocalBinds@'s job is to make sure the Uniques match see `LocalHole.hs`

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
                                   (RE M.empty ( F.notracepp "REPLACE-LOCAL" senv )  emb tyi))
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
      fenv = F.notracepp "FENV" $ L.foldl' (\m v -> insertSEnv (symbol v) (rTypeSortedReft emb (ofType $ varType v :: RSort)) m) fenv' vs
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
           let msg  = ErrTySpec (GM.sourcePosSrcSpan l) ( {- text "replaceLocalBindsOne" <+> -} pprint v) t'
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


varLocSimpleSym :: Var -> LocSymbol
varLocSimpleSym v = simpleSymbolVar <$> GM.locNamedThing v




-}
