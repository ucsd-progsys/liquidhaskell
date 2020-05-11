{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE OverloadedStrings         #-}

-- | This module contains the functions that convert /from/ descriptions of
--   symbols, names and types (over freshly parsed /bare/ Strings),
--   /to/ representations connected to GHC 'Var's, 'Name's, and 'Type's.
--   The actual /representations/ of bare and real (refinement) types are all
--   in 'RefType' -- they are different instances of 'RType'.

module Language.Haskell.Liquid.Bare (
  -- * Creating a TargetSpec
  -- $creatingTargetSpecs
    makeTargetSpec

  -- * Loading and Saving lifted specs from/to disk
  , loadLiftedSpec
  , saveLiftedSpec

  -- * Internal utilities
  , checkThrow
  ) where

import           Prelude                                    hiding (error)
import           Optics
import           Control.Monad                              (unless, when, void, forM)
import qualified Control.Exception                          as Ex
import qualified Data.Binary                                as B
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S
import           Text.PrettyPrint.HughesPJ                  hiding (first, (<>)) -- (text, (<+>))
import           System.Directory                           (doesFileExist)
import           System.Console.CmdArgs.Verbosity           (whenLoud)
import           Language.Fixpoint.Utils.Files             
import           Language.Fixpoint.Misc                     as Misc 
import           Language.Fixpoint.Types                    hiding (dcFields, DataDecl, Error, panic)
import qualified Language.Fixpoint.Types                    as F
import qualified Language.Haskell.Liquid.Misc               as Misc -- (nubHashOn)
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Language.Haskell.Liquid.GHC.API            as Ghc 
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn
import qualified Language.Haskell.Liquid.Measure            as Ms
import qualified Language.Haskell.Liquid.Bare.Types         as Bare 
import qualified Language.Haskell.Liquid.Bare.Resolve       as Bare 
import qualified Language.Haskell.Liquid.Bare.DataType      as Bare
import           Language.Haskell.Liquid.Bare.Elaborate
import qualified Language.Haskell.Liquid.Bare.Expand        as Bare 
import qualified Language.Haskell.Liquid.Bare.Measure       as Bare 
import qualified Language.Haskell.Liquid.Bare.Plugged       as Bare 
import qualified Language.Haskell.Liquid.Bare.Axiom         as Bare 
import qualified Language.Haskell.Liquid.Bare.ToBare        as Bare 
import qualified Language.Haskell.Liquid.Bare.Class         as Bare 
import qualified Language.Haskell.Liquid.Bare.Check         as Bare 
import qualified Language.Haskell.Liquid.Bare.Laws          as Bare
import qualified Language.Haskell.Liquid.Bare.Typeclass     as Bare 
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as CoreToLogic 
import           Control.Arrow                    (second)

--------------------------------------------------------------------------------
-- | De/Serializing Spec files
--------------------------------------------------------------------------------

loadLiftedSpec :: Config -> FilePath -> IO (Maybe Ms.BareSpec)
loadLiftedSpec cfg srcF
  | noLiftedImport cfg = putStrLn "No LIFTED Import" >> return Nothing 
  | otherwise          = do
      let specF = extFileName BinSpec srcF
      ex  <- doesFileExist specF
      whenLoud $ putStrLn $ "Loading Binary Lifted Spec: " ++ specF ++ " " ++ "for source-file: " ++ show srcF ++ " " ++ show ex
      lSp <- if ex 
               then Just <$> B.decodeFile specF 
               else (warnMissingLiftedSpec srcF specF >> return Nothing)
      Ex.evaluate lSp

warnMissingLiftedSpec :: FilePath -> FilePath -> IO () 
warnMissingLiftedSpec srcF specF = do 
  incDir <- Misc.getIncludeDir 
  unless (Misc.isIncludeFile incDir srcF)
    $ Ex.throw (errMissingSpec srcF specF) 

errMissingSpec :: FilePath -> FilePath -> UserError 
errMissingSpec srcF specF = ErrNoSpec Ghc.noSrcSpan (text srcF) (text specF)

-- saveLiftedSpec :: FilePath -> ModName -> Ms.BareSpec -> IO ()
saveLiftedSpec :: FilePath -> Ms.BareSpec -> IO () 
saveLiftedSpec srcF lspec = do
  ensurePath specF
  B.encodeFile specF lspec
  -- print (errorP "DIE" "HERE" :: String) 
  where
    specF = extFileName BinSpec srcF

{- $creatingTargetSpecs

/Liquid Haskell/ operates on 'TargetSpec's, so this module provides a single function called
'makeTargetSpec' to produce a 'TargetSpec', alongside the 'LiftedSpec'. The former will be used by
functions like 'liquid' or 'liquidOne' to verify our program is correct, the latter will be serialised
to disk so that we can retrieve it later without having to re-check the relevant Haskell file.
-}

-- | 'makeTargetSpec' constructs the 'TargetSpec' and then validates it. Upon success, the 'TargetSpec' 
-- and the 'LiftedSpec' are returned.
makeTargetSpec :: Config
               -> LogicMap
               -> TargetSrc
               -> BareSpec
               -> TargetDependencies
               -> Ghc.Ghc (Either [Error] (TargetSpec, LiftedSpec))
makeTargetSpec cfg lmap targetSrc bareSpec dependencies = 
  -- Check that our input 'BareSpec' doesn't contain duplicates.
  case Bare.checkBareSpec (giTargetMod targetSrc) (review bareSpecIso bareSpec) of
    Left errs -> pure $ Left errs
    Right validatedBareSpec -> do
      -- we should be able to setContext regardless of whether
      -- we use the ghc api. However, ghc will complain
      -- if the filename does not match the module name
      when (typeclass cfg) $ do
        Ghc.setContext [iimport |(modName, _) <- allSpecs validatedBareSpec,
                        let iimport = if isTarget modName
                                      then Ghc.IIModule (getModName modName)
                                      else Ghc.IIDecl (Ghc.simpleImportDecl (getModName modName))]
        void $ Ghc.execStmt
          "let {infixr 1 ==>; True ==> False = False; _ ==> _ = True}"
          Ghc.execOptions
        void $ Ghc.execStmt
          "let {infixr 1 <=>; True <=> False = False; _ <=> _ = True}"
          Ghc.execOptions
        void $ Ghc.execStmt
          "let {infix 4 ==; (==) :: a -> a -> Bool; _ == _ = undefined}"
          Ghc.execOptions
        void $ Ghc.execStmt
          "let {infix 4 /=; (/=) :: a -> a -> Bool; _ /= _ = undefined}"
          Ghc.execOptions
        void $ Ghc.execStmt
          "let {infixl 7 /; (/) :: Num a => a -> a -> a; _ / _ = undefined}"
          Ghc.execOptions        
      ghcSpec <- makeGhcSpec cfg (review targetSrcIso targetSrc) lmap (allSpecs validatedBareSpec)
      pure $ view targetSpecGetter <$> ghcSpec
  where
    toLegacyDep :: (StableModule, LiftedSpec) -> (ModName, Ms.BareSpec)
    toLegacyDep (sm, ls) = (ModName SrcImport (Ghc.moduleName . unStableModule $ sm), unsafeFromLiftedSpec ls)

    toLegacyTarget :: Ms.BareSpec -> (ModName, Ms.BareSpec)
    toLegacyTarget validatedSpec = (giTargetMod targetSrc, validatedSpec)

    allSpecs :: Ms.BareSpec -> [(ModName, Ms.BareSpec)]
    allSpecs validSpec = 
      toLegacyTarget validSpec : (map toLegacyDep . M.toList . getDependencies $ dependencies)

-------------------------------------------------------------------------------------
-- | @makeGhcSpec@ invokes @makeGhcSpec0@ to construct the @GhcSpec@ and then 
--   validates it using @checkGhcSpec@. 
-------------------------------------------------------------------------------------
makeGhcSpec :: Config 
            -> GhcSrc 
            -> LogicMap 
            -> [(ModName, Ms.BareSpec)] 
            -> Ghc.Ghc (Either [Error] GhcSpec)
-------------------------------------------------------------------------------------
makeGhcSpec cfg src lmap mspecs0  = do
  sp     <- makeGhcSpec0 cfg src lmap mspecs
  let renv             = ghcSpecEnv sp 
      _validTargetSpec = Bare.checkTargetSpec (map snd mspecs) 
                                           (view targetSrcIso src)
                                           renv 
                                           cbs 
                                           (fst . view targetSpecGetter $ sp)
  pure (_validTargetSpec >> pure sp)
  where 
    mspecs =  [ (m, checkThrow $ Bare.checkBareSpec m sp) | (m, sp) <- mspecs0, isTarget m ] 
           ++ [ (m, sp) | (m, sp) <- mspecs0, not (isTarget m)]
    cbs    = _giCbs src

checkThrow :: Ex.Exception e => Either e c -> c
checkThrow = either Ex.throw id 

ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp = fromListSEnv binds
  where
    emb       = gsTcEmbeds (_gsName sp)
    binds     = concat 
                 [ [(x,        rSort t) | (x, Loc _ _ t) <- gsMeas     (_gsData sp)]
                 , [(symbol v, rSort t) | (v, Loc _ _ t) <- gsCtors    (_gsData sp)]
                 , [(symbol v, vSort v) | v              <- gsReflects (_gsRefl sp)]
                 , [(x,        vSort v) | (x, v)         <- gsFreeSyms (_gsName sp), Ghc.isConLikeId v ]
                 , [(x, RR s mempty)    | (x, s)         <- wiredSortedSyms       ]
                 , [(x, RR s mempty)    | (x, s)         <- _gsImps sp       ]
                 ]
    vSort     = Bare.varSortedReft emb
    rSort     = rTypeSortedReft    emb


-------------------------------------------------------------------------------------
-- | @makeGhcSpec0@ slurps up all the relevant information needed to generate 
--   constraints for a target module and packages them into a @GhcSpec@ 
--   See [NOTE] LIFTING-STAGES to see why we split into lSpec0, lSpec1, etc.
--   essentially, to get to the `BareRTEnv` as soon as possible, as thats what
--   lets us use aliases inside data-constructor definitions.
-------------------------------------------------------------------------------------
makeGhcSpec0 :: Config -> GhcSrc ->  LogicMap -> [(ModName, Ms.BareSpec)] -> Ghc.Ghc GhcSpec
-------------------------------------------------------------------------------------
makeGhcSpec0 cfg src lmap mspecsNoCls = do
  tycEnv <- makeTycEnv1 name env (tycEnv0, datacons) coreToLg simplifier
  let tyi      = Bare.tcTyConMap   tycEnv 
  let sigEnv   = makeSigEnv  embs tyi (_gsExports src) rtEnv 
  let lSpec1   = lSpec0 <> makeLiftedSpec1 cfg src tycEnv lmap mySpec1 
  let mySpec   = mySpec2 <> lSpec1 
  let specs    = M.insert name mySpec iSpecs2
  let measEnv  = makeMeasEnv      env tycEnv sigEnv       specs 
  let sig      = makeSpecSig cfg name specs env sigEnv   tycEnv measEnv (_giCbs src)
  let myRTE    = myRTEnv       src env sigEnv rtEnv  
  let qual     = makeSpecQual cfg env tycEnv measEnv rtEnv specs 
  let sData    = makeSpecData  src env sigEnv measEnv sig specs 
  let refl     = makeSpecRefl  cfg src measEnv specs env name sig tycEnv 
  let laws     = makeSpecLaws env sigEnv (gsTySigs sig ++ gsAsmSigs sig) measEnv specs 
  elaboratedSig<- if allowTC then Bare.makeClassAuxTypes (elaborateSpecType coreToLg simplifier) datacons instMethods
                              >>= elaborateSig sig
                             else pure sig
  pure $ SP 
    { _gsConfig = cfg 
    , _gsImps   = makeImports mspecs
    , _gsSig    = addReflSigs refl elaboratedSig
    , _gsRefl   = refl 
    , _gsLaws   = laws 
    , _gsData   = sData 
    , _gsQual   = qual 
    , _gsName   = makeSpecName env     tycEnv measEnv   name 
    , _gsVars   = makeSpecVars cfg src mySpec env measEnv
    , _gsTerm   = makeSpecTerm cfg     mySpec env       name    
    , _gsLSpec  = makeLiftedSpec   src env refl sData elaboratedSig qual myRTE lSpec1 {
                     impSigs   = makeImports mspecs,
                     expSigs   = [ (F.symbol v, F.sr_sort $ Bare.varSortedReft embs v) | v <- gsReflects refl ],
                     dataDecls = dataDecls mySpec2 
                     } 
    }
  where
    -- typeclass elaboration
    allowTC    = typeclass cfg
    simplifier :: Ghc.CoreExpr -> Ghc.Ghc Ghc.CoreExpr
    simplifier = pure -- no simplification
    coreToLg e =
      case CoreToLogic.runToLogic
             embs
             lmap
             dm
             (\x -> todo Nothing ("coreToLogic not working " ++ x))
             (CoreToLogic.coreToLogic allowTC e) of
        Left _ -> impossible Nothing "can't reach here"
        Right e -> e    
    elaborateSig si auxsig = do
      tySigs <-
        forM (gsTySigs si) $ \(x, t) ->
          if Ghc.nameModule (Ghc.getName x) == Ghc.gHC_REAL then
            pure (x, t)
          else do t' <- traverse (elaborateSpecType coreToLg simplifier) t
                  pure (x, t')
      -- things like len breaks the code
      -- asmsigs should be elaborated only if they are from the current module
      -- asmSigs <- forM (gsAsmSigs si) $ \(x, t) -> do
      --   t' <- traverse (elaborateSpecType (pure ()) coreToLg) t
      --   pure (x, fst <$> t')
      pure
        si
          { gsTySigs = F.notracepp ("asmSigs" ++ F.showpp (gsAsmSigs si)) tySigs ++ auxsig  }

    -- build up environments
    (tycEnv0, datacons)   = makeTycEnv0   cfg name env embs mySpec2 iSpecs2 
    mySpec2  = Bare.qualifyExpand env name rtEnv l [] mySpec1    where l = F.dummyPos "expand-mySpec2"
    iSpecs2  = Bare.qualifyExpand env name rtEnv l [] iSpecs0    where l = F.dummyPos "expand-iSpecs2"
    rtEnv    = Bare.makeRTEnv env name mySpec1 iSpecs0 lmap  
    mspecs   = if allowTC then M.toList $ M.insert name mySpec0 iSpecs0 else mspecsNoCls
    (mySpec0, instMethods)  = if allowTC
                              then Bare.compileClasses src env (name, mySpec0NoCls) (M.toList iSpecs0)
                              else (mySpec0NoCls, [])
    mySpec1  = mySpec0 <> lSpec0    
    lSpec0   = makeLiftedSpec0 cfg src embs lmap mySpec0 
    embs     = makeEmbeds          src env ((name, mySpec0) : M.toList iSpecs0)
    dm       = Bare.tcDataConMap tycEnv0
    -- extract name and specs
    env      = Bare.makeEnv cfg src lmap mspecsNoCls
    (mySpec0NoCls, iSpecs0) = splitSpecs name mspecsNoCls
    -- check barespecs 
    name     = F.notracepp ("ALL-SPECS" ++ zzz) $ _giTargetMod  src 
    zzz      = F.showpp (fst <$> mspecs)

splitSpecs :: ModName -> [(ModName, Ms.BareSpec)] -> (Ms.BareSpec, Bare.ModSpecs) 
splitSpecs name specs = (mySpec, iSpecm) 
  where 
    mySpec            = mconcat (snd <$> mySpecs)
    (mySpecs, iSpecs) = L.partition ((name ==) . fst) specs 
    iSpecm            = fmap mconcat . Misc.group $ iSpecs


makeImports :: [(ModName, Ms.BareSpec)] -> [(F.Symbol, F.Sort)]
makeImports specs = concatMap (expSigs . snd) specs'
  where specs' = filter (isSrcImport . fst) specs


makeEmbeds :: GhcSrc -> Bare.Env -> [(ModName, Ms.BareSpec)] -> F.TCEmb Ghc.TyCon 
makeEmbeds src env 
  = Bare.addClassEmbeds (_gsCls src) (_gsFiTcs src) 
  . mconcat 
  . map (makeTyConEmbeds env)

makeTyConEmbeds :: Bare.Env -> (ModName, Ms.BareSpec) -> F.TCEmb Ghc.TyCon
makeTyConEmbeds env (name, spec) 
  = F.tceFromList [ (tc, t) | (c,t) <- F.tceToList (Ms.embeds spec), tc <- symTc c ]
    where
      symTc = Mb.maybeToList . Bare.maybeResolveSym env name "embed-tycon" 

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
makeLiftedSpec1 config src tycEnv lmap mySpec = mempty
  { Ms.measures  = Bare.makeHaskellMeasures (typeclass config) src tycEnv lmap mySpec }

--------------------------------------------------------------------------------
-- | [NOTE]: LIFTING-STAGES 
-- 
-- We split the lifting up into stage:
-- 0. Where we only lift inlines,
-- 1. Where we lift reflects, measures, and normalized tySigs
-- 
-- This is because we need the inlines to build the @BareRTEnv@ which then
-- does the alias @expand@ business, that in turn, lets us build the DataConP,
-- i.e. the refined datatypes and their associate selectors, projectors etc,
-- that are needed for subsequent stages of the lifting.
--------------------------------------------------------------------------------
makeLiftedSpec0 :: Config -> GhcSrc -> F.TCEmb Ghc.TyCon -> LogicMap -> Ms.BareSpec 
                -> Ms.BareSpec
makeLiftedSpec0 cfg src embs lmap mySpec = mempty
  { Ms.ealiases  = lmapEAlias . snd <$> Bare.makeHaskellInlines (typeclass cfg) src embs lmap mySpec 
  , Ms.reflects  = Ms.reflects mySpec
  , Ms.dataDecls = Bare.makeHaskellDataDecls cfg name mySpec tcs  
  }
  where 
    tcs          = uniqNub (_gsTcs src ++ refTcs)
    refTcs       = reflectedTyCons cfg embs cbs  mySpec
    cbs          = _giCbs       src
    name         = _giTargetMod src

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
makeSpecVars :: Config -> GhcSrc -> Ms.BareSpec -> Bare.Env -> Bare.MeasEnv -> GhcSpecVars 
------------------------------------------------------------------------------------------
makeSpecVars cfg src mySpec env measEnv = SpVar 
  { gsTgtVars    =   map (resolveStringVar  env name)              (checks     cfg) 
  , gsIgnoreVars = S.map (Bare.lookupGhcVar env name "gs-ignores") (Ms.ignores mySpec) 
  , gsLvars      = S.map (Bare.lookupGhcVar env name "gs-lvars"  ) (Ms.lvars   mySpec)
  , gsCMethods   = snd3 <$> Bare.meMethods measEnv 
  }
  where name     = _giTargetMod src 

qualifySymbolic :: (F.Symbolic a) => ModName -> a -> F.Symbol 
qualifySymbolic name s = GM.qualifySymbol (F.symbol name) (F.symbol s)

resolveStringVar :: Bare.Env -> ModName -> String -> Ghc.Var
resolveStringVar env name s = Bare.lookupGhcVar env name "resolve-string-var" lx
  where 
    lx                      = dummyLoc (qualifySymbolic name s)

------------------------------------------------------------------------------------------
makeSpecQual :: Config -> Bare.Env -> Bare.TycEnv -> Bare.MeasEnv -> BareRTEnv -> Bare.ModSpecs 
             -> GhcSpecQual 
------------------------------------------------------------------------------------------
makeSpecQual _cfg env tycEnv measEnv _rtEnv specs = SpQual 
  { gsQualifiers = filter okQual quals 
  , gsRTAliases  = [] -- makeSpecRTAliases env rtEnv -- TODO-REBARE
  } 
  where 
    quals        = concatMap (makeQualifiers env tycEnv) (M.toList specs) 
    -- mSyms        = F.tracepp "MSYMS" $ M.fromList (Bare.meSyms measEnv ++ Bare.meClassSyms measEnv)
    okQual q     = F.notracepp ("okQual: " ++ F.showpp q) 
                   $ all (`S.member` mSyms) (F.syms q)
    mSyms        = F.notracepp "MSYMS" . S.fromList 
                   $  (fst <$> wiredSortedSyms) 
                   ++ (fst <$> Bare.meSyms measEnv) 
                   ++ (fst <$> Bare.meClassSyms measEnv)

makeQualifiers :: Bare.Env -> Bare.TycEnv -> (ModName, Ms.Spec ty bndr) -> [F.Qualifier]
makeQualifiers env tycEnv (mod, spec) 
  = fmap        (Bare.qualifyTopDummy env        mod) 
  . Mb.mapMaybe (resolveQParams       env tycEnv mod)
  $ Ms.qualifiers spec 


-- | @resolveQualParams@ converts the sorts of parameters from, e.g. 
--     'Int' ===> 'GHC.Types.Int' or 
--     'Ptr' ===> 'GHC.Ptr.Ptr'  
--   It would not be required if _all_ qualifiers are scraped from 
--   function specs, but we're keeping it around for backwards compatibility.

resolveQParams :: Bare.Env -> Bare.TycEnv -> ModName -> F.Qualifier -> Maybe F.Qualifier 
resolveQParams env tycEnv name q = do 
     qps   <- mapM goQP (F.qParams q) 
     return $ q { F.qParams = qps } 
  where 
    goQP qp          = do { s <- go (F.qpSort qp) ; return qp { F.qpSort = s } } 
    go               :: F.Sort -> Maybe F.Sort   
    go (FAbs i s)    = FAbs i <$> go s
    go (FFunc s1 s2) = FFunc  <$> go s1 <*> go s2
    go (FApp  s1 s2) = FApp   <$> go s1 <*> go s2
    go (FTC c)       = qualifyFTycon env tycEnv name c 
    go s             = Just s 

qualifyFTycon :: Bare.Env -> Bare.TycEnv -> ModName -> F.FTycon -> Maybe F.Sort 
qualifyFTycon env tycEnv name c 
  | isPrimFTC           = Just (FTC c) 
  | otherwise           = tyConSort embs . F.atLoc tcs <$> ty 
  where       
    ty                  = Bare.maybeResolveSym env name "qualify-FTycon" tcs                
    isPrimFTC           = (F.val tcs) `elem` F.prims 
    tcs                 = F.fTyconSymbol c
    embs                = Bare.tcEmbs tycEnv 

tyConSort :: F.TCEmb Ghc.TyCon -> F.Located Ghc.TyCon -> F.Sort 
tyConSort embs lc = Mb.maybe s0 fst (F.tceLookup c embs)
  where 
    c             = F.val lc
    s0            = tyConSortRaw lc

tyConSortRaw :: F.Located Ghc.TyCon -> F.Sort 
tyConSortRaw = FTC . F.symbolFTycon . fmap F.symbol 

------------------------------------------------------------------------------------------
makeSpecTerm :: Config -> Ms.BareSpec -> Bare.Env -> ModName -> GhcSpecTerm 
------------------------------------------------------------------------------------------
makeSpecTerm cfg mySpec env name = SpTerm 
  { gsLazy       = S.insert dictionaryVar (lazies `mappend` sizes)
  , gsFail       = makeFail     env name mySpec 
  , gsStTerm     = sizes
  , gsAutosize   = autos 
  , gsDecr       = makeDecrs env name mySpec
  , gsNonStTerm  = mempty 
  }
  where  
    lazies       = makeLazy     env name mySpec
    autos        = makeAutoSize env name mySpec
    strT         = not (structuralTerm cfg) 
    sizes 
     | strT      = makeSize env name mySpec 
     | otherwise = mempty 

-- formerly, makeHints
makeDecrs :: Bare.Env -> ModName -> Ms.BareSpec -> [(Ghc.Var, [Int])] 
makeDecrs env name mySpec = 
  [ (v, z) | (lx, z) <- Ms.decr mySpec
           , let v    = Bare.lookupGhcVar env name "decreasing" lx
  ]

makeLazy :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet Ghc.Var
makeLazy env name spec = 
  S.map (Bare.lookupGhcVar env name "Var") (Ms.lazy spec)

makeFail :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet (Located Ghc.Var)
makeFail env name spec = 
  S.map (\x -> x{ val = Bare.lookupGhcVar env name "Var" x}) (Ms.fails spec)

makeRewrite :: Bare.Env -> ModName -> Ms.BareSpec -> S.HashSet (Located Ghc.Var)
makeRewrite env name spec = 
  S.map (\x -> x{ val = Bare.lookupGhcVar env name "Var" x}) (Ms.rewrites spec)

makeRewriteWith :: Bare.Env -> ModName -> Ms.BareSpec -> M.HashMap Ghc.Var [Ghc.Var]
makeRewriteWith env name spec = 
  M.fromList [ (lu x, lu <$> xs) | (x,xs) <- M.toList $ Ms.rewriteWith spec]
    where lu = Bare.lookupGhcVar env name "Var"  


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
makeSpecLaws :: Bare.Env -> Bare.SigEnv -> [(Ghc.Var,LocSpecType)] -> Bare.MeasEnv -> Bare.ModSpecs 
             -> GhcSpecLaws 
------------------------------------------------------------------------------------------
makeSpecLaws env sigEnv sigs menv specs = SpLaws 
  { gsLawDefs = second (map (\(_,x,y) -> (x,y))) <$> Bare.meCLaws menv  
  , gsLawInst = Bare.makeInstanceLaws env sigEnv sigs specs
  }

------------------------------------------------------------------------------------------
makeSpecRefl :: Config -> GhcSrc -> Bare.MeasEnv -> Bare.ModSpecs -> Bare.Env -> ModName -> GhcSpecSig -> Bare.TycEnv 
             -> GhcSpecRefl 
------------------------------------------------------------------------------------------
makeSpecRefl cfg src menv specs env name sig tycEnv = SpRefl 
  { gsLogicMap   = lmap 
  , gsAutoInst   = makeAutoInst env name mySpec 
  , gsImpAxioms  = concatMap (Ms.axeqs . snd) (M.toList specs)
  , gsMyAxioms   = F.notracepp "gsMyAxioms" myAxioms 
  , gsReflects   = F.notracepp "gsReflects" (lawMethods ++ filter (isReflectVar rflSyms) sigVars ++ wReflects)
  , gsHAxioms    = F.notracepp "gsHAxioms" xtes 
  , gsWiredReft  = wReflects
  , gsRewrites   = makeRewrite env name mySpec
  , gsRewritesWith = makeRewriteWith env name mySpec
  }
  where
    wReflects    = Bare.wiredReflects cfg env name sig
    lawMethods   = F.notracepp "Law Methods" $ concatMap Ghc.classMethods (fst <$> Bare.meCLaws menv) 
    mySpec       = M.lookupDefault mempty name specs 
    xtes         = Bare.makeHaskellAxioms cfg src env tycEnv name lmap sig mySpec
    myAxioms     = [ Bare.qualifyTop env name (F.loc lt) (e {eqName = symbol x}) | (x, lt, e) <- xtes]  
    rflSyms      = S.fromList (getReflects specs)
    sigVars      = F.notracepp "SIGVARS" $ (fst3 <$> xtes)            -- reflects
                                        ++ (fst  <$> gsAsmSigs sig)   -- assumes
                                        ++ (fst  <$> gsRefSigs sig)
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
addReflSigs refl sig = sig { gsRefSigs = reflSigs, gsAsmSigs = wreflSigs ++ filter notReflected (gsAsmSigs sig) }
  where 
    (wreflSigs, reflSigs)   = L.partition ((`elem` gsWiredReft refl) . fst) 
                                 [ (x, t) | (x, t, _) <- gsHAxioms refl ]   
    reflected       = fst <$> (wreflSigs ++ reflSigs)
    notReflected xt = fst xt `notElem` reflected

makeAutoInst :: Bare.Env -> ModName -> Ms.BareSpec -> M.HashMap Ghc.Var (Maybe Int)
makeAutoInst env name spec = Misc.hashMapMapKeys (Bare.lookupGhcVar env name "Var") (Ms.autois spec)

----------------------------------------------------------------------------------------
makeSpecSig :: Config -> ModName -> Bare.ModSpecs -> Bare.Env -> Bare.SigEnv -> Bare.TycEnv -> Bare.MeasEnv -> [Ghc.CoreBind]
            -> GhcSpecSig 
----------------------------------------------------------------------------------------
makeSpecSig cfg name specs env sigEnv tycEnv measEnv cbs = SpSig 
  { gsTySigs   = F.notracepp "gsTySigs"  tySigs 
  , gsAsmSigs  = F.notracepp "gsAsmSigs" asmSigs
  , gsRefSigs  = [] 
  , gsDicts    = dicts 
  , gsMethods  = if noclasscheck cfg then [] else Bare.makeMethodTypes (typeclass cfg) dicts (Bare.meClasses  measEnv) cbs 
  , gsInSigs   = mempty -- TODO-REBARE :: ![(Var, LocSpecType)]  
  , gsNewTypes = makeNewTypes env sigEnv allSpecs 
  , gsTexprs   = [ (v, t, es) | (v, t, Just es) <- mySigs ] 
  }
  where 
    dicts      = Bare.makeSpecDictionaries env sigEnv specs  
    mySpec     = M.lookupDefault mempty name specs
    asmSigs    = Bare.tcSelVars tycEnv 
              ++ makeAsmSigs env sigEnv name specs 
              ++ [ (x,t) | (_, x, t) <- concat $ map snd (Bare.meCLaws measEnv)]
    tySigs     = strengthenSigs . concat $ 
                  [ [(v, (0, t)) | (v, t,_) <- mySigs                         ]   -- NOTE: these weights are to priortize 
                  , [(v, (1, t)) | (v, t  ) <- makeMthSigs measEnv            ]   -- user defined sigs OVER auto-generated 
                  , [(v, (2, t)) | (v, t  ) <- makeInlSigs env rtEnv allSpecs ]   -- during the strengthening, i.e. to KEEP 
                  , [(v, (3, t)) | (v, t  ) <- makeMsrSigs env rtEnv allSpecs ]   -- the binders used in USER-defined sigs 
                  ]                                                               -- as they appear in termination metrics
    mySigs     = F.notracepp "MAKE-TYSIGS" $ makeTySigs  env sigEnv name mySpec
    allSpecs   = M.toList specs 
    rtEnv      = Bare.sigRTEnv sigEnv 
    -- hmeas      = makeHMeas    env allSpecs 

strengthenSigs :: [(Ghc.Var, (Int, LocSpecType))] ->[(Ghc.Var, LocSpecType)]
strengthenSigs sigs = go <$> Misc.groupList sigs 
  where
    go (v, ixs)     = (v,) $ L.foldl1' (flip meetLoc) (F.notracepp ("STRENGTHEN-SIGS: " ++ F.showpp v) (prio ixs))
    prio            = fmap snd . Misc.sortOn fst 
    meetLoc         :: LocSpecType -> LocSpecType -> LocSpecType
    meetLoc t1 t2   = t1 {val = val t1 `F.meet` val t2}

makeMthSigs :: Bare.MeasEnv -> [(Ghc.Var, LocSpecType)]
makeMthSigs measEnv = [ (v, t) | (_, v, t) <- Bare.meMethods measEnv ]

makeInlSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)] 
makeInlSigs env rtEnv 
  = makeLiftedSigs rtEnv (CoreToLogic.inlineSpecType (typeclass (getConfig env)))
  . makeFromSet "hinlines" Ms.inlines env 

makeMsrSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)] 
makeMsrSigs env rtEnv 
  = makeLiftedSigs rtEnv (CoreToLogic.inlineSpecType (typeclass (getConfig env)))
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

makeTySigs :: Bare.Env -> Bare.SigEnv -> ModName -> Ms.BareSpec 
           -> [(Ghc.Var, LocSpecType, Maybe [Located F.Expr])]
makeTySigs env sigEnv name spec 
              = [ (x, cook x bt, z) | (x, bt, z) <- rawSigs ]
  where 
    rawSigs   = Bare.resolveLocalBinds env expSigs 
    expSigs   = makeTExpr  env name bareSigs rtEnv spec 
    bareSigs  = bareTySigs env name                spec 
    rtEnv     = Bare.sigRTEnv sigEnv 
    cook x bt = Bare.cookSpecType env sigEnv name (Bare.HsTV x) bt 

bareTySigs :: Bare.Env -> ModName -> Ms.BareSpec -> [(Ghc.Var, LocBareType)]
bareTySigs env name spec = checkDuplicateSigs 
  [ (v, t) | (x, t) <- Ms.sigs spec ++ Ms.localSigs spec  
           , let v   = F.notracepp "LOOKUP-GHC-VAR" $ Bare.lookupGhcVar env name "rawTySigs" x 
  ] 

-- checkDuplicateSigs :: [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)] 
checkDuplicateSigs :: (Symbolic x) => [(x, F.Located t)] -> [(x, F.Located t)]
checkDuplicateSigs xts = case Misc.uniqueByKey symXs  of
  Left (k, ls) -> uError (errDupSpecs (pprint k) (GM.sourcePosSrcSpan <$> ls))
  Right _      -> xts 
  where
    symXs = [ (F.symbol x, F.loc t) | (x, t) <- xts ]


makeAsmSigs :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs -> [(Ghc.Var, LocSpecType)]
makeAsmSigs env sigEnv myName specs = 
  [ (x, t) | (name, x, bt) <- rawAsmSigs env myName specs
           , let t = Bare.cookSpecType env sigEnv name (Bare.LqTV x) bt
  ] 

rawAsmSigs :: Bare.Env -> ModName -> Bare.ModSpecs -> [(ModName, Ghc.Var, LocBareType)]
rawAsmSigs env myName specs = 
  [ (m, v, t) | (v, sigs) <- allAsmSigs env myName specs 
              , let (m, t) = myAsmSig v sigs 
  ] 
    
myAsmSig :: Ghc.Var -> [(Bool, ModName, LocBareType)] -> (ModName, LocBareType)
myAsmSig v sigs = Mb.fromMaybe errImp (Misc.firstMaybes [mbHome, mbImp]) 
  where 
    mbHome      = takeUnique err                  sigsHome 
    mbImp       = takeUnique err (Misc.firstGroup sigsImp) -- see [NOTE:Prioritize-Home-Spec] 
    sigsHome    = [(m, t)      | (True,  m, t) <- sigs ]
    sigsImp     = F.notracepp ("SIGS-IMP: " ++ F.showpp v)
                  [(d, (m, t)) | (False, m, t) <- sigs, let d = nameDistance vName m]
    err ts      = ErrDupSpecs (Ghc.getSrcSpan v) (F.pprint v) (GM.sourcePosSrcSpan . F.loc . snd <$> ts) :: UserError
    errImp      = impossible Nothing "myAsmSig: cannot happen as sigs is non-null"
    vName       = GM.takeModuleNames (F.symbol v)

makeTExpr :: Bare.Env -> ModName -> [(Ghc.Var, LocBareType)] -> BareRTEnv -> Ms.BareSpec 
          -> [(Ghc.Var, LocBareType, Maybe [Located F.Expr])]
makeTExpr env name tySigs rtEnv spec 
                = F.notracepp "MAKE-TEXPRS" 
                  [ (v, t, qual t <$> es) | (v, (t, es)) <- M.toList vSigExprs ] 
  where 
    qual t es   = qualifyTermExpr env name rtEnv t <$> es
    vSigExprs   = Misc.hashMapMapWithKey (\v t -> (t, M.lookup v vExprs)) vSigs 
    vExprs      = M.fromList (makeVarTExprs env name spec) 
    vSigs       = M.fromList tySigs 
                    
qualifyTermExpr :: Bare.Env -> ModName -> BareRTEnv -> LocBareType -> Located F.Expr 
                -> Located F.Expr 
qualifyTermExpr env name rtEnv t le 
        = F.atLoc le (Bare.qualifyExpand env name rtEnv l bs e)
  where 
    l   = F.loc le 
    e   = F.val le 
    bs  = ty_binds . toRTypeRep . val $ t 

makeVarTExprs :: Bare.Env -> ModName -> Ms.BareSpec -> [(Ghc.Var, [Located F.Expr])]
makeVarTExprs env name spec = 
  [ (Bare.lookupGhcVar env name "Var" x, es) 
      | (x, es) <- Ms.termexprs spec           ]
----------------------------------------------------------------------------------------
-- [NOTE:Prioritize-Home-Spec] Prioritize spec for THING defined in 
-- `Foo.Bar.Baz.Quux.x` over any other specification, IF GHC's 
-- fully qualified name for THING is `Foo.Bar.Baz.Quux.x`. 
--
-- For example, see tests/names/neg/T1078.hs for example, 
-- which assumes a spec for `head` defined in both 
-- 
--   (1) Data/ByteString.spec
--   (2) Data/ByteString/Char8.spec 
-- 
-- We end up resolving the `head` in (1) to the @Var@ `Data.ByteString.Char8.head` 
-- even though there is no exact match, just to account for re-exports of "internal"
-- modules and such (see `Resolve.matchMod`). However, we should pick the closer name
-- if its available.
----------------------------------------------------------------------------------------
nameDistance :: F.Symbol -> ModName -> Int 
nameDistance vName tName 
  | vName == F.symbol tName = 0 
  | otherwise               = 1


takeUnique :: Ex.Exception e => ([a] -> e) -> [a] -> Maybe a
takeUnique _ []  = Nothing 
takeUnique _ [x] = Just x 
takeUnique f xs  = Ex.throw (f xs) 

allAsmSigs :: Bare.Env -> ModName -> Bare.ModSpecs -> [(Ghc.Var, [(Bool, ModName, LocBareType)])]
allAsmSigs env myName specs = Misc.groupList
  [ (v, (must, name, t))  
      | (name, spec) <- M.toList specs
      , (must, x, t) <- getAsmSigs myName name spec
      , v            <- Mb.maybeToList (resolveAsmVar env name must x) 
  ] 

resolveAsmVar :: Bare.Env -> ModName -> Bool -> LocSymbol -> Maybe Ghc.Var 
resolveAsmVar env name True  lx = Just $ Bare.lookupGhcVar env name "resolveAsmVar-True"  lx
resolveAsmVar env name False lx = Bare.maybeResolveSym     env name "resolveAsmVar-False" lx  

getAsmSigs :: ModName -> ModName -> Ms.BareSpec -> [(Bool, LocSymbol, LocBareType)]  
getAsmSigs myName name spec 
  | myName == name = [ (True,  x,  t) | (x, t) <- Ms.asmSigs spec ] -- MUST    resolve, or error
  | otherwise      = [ (False, x', t) | (x, t) <- Ms.asmSigs spec 
                                                  ++ Ms.sigs spec
                                      , let x' = qSym x           ]  -- MAY-NOT resolve
  where 
    qSym           = fmap (GM.qualifySymbol ns) 
    ns             = F.symbol name

-- TODO-REBARE: grepClassAssumes
_grepClassAssumes :: [RInstance t] -> [(Located F.Symbol, t)]
_grepClassAssumes  = concatMap go
  where
    go    xts              = Mb.mapMaybe goOne (risigs xts)
    goOne (x, RIAssumed t) = Just (fmap (F.symbol . (".$c" ++ ) . F.symbolString) x, t)
    goOne (_, RISig _)     = Nothing

makeSigEnv :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> Ghc.NameSet -> BareRTEnv -> Bare.SigEnv 
makeSigEnv embs tyi exports rtEnv = Bare.SigEnv
  { sigEmbs     = embs 
  , sigTyRTyMap = tyi 
  , sigExports  = exports 
  , sigRTEnv    = rtEnv
  } 

makeNewTypes :: Bare.Env -> Bare.SigEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.TyCon, LocSpecType)]
makeNewTypes env sigEnv specs = 
  [ ct | (name, spec) <- specs
       , d            <- Ms.newtyDecls spec
       , ct           <- makeNewType env sigEnv name d 
  ] 

makeNewType :: Bare.Env -> Bare.SigEnv -> ModName -> DataDecl -> [(Ghc.TyCon, LocSpecType)]
makeNewType env sigEnv name d 
 | Just tc <- tcMb            = [(tc, t)] 
 | otherwise                  = []
  where 
    tcMb                      = Bare.lookupGhcDnTyCon env name "makeNewType" tcName
    tcName                    = tycName d
    t                         = Bare.cookSpecType env sigEnv name Bare.GenTV bt
    bt                        = getTy tcName (tycSrcPos d) (tycDCons d)
    getTy _ l [c]
      | [(_, t)] <- dcFields c = Loc l l t
    getTy n l _                = Ex.throw (err n l) 
    err n l                    = ErrOther (GM.sourcePosSrcSpan l) ("Bad new type declaration:" <+> F.pprint n) :: UserError

------------------------------------------------------------------------------------------
makeSpecData :: GhcSrc -> Bare.Env -> Bare.SigEnv -> Bare.MeasEnv -> GhcSpecSig -> Bare.ModSpecs
             -> GhcSpecData
------------------------------------------------------------------------------------------
makeSpecData src env sigEnv measEnv sig specs = SpData 
  { gsCtors      = -- F.notracepp "GS-CTORS" 
                   [ (x, tt) 
                       | (x, t) <- Bare.meDataCons measEnv
                       , let tt  = Bare.plugHoles (typeclass $ getConfig env) sigEnv name (Bare.LqTV x) t 
                   ]
  , gsMeas       = [ (F.symbol x, uRType <$> t) | (x, t) <- measVars ] 
  , gsMeasures   = Bare.qualifyTopDummy env name <$> (ms1 ++ ms2)
  , gsInvariants = Misc.nubHashOn (F.loc . snd) invs 
  , gsIaliases   = concatMap (makeIAliases env sigEnv) (M.toList specs)
  , gsUnsorted   = usI ++ (concatMap msUnSorted $ concatMap measures specs)
  }
  where
    measVars     = Bare.meSyms      measEnv -- ms'
                ++ Bare.meClassSyms measEnv -- cms' 
                ++ Bare.varMeasures env
    measuresSp   = Bare.meMeasureSpec measEnv  
    ms1          = M.elems (Ms.measMap measuresSp)
    ms2          =          Ms.imeas   measuresSp
    mySpec       = M.lookupDefault mempty name specs
    name         = _giTargetMod      src
    (minvs,usI)  = makeMeasureInvariants env name sig mySpec
    invs         = minvs ++ concat (makeInvariants env sigEnv <$> M.toList specs)

makeIAliases :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> [(LocSpecType, LocSpecType)]
makeIAliases env sigEnv (name, spec)
  = [ z | Right z <- mkIA <$> Ms.ialiases spec ]
  where 
    -- mkIA :: (LocBareType, LocBareType) -> Either _ (LocSpecType, LocSpecType)
    mkIA (t1, t2) = (,) <$> mkI t1 <*> mkI t2
    mkI           = Bare.cookSpecTypeE env sigEnv name Bare.GenTV 

makeInvariants :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> [(Maybe Ghc.Var, Located SpecType)]
makeInvariants env sigEnv (name, spec) = 
  [ (Nothing, t) 
    | (_, bt) <- Ms.invariants spec 
    , Bare.knownGhcType env name bt
    , let t = Bare.cookSpecType env sigEnv name Bare.GenTV bt
  ]

makeMeasureInvariants :: Bare.Env -> ModName -> GhcSpecSig -> Ms.BareSpec 
                      -> ([(Maybe Ghc.Var, LocSpecType)], [UnSortedExpr])
makeMeasureInvariants env name sig mySpec 
  = mapSnd Mb.catMaybes $ 
    unzip (measureTypeToInv env name <$> [(x, (y, ty)) | x <- xs, (y, ty) <- sigs
                                         , isSymbolOfVar (val x) y ])
  where 
    sigs = gsTySigs sig 
    xs   = S.toList (Ms.hmeas  mySpec) 

isSymbolOfVar :: Symbol -> Ghc.Var -> Bool
isSymbolOfVar x v = x == symbol' v
  where
    symbol' :: Ghc.Var -> Symbol
    symbol' = GM.dropModuleNames . symbol . Ghc.getName

measureTypeToInv :: Bare.Env -> ModName -> (LocSymbol, (Ghc.Var, LocSpecType)) -> ((Maybe Ghc.Var, LocSpecType), Maybe UnSortedExpr)
measureTypeToInv env name (x, (v, t)) 
  = notracepp "measureTypeToInv" $ ((Just v, t {val = Bare.qualifyTop env name (F.loc x) mtype}), usorted)
  where
    trep = toRTypeRep (val t)
    ts   = ty_args  trep
    args = ty_binds trep
    res  = ty_res   trep
    z    = last args
    tz   = last ts
    usorted = if isSimpleADT tz then Nothing else ((mapFst (:[])) <$> mkReft (dummyLoc $ F.symbol v) z tz res)
    mtype
      | null ts 
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x) "Measure has no arguments!"
      | otherwise 
      = mkInvariant x z tz res 
    isSimpleADT (RApp _ ts _ _) = all isRVar ts 
    isSimpleADT _               = False 

mkInvariant :: LocSymbol -> Symbol -> SpecType -> SpecType -> SpecType
mkInvariant x z t tr = strengthen (top <$> t) (MkUReft reft mempty)
      where
        reft  = Mb.maybe mempty Reft mreft
        mreft = mkReft x z t tr 


mkReft :: LocSymbol -> Symbol -> SpecType -> SpecType -> Maybe (Symbol, Expr)
mkReft x z _t tr 
  | Just q <- stripRTypeBase tr
  = let Reft (v, p) = toReft q
        su          = mkSubst [(v, mkEApp x [EVar v])]
        p'          = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p
    in  Just (v, subst su p')
mkReft _ _ _ _  
  = Nothing 


-- REBARE: formerly, makeGhcSpec3
-------------------------------------------------------------------------------------------
makeSpecName :: Bare.Env -> Bare.TycEnv -> Bare.MeasEnv -> ModName -> GhcSpecNames
-------------------------------------------------------------------------------------------
makeSpecName env tycEnv measEnv name = SpNames 
  { gsFreeSyms = Bare.reSyms env 
  , gsDconsP   = [ F.atLoc dc (dcpCon dc) | dc <- datacons ++ cls ] 
  , gsTconsP   = Bare.qualifyTopDummy env name <$> tycons                
  -- , gsLits = mempty                                              -- TODO-REBARE, redundant with gsMeas
  , gsTcEmbeds = Bare.tcEmbs     tycEnv   
  , gsADTs     = Bare.tcAdts     tycEnv 
  , gsTyconEnv = Bare.tcTyConMap tycEnv  
  }
  where 
    datacons, cls :: [DataConP]
    datacons   = Bare.tcDataCons tycEnv 
    cls        = F.tracepp "meClasses" $ Bare.meClasses measEnv 
    tycons     = Bare.tcTyCons   tycEnv 


-- REBARE: formerly, makeGhcCHOP1
-- split into two to break circular dependency. we need dataconmap for core2logic
-------------------------------------------------------------------------------------------
makeTycEnv0 :: Config -> ModName -> Bare.Env -> TCEmb Ghc.TyCon -> Ms.BareSpec -> Bare.ModSpecs 
           -> (Bare.TycEnv, [Located DataConP] )
-------------------------------------------------------------------------------------------
makeTycEnv0 cfg myName env embs mySpec iSpecs = (,datacons) $ Bare.TycEnv 
  { tcTyCons      = tycons                  
  , tcDataCons    = mempty -- val <$> datacons 
  , tcSelMeasures = dcSelectors             
  , tcSelVars     = mempty -- recSelectors            
  , tcTyConMap    = tyi                     
  , tcAdts        = adts                    
  , tcDataConMap  = dm
  , tcEmbs        = embs
  , tcName        = myName
  }
  where 
    (tcDds, dcs)  = Misc.concatUnzip $ Bare.makeConTypes env <$> specs 
    specs         = (myName, mySpec) : M.toList iSpecs
    tcs           = Misc.snd3 <$> tcDds 
    tyi           = Bare.qualifyTopDummy env myName (makeTyConInfo embs fiTcs tycons)
    -- tycons        = F.tracepp "TYCONS" $ Misc.replaceWith tcpCon tcs wiredTyCons
    -- datacons      =  Bare.makePluggedDataCons embs tyi (Misc.replaceWith (dcpCon . val) (F.tracepp "DATACONS" $ concat dcs) wiredDataCons)
    tycons        = tcs ++ knownWiredTyCons env myName 
    datacons      = Bare.makePluggedDataCon (typeclass cfg) embs tyi <$> (concat dcs ++ knownWiredDataCons env myName)
    tds           = [(name, tcpCon tcp, dd) | (name, tcp, Just dd) <- tcDds]
    adts          = Bare.makeDataDecls cfg embs myName tds       datacons
    dm            = Bare.dataConMap adts
    dcSelectors   = concatMap (Bare.makeMeasureSelectors cfg dm) datacons
    fiTcs         = _gsFiTcs (Bare.reSrc env)


makeTycEnv1 ::
     ModName
  -> Bare.Env
  -> (Bare.TycEnv, [Located DataConP])
  -> (Ghc.CoreExpr -> F.Expr)
  -> (Ghc.CoreExpr -> Ghc.Ghc Ghc.CoreExpr)
  -> Ghc.Ghc Bare.TycEnv
makeTycEnv1 myName env (tycEnv, datacons) coreToLg simplifier = do
  -- fst for selector generation, snd for dataconsig generation
  lclassdcs <- forM classdcs $ traverse (Bare.elaborateClassDcp coreToLg simplifier)
  let recSelectors = Bare.makeRecordSelectorSigs env myName (dcs ++ (fmap . fmap) snd lclassdcs)
  pure $
    tycEnv {Bare.tcSelVars = recSelectors, Bare.tcDataCons = F.val <$> ((fmap . fmap) fst lclassdcs ++ dcs )}
  where
    (classdcs, dcs) =
      L.partition
        (Ghc.isClassTyCon . Ghc.dataConTyCon . dcpCon . F.val)
        datacons

    
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
  , meMethods     = mts ++ dms 
  , meCLaws       = laws
  }
  where 
    measures      = mconcat (Ms.mkMSpec' dcSelectors : (Bare.makeMeasureSpec env sigEnv name <$> M.toList specs))
    (cs, ms)      = Bare.makeMeasureSpec' (typeclass $ getConfig env)   measures
    cms           = Bare.makeClassMeasureSpec measures
    cms'          = [ (x, Loc l l' $ cSort t)  | (Loc l l' x, t) <- cms ]
    ms'           = [ (F.val lx, F.atLoc lx t) | (lx, t) <- ms
                                               , Mb.isNothing (lookup (val lx) cms') ]
    cs'           = [ (v, txRefs v t) | (v, t) <- Bare.meetDataConSpec (typeclass (getConfig env)) embs cs (datacons ++ cls)]
    txRefs v t    = Bare.txRefSort tyi embs (const t <$> GM.locNamedThing v) 
    -- unpacking the environment
    tyi           = Bare.tcTyConMap    tycEnv 
    dcSelectors   = Bare.tcSelMeasures tycEnv 
    datacons      = Bare.tcDataCons    tycEnv 
    embs          = Bare.tcEmbs        tycEnv 
    name          = Bare.tcName        tycEnv
    dms           = Bare.makeDefaultMethods env mts  
    (cls, mts)    = Bare.makeClasses        env sigEnv name specs
    laws          = Bare.makeCLaws env sigEnv name specs

-----------------------------------------------------------------------------------------
-- | @makeLiftedSpec@ is used to generate the BareSpec object that should be serialized 
--   so that downstream files that import this target can access the lifted definitions, 
--   e.g. for measures, reflected functions etc.
-----------------------------------------------------------------------------------------
makeLiftedSpec :: GhcSrc -> Bare.Env 
               -> GhcSpecRefl -> GhcSpecData -> GhcSpecSig -> GhcSpecQual -> BareRTEnv 
               -> Ms.BareSpec -> Ms.BareSpec 
-----------------------------------------------------------------------------------------
makeLiftedSpec src _env refl sData sig qual myRTE lSpec0 = lSpec0 
  { Ms.asmSigs    = F.notracepp   "LIFTED-ASM-SIGS" $ xbs -- ++ mkSigs (gsAsmSigs sig)
  , Ms.reflSigs   = F.notracepp "REFL-SIGS"         xbs
  , Ms.sigs       = F.notracepp   "LIFTED-SIGS"     $        mkSigs (gsTySigs sig)  
  , Ms.invariants = [ ((varLocSym <$> x), Bare.specToBare <$> t) 
                       | (x, t) <- gsInvariants sData 
                       , isLocInFile srcF t
                    ]
  , Ms.axeqs      = gsMyAxioms refl 
  , Ms.aliases    = F.notracepp "MY-ALIASES" $ M.elems . typeAliases $ myRTE
  , Ms.ealiases   = M.elems . exprAliases $ myRTE 
  , Ms.qualifiers = filter (isLocInFile srcF) (gsQualifiers qual)
  }
  where
    mkSigs xts    = [ toBare (x, t) | (x, t) <- xts,  S.member x sigVars && (isExported src x) ] 
    toBare (x, t) = (varLocSym x, Bare.specToBare <$> t)
    xbs           = toBare <$> reflTySigs 
    sigVars       = S.difference defVars reflVars
    defVars       = S.fromList (_giDefVars src)
    reflTySigs    = [(x, t) | (x,t,_) <- gsHAxioms refl, x `notElem` gsWiredReft refl]
    reflVars      = S.fromList (fst <$> reflTySigs)
    -- myAliases fld = M.elems . fld $ myRTE 
    srcF          = _giTarget src 

isExported :: GhcSrc -> Ghc.Var -> Bool
isExported info v = n `Ghc.elemNameSet` ns
  where
    n                = Ghc.getName v
    ns               = _gsExports info

isLocInFile :: (F.Loc a) => FilePath -> a ->  Bool 
isLocInFile f lx = f == (locFile lx) 

locFile :: (F.Loc a) => a -> FilePath 
locFile = Misc.fst3 . F.sourcePosElts . F.sp_start . F.srcSpan

varLocSym :: Ghc.Var -> LocSymbol
varLocSym v = F.symbol <$> GM.locNamedThing v

-- makeSpecRTAliases :: Bare.Env -> BareRTEnv -> [Located SpecRTAlias]
-- makeSpecRTAliases _env _rtEnv = [] -- TODO-REBARE 


--------------------------------------------------------------------------------
-- | @myRTEnv@ slices out the part of RTEnv that was generated by aliases defined 
--   in the _target_ file, "cooks" the aliases (by conversion to SpecType), and 
--   then saves them back as BareType.
--------------------------------------------------------------------------------
myRTEnv :: GhcSrc -> Bare.Env -> Bare.SigEnv -> BareRTEnv -> BareRTEnv 
myRTEnv src env sigEnv rtEnv = mkRTE tAs' eAs 
  where 
    tAs'                     = normalizeBareAlias env sigEnv name <$> tAs
    tAs                      = myAliases typeAliases 
    eAs                      = myAliases exprAliases 
    myAliases fld            = filter (isLocInFile srcF) . M.elems . fld $ rtEnv 
    srcF                     = _giTarget    src
    name                     = _giTargetMod src
  
mkRTE :: [Located (RTAlias x a)] -> [Located (RTAlias F.Symbol F.Expr)] -> RTEnv x a 
mkRTE tAs eAs   = RTE 
  { typeAliases = M.fromList [ (aName a, a) | a <- tAs ] 
  , exprAliases = M.fromList [ (aName a, a) | a <- eAs ] 
  } 
  where aName   = rtName . F.val  

normalizeBareAlias :: Bare.Env -> Bare.SigEnv -> ModName -> Located BareRTAlias 
                   -> Located BareRTAlias 
normalizeBareAlias env sigEnv name lx = fixRTA <$> lx
  where 
    fixRTA  :: BareRTAlias -> BareRTAlias 
    fixRTA  = mapRTAVars fixArg . fmap fixBody 

    fixArg  :: Symbol -> Symbol 
    fixArg  = F.symbol . GM.symbolTyVar 
      
    fixBody :: BareType -> BareType 
    fixBody = Bare.specToBare 
            . F.val 
            . Bare.cookSpecType env sigEnv name Bare.RawTV 
            . F.atLoc lx

