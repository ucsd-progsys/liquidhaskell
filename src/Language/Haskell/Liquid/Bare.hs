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
  ) where

import           Prelude                                    hiding (error)
import           Optics
import           Control.Monad                              (unless, forM)
import           Control.Applicative                        ((<|>))
import qualified Control.Exception                          as Ex
import qualified Data.Binary                                as B
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S
import           Text.PrettyPrint.HughesPJ                  hiding (first, (<>)) -- (text, (<+>))
import           System.FilePath                            (dropExtension)
import           System.Directory                           (doesFileExist)
import           System.Console.CmdArgs.Verbosity           (whenLoud)
import           Language.Fixpoint.Utils.Files              as Files
import           Language.Fixpoint.Misc                     as Misc 
import           Language.Fixpoint.Types                    hiding (dcFields, DataDecl, Error, panic)
import qualified Language.Fixpoint.Types                    as F
import qualified Language.Haskell.Liquid.Misc               as Misc -- (nubHashOn)
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Language.Haskell.Liquid.GHC.API            as Ghc 
import           Language.Haskell.Liquid.GHC.Types          (StableName)
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
import Data.Hashable (Hashable)
import qualified Language.Haskell.Liquid.Bare.Slice as Dg

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
               else {- warnMissingLiftedSpec srcF specF >> -} return Nothing
      Ex.evaluate lSp

-- warnMissingLiftedSpec :: FilePath -> FilePath -> IO () 
-- warnMissingLiftedSpec srcF specF = do 
--   incDir <- Misc.getIncludeDir 
--   unless (Misc.isIncludeFile incDir srcF)
--     $ Ex.throw (errMissingSpec srcF specF) 

errMissingSpec :: FilePath -> FilePath -> UserError 
errMissingSpec srcF specF = ErrNoSpec Ghc.noSrcSpan (text srcF) (text specF)

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
-- and the 'LiftedSpec' are returned. We perform error checking in \"two phases\": during the first phase,
-- we check for errors and warnings in the input 'BareSpec' and the dependencies. During this phase we ideally
-- want to short-circuit in case the validation failure is found in one of the dependencies (to avoid
-- printing potentially endless failures).
-- The second phase involves creating the 'TargetSpec', and returning either the full list of diagnostics
-- (errors and warnings) in case things went wrong, or the final 'TargetSpec' and 'LiftedSpec' together
-- with a list of 'Warning's, which shouldn't abort the compilation (modulo explicit request from the user,
-- to treat warnings and errors).
makeTargetSpec :: Config
               -> LogicMap
               -> TargetSrc
               -> BareSpec
               -> TargetDependencies
               -> Ghc.TcRn (Either Diagnostics ([Warning], TargetSpec, LiftedSpec))
makeTargetSpec cfg lmap targetSrc bareSpec dependencies = do
  let depsDiagnostics     = mapM (uncurry Bare.checkBareSpec) legacyDependencies
  let bareSpecDiagnostics = Bare.checkBareSpec (giTargetMod targetSrc) legacyBareSpec
  case depsDiagnostics >> bareSpecDiagnostics of
   Left d | noErrors d -> secondPhase (allWarnings d)
   Left d              -> return $ Left d
   Right ()            -> secondPhase mempty
  where
    secondPhase :: [Warning] -> Ghc.TcRn (Either Diagnostics ([Warning], TargetSpec, LiftedSpec))
    secondPhase phaseOneWarns = do

      -- we should be able to setContext regardless of whether
      -- we use the ghc api. However, ghc will complain
      -- if the filename does not match the module name
      -- when (typeclass cfg) $ do
      --   Ghc.setContext [iimport |(modName, _) <- allSpecs legacyBareSpec,
      --                   let iimport = if isTarget modName
      --                                 then Ghc.IIModule (getModName modName)
      --                                 else Ghc.IIDecl (Ghc.simpleImportDecl (getModName modName))]
      --   void $ Ghc.execStmt
      --     "let {infixr 1 ==>; True ==> False = False; _ ==> _ = True}"
      --     Ghc.execOptions
      --   void $ Ghc.execStmt
      --     "let {infixr 1 <=>; True <=> False = False; _ <=> _ = True}"
      --     Ghc.execOptions
      --   void $ Ghc.execStmt
      --     "let {infix 4 ==; (==) :: a -> a -> Bool; _ == _ = undefined}"
      --     Ghc.execOptions
      --   void $ Ghc.execStmt
      --     "let {infix 4 /=; (/=) :: a -> a -> Bool; _ /= _ = undefined}"
      --     Ghc.execOptions
      --   void $ Ghc.execStmt
      --     "let {infixl 7 /; (/) :: Num a => a -> a -> a; _ / _ = undefined}"
      --     Ghc.execOptions        
      --   void $ Ghc.execStmt
      --     "let {len :: [a] -> Int; len _ = undefined}"
      --     Ghc.execOptions        

      diagOrSpec <- makeGhcSpec cfg (review targetSrcIso targetSrc) lmap (allSpecs legacyBareSpec)
      return $ do
        (warns, ghcSpec) <- diagOrSpec
        let (targetSpec, liftedSpec) = view targetSpecGetter ghcSpec
        pure (phaseOneWarns <> warns, targetSpec, liftedSpec)

    toLegacyDep :: (Ghc.StableModule, LiftedSpec) -> (ModName, Ms.BareSpec)
    toLegacyDep (sm, ls) = (ModName SrcImport (Ghc.moduleName . Ghc.unStableModule $ sm), unsafeFromLiftedSpec ls)

    toLegacyTarget :: Ms.BareSpec -> (ModName, Ms.BareSpec)
    toLegacyTarget validatedSpec = (giTargetMod targetSrc, validatedSpec)

    legacyDependencies :: [(ModName, Ms.BareSpec)]
    legacyDependencies = map toLegacyDep . M.toList . getDependencies $ dependencies

    allSpecs :: Ms.BareSpec -> [(ModName, Ms.BareSpec)]
    allSpecs validSpec = toLegacyTarget validSpec : legacyDependencies

    legacyBareSpec :: Spec LocBareType F.LocSymbol
    legacyBareSpec = review bareSpecIso bareSpec

-------------------------------------------------------------------------------------
-- | @makeGhcSpec@ invokes @makeGhcSpec0@ to construct the @GhcSpec@ and then
--   validates it using @checkGhcSpec@.
-------------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> GhcSrc
            -> LogicMap
            -> [(ModName, Ms.BareSpec)]
            -> Ghc.TcRn (Either Diagnostics ([Warning], GhcSpec))
-------------------------------------------------------------------------------------
makeGhcSpec cfg src lmap validatedSpecs = do
  (dg0, sp) <- makeGhcSpec0 cfg src lmap validatedSpecs
  let diagnostics = Bare.checkTargetSpec (map snd validatedSpecs)
                                         (view targetSrcIso src)
                                         (ghcSpecEnv sp)
                                         (_giCbs src)
                                         (fst . view targetSpecGetter $ sp)
  pure $ if not (noErrors dg0) then Left dg0 else 
           case diagnostics of
             Left dg1 
               | noErrors dg1 -> pure (allWarnings dg1, sp)
               | otherwise    -> Left dg1
             Right ()         -> pure (mempty, sp)


ghcSpecEnv :: GhcSpec -> SEnv SortedReft
ghcSpecEnv sp = F.notracepp "RENV" $ fromListSEnv binds
  where
    emb       = gsTcEmbeds (_gsName sp)
    binds     = F.notracepp "binds" $ concat 
                 [ [(x,        rSort t) | (x, Loc _ _ t)  <- gsMeas     (_gsData sp)]
                 , [(symbol v, rSort t) | (v, Loc _ _ t)  <- gsCtors    (_gsData sp)]
                 , [(symbol v, vSort v) | v               <- gsReflects (_gsRefl sp)]
                 , [(x,        vSort v) | (x, v)          <- gsFreeSyms (_gsName sp), Ghc.isConLikeId v ]
                 , [(x, RR s mempty)    | (x, s)          <- wiredSortedSyms       ]
                 , [(x, RR s mempty)    | (x, s)          <- _gsImps sp       ]
                 ]
    vSort     = rSort . classRFInfoType (typeclass $ getConfig sp) .
                (ofType :: Ghc.Type -> SpecType) . Ghc.varType
    rSort     = rTypeSortedReft    emb


-------------------------------------------------------------------------------------
-- | @makeGhcSpec0@ slurps up all the relevant information needed to generate 
--   constraints for a target module and packages them into a @GhcSpec@ 
--   See [NOTE] LIFTING-STAGES to see why we split into lSpec0, lSpec1, etc.
--   essentially, to get to the `BareRTEnv` as soon as possible, as thats what
--   lets us use aliases inside data-constructor definitions.
-------------------------------------------------------------------------------------
makeGhcSpec0 :: Config -> GhcSrc ->  LogicMap -> [(ModName, Ms.BareSpec)] -> 
                Ghc.TcRn (Diagnostics, GhcSpec)
makeGhcSpec0 cfg src lmap mspecsNoCls = do
  -- build up environments
  tycEnv <- makeTycEnv1 cfg name env (tycEnv0, datacons) coreToLg simplifier
  let tyi      = Bare.tcTyConMap   tycEnv 
  let sigEnv   = makeSigEnv  embs tyi (_gsExports src) rtEnv 
  let lSpec1   = lSpec0 <> makeLiftedSpec1 cfg src tycEnv lmap mySpec1 
  let mySpec   = mySpec2 <> lSpec1 
  let specs    = M.insert name mySpec iSpecs2
  let myRTE    = myRTEnv       src env sigEnv rtEnv  
  let (dg5, measEnv) = withDiagnostics $ makeMeasEnv      env tycEnv sigEnv       specs 
  let (dg4, sig) = withDiagnostics $ makeSpecSig cfg name specs env sigEnv   tycEnv measEnv (_giCbs src)
  elaboratedSig <-
    if allowTC then Bare.makeClassAuxTypes (elaborateSpecType coreToLg simplifier) datacons instMethods
                              >>= elaborateSig sig
               else pure sig
  let qual     = makeSpecQual cfg env tycEnv measEnv rtEnv specs 
  let sData    = makeSpecData  src env sigEnv measEnv elaboratedSig specs 
  let (dg1, spcVars) = withDiagnostics $ makeSpecVars cfg src mySpec env measEnv
  let (dg2, spcTerm) = withDiagnostics $ makeSpecTerm cfg     mySpec env       name    
  let (dg3, refl)    = withDiagnostics $ makeSpecRefl cfg src measEnv specs env name elaboratedSig tycEnv 
  let laws     = makeSpecLaws env sigEnv (gsTySigs elaboratedSig ++ gsAsmSigs elaboratedSig) measEnv specs 
  let finalLiftedSpec = makeLiftedSpec name src env refl sData elaboratedSig qual myRTE lSpec1
  let diags    = mconcat [dg0, dg1, dg2, dg3, dg4, dg5]

  pure (diags, SP 
    { _gsConfig = cfg 
    , _gsImps   = makeImports mspecs
    , _gsSig    = addReflSigs env name rtEnv refl elaboratedSig
    , _gsRefl   = refl 
    , _gsLaws   = laws 
    , _gsData   = sData 
    , _gsQual   = qual 
    , _gsName   = makeSpecName env     tycEnv measEnv   name 
    , _gsVars   = spcVars
    , _gsTerm   = spcTerm

    , _gsLSpec  = finalLiftedSpec
                { impSigs   = makeImports mspecs
                , expSigs   = [ (F.symbol v, F.sr_sort $ Bare.varSortedReft embs v) | v <- gsReflects refl ]
                , dataDecls = dataDecls mySpec2 
                , measures  = Ms.measures mySpec
                  -- We want to export measures in a 'LiftedSpec', especially if they are
                  -- required to check termination of some 'liftedSigs' we export. Due to the fact
                  -- that 'lSpec1' doesn't contain the measures that we compute via 'makeHaskellMeasures',
                  -- we take them from 'mySpec', which has those.
                , asmSigs = Ms.asmSigs finalLiftedSpec ++ Ms.asmSigs mySpec
                  -- Export all the assumptions (not just the ones created out of reflection) in
                  -- a 'LiftedSpec'.
                , imeasures = Ms.imeasures finalLiftedSpec ++ Ms.imeasures mySpec
                  -- Preserve user-defined 'imeasures'.
                , dvariance = Ms.dvariance finalLiftedSpec ++ Ms.dvariance mySpec
                  -- Preserve user-defined 'dvariance'.
                , rinstance = Ms.rinstance finalLiftedSpec ++ Ms.rinstance mySpec
                  -- Preserve rinstances.
                } 
    })
  where
    -- typeclass elaboration

    coreToLg e =
      case CoreToLogic.runToLogic
             embs
             lmap
             dm
             (\x -> todo Nothing ("coreToLogic not working " ++ x))
             (CoreToLogic.coreToLogic allowTC e) of
        Left msg -> panic Nothing (F.showpp msg)
        Right e -> e    
    elaborateSig si auxsig = do
      tySigs <-
        forM (gsTySigs si) $ \(x, t) ->
          if GM.isFromGHCReal x then
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

    simplifier :: Ghc.CoreExpr -> Ghc.TcRn Ghc.CoreExpr
    simplifier = pure -- no simplification
    allowTC  = typeclass cfg
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
    (dg0, datacons, tycEnv0) = makeTycEnv0   cfg name env embs mySpec2 iSpecs2 
    -- extract name and specs
    env      = Bare.makeEnv cfg src lmap mspecsNoCls
    (mySpec0NoCls, iSpecs0) = splitSpecs name src mspecsNoCls
    -- check barespecs 
    name     = F.notracepp ("ALL-SPECS" ++ zzz) $ _giTargetMod  src 
    zzz      = F.showpp (fst <$> mspecs)

splitSpecs :: ModName -> GhcSrc -> [(ModName, Ms.BareSpec)] -> (Ms.BareSpec, Bare.ModSpecs) 
splitSpecs name src specs = (mySpec, iSpecm) 
  where 
    iSpecm             = fmap mconcat . Misc.group $ iSpecs
    iSpecs             = Dg.sliceSpecs src mySpec iSpecs'
    mySpec             = mconcat (snd <$> mySpecs)
    (mySpecs, iSpecs') = L.partition ((name ==) . fst) specs 


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
  , Ms.reflects  = Ms.reflects mySpec <> (if reflection cfg then Ms.hmeas mySpec else mempty)
  , Ms.dataDecls = Bare.makeHaskellDataDecls cfg name mySpec tcs  
  , Ms.embeds    = Ms.embeds mySpec
  -- We do want 'embeds' to survive and to be present into the final 'LiftedSpec'. The
  -- caveat is to decide which format is more appropriate. We obviously cannot store
  -- them as a 'TCEmb TyCon' as serialising a 'TyCon' would be fairly exponsive. This
  -- needs more thinking.
  , Ms.cmeasures = Ms.cmeasures mySpec
  -- We do want 'cmeasures' to survive and to be present into the final 'LiftedSpec'. The
  -- caveat is to decide which format is more appropriate. This needs more thinking.
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
                    $ reflectedVars cfg spec cbs
  | otherwise       = []

-- | We cannot reflect embedded tycons (e.g. Bool) as that gives you a sort
--   conflict: e.g. what is the type of is-True? does it take a GHC.Types.Bool
--   or its embedding, a bool?
isEmbedded :: TCEmb Ghc.TyCon -> Ghc.TyCon -> Bool
isEmbedded embs c = F.tceMember c embs

varTyCons :: Ghc.Var -> [Ghc.TyCon]
varTyCons = specTypeCons . ofType . Ghc.varType

specTypeCons           :: SpecType -> [Ghc.TyCon]
specTypeCons         = foldRType tc []
  where
    tc acc t@RApp {} = rtc_tc (rt_tycon t) : acc
    tc acc _         = acc

reflectedVars :: Config -> Ms.BareSpec -> [Ghc.CoreBind] -> [Ghc.Var]
reflectedVars cfg spec cbs = fst <$> xDefs
  where
    xDefs              = Mb.mapMaybe (`GM.findVarDef` cbs) reflSyms
    reflSyms           = fmap val $ S.toList (Ms.reflects spec <> if reflection cfg then Ms.hmeas spec else mempty)

------------------------------------------------------------------------------------------
makeSpecVars :: Config -> GhcSrc -> Ms.BareSpec -> Bare.Env -> Bare.MeasEnv 
             -> Bare.Lookup GhcSpecVars
------------------------------------------------------------------------------------------
makeSpecVars cfg src mySpec env measEnv = do 
  tgtVars     <-   mapM (resolveStringVar  env name)              (checks     cfg) 
  igVars      <-  sMapM (Bare.lookupGhcVar env name "gs-ignores") (Ms.ignores mySpec) 
  lVars       <-  sMapM (Bare.lookupGhcVar env name "gs-lvars"  ) (Ms.lvars   mySpec)
  return (SpVar tgtVars igVars lVars cMethods)
  where 
    name       = _giTargetMod src 
    cMethods   = snd3 <$> Bare.meMethods measEnv 

sMapM :: (Monad m, Eq b, Hashable b) => (a -> m b) -> S.HashSet a -> m (S.HashSet b)
sMapM f xSet = do 
 ys <- mapM f (S.toList xSet) 
 return (S.fromList ys)

sForM :: (Monad m, Eq b, Hashable b) =>S.HashSet a -> (a -> m b) -> m (S.HashSet b)
sForM xs f = sMapM f xs

qualifySymbolic :: (F.Symbolic a) => ModName -> a -> F.Symbol 
qualifySymbolic name s = GM.qualifySymbol (F.symbol name) (F.symbol s)

resolveStringVar :: Bare.Env -> ModName -> String -> Bare.Lookup Ghc.Var
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
    isPrimFTC           = F.val tcs `elem` F.prims 
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
makeSpecTerm :: Config -> Ms.BareSpec -> Bare.Env -> ModName -> 
                Bare.Lookup GhcSpecTerm 
------------------------------------------------------------------------------------------
makeSpecTerm cfg mySpec env name = do 
  sizes  <- if structuralTerm cfg then pure mempty else makeSize env name mySpec
  lazies <- makeLazy     env name mySpec
  autos  <- makeAutoSize env name mySpec
  decr   <- makeDecrs env name mySpec
  fail   <- makeFail env name mySpec 
  return  $ SpTerm 
    { gsLazy       = S.insert dictionaryVar (lazies `mappend` sizes)
    , gsFail       = fail
    , gsStTerm     = sizes
    , gsAutosize   = autos 
    , gsDecr       = decr 
    , gsNonStTerm  = mempty 
    }

-- formerly, makeHints
makeDecrs :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup [(Ghc.Var, [Int])] 
makeDecrs env name mySpec =
  forM (Ms.decr mySpec) $ \(lx, z) -> do 
    v <- Bare.lookupGhcVar env name "decreasing" lx
    return (v, z)

makeLazy :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.Var)
makeLazy env name spec =
  sMapM (Bare.lookupGhcVar env name "Var") (Ms.lazy spec)

makeFail :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (S.HashSet (Located Ghc.Var))
makeFail env name spec = 
  sForM (Ms.fails spec) $ \x -> do 
    vx <- Bare.lookupGhcVar env name "Var" x 
    return x { val = vx }

makeRewrite :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (S.HashSet (Located Ghc.Var))
makeRewrite env name spec = 
  sForM (Ms.rewrites spec) $ \x -> do
    vx <-  Bare.lookupGhcVar env name "Var" x 
    return x { val = vx }

makeRewriteWith :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (M.HashMap Ghc.Var [Ghc.Var])
makeRewriteWith env name spec = M.fromList <$> makeRewriteWith' env name spec

makeRewriteWith' :: Bare.Env -> ModName -> Spec ty bndr -> Bare.Lookup [(Ghc.Var, [Ghc.Var])]
makeRewriteWith' env name spec = 
  forM (M.toList $ Ms.rewriteWith spec) $ \(x, xs) -> do
    xv  <- Bare.lookupGhcVar env name "Var1" x
    xvs <- mapM (Bare.lookupGhcVar env name "Var2") xs
    return (xv, xvs)

makeAutoSize :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.TyCon)
makeAutoSize env name
  = fmap S.fromList 
  . mapM (Bare.lookupGhcTyCon env name "TyCon") 
  . S.toList 
  . Ms.autosize 

makeSize :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.Var)
makeSize env name
  = fmap S.fromList
  . mapM (Bare.lookupGhcVar env name "Var") 
  . Mb.mapMaybe getSizeFuns
  . Ms.dataDecls 

getSizeFuns :: DataDecl -> Maybe LocSymbol
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
             -> Bare.Lookup GhcSpecRefl 
------------------------------------------------------------------------------------------
makeSpecRefl cfg src menv specs env name sig tycEnv = do 
  autoInst <- makeAutoInst env name mySpec 
  rwr      <- makeRewrite env name mySpec
  rwrWith  <- makeRewriteWith env name mySpec
  wRefls   <- Bare.wiredReflects cfg env name sig
  xtes     <- Bare.makeHaskellAxioms cfg src env tycEnv name lmap sig mySpec
  let myAxioms = [ Bare.qualifyTop env name (F.loc lt) (e {eqName = symbol x}) | (x, lt, e) <- xtes]  
  let sigVars  = F.notracepp "SIGVARS" $ (fst3 <$> xtes)            -- reflects
                                      ++ (fst  <$> gsAsmSigs sig)   -- assumes
                                      ++ (fst  <$> gsRefSigs sig)
  return SpRefl 
    { gsLogicMap   = lmap 
    , gsAutoInst   = autoInst 
    , gsImpAxioms  = concatMap (Ms.axeqs . snd) (M.toList specs)
    , gsMyAxioms   = F.notracepp "gsMyAxioms" myAxioms 
    , gsReflects   = F.notracepp "gsReflects" (lawMethods ++ filter (isReflectVar rflSyms) sigVars ++ wRefls)
    , gsHAxioms    = F.notracepp "gsHAxioms" xtes 
    , gsWiredReft  = wRefls
    , gsRewrites   = rwr
    , gsRewritesWith = rwrWith
    }
  where
    lawMethods   = F.notracepp "Law Methods" $ concatMap Ghc.classMethods (fst <$> Bare.meCLaws menv) 
    mySpec       = M.lookupDefault mempty name specs 
    rflSyms      = S.fromList (getReflects specs)
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
addReflSigs :: Bare.Env -> ModName -> BareRTEnv -> GhcSpecRefl -> GhcSpecSig -> GhcSpecSig
------------------------------------------------------------------------------------------
addReflSigs env name rtEnv refl sig =
  sig { gsRefSigs = F.notracepp ("gsRefSigs for " ++ F.showpp name) $ map expandReflectedSignature reflSigs
      , gsAsmSigs = F.notracepp ("gsAsmSigs for " ++ F.showpp name) $ (wreflSigs ++ filter notReflected (gsAsmSigs sig))
      }
  where

    -- See T1738. We need to expand and qualify any reflected signature /here/, after any
    -- relevant binder has been detected and \"promoted\". The problem stems from the fact that any input
    -- 'BareSpec' will have a 'reflects' list of binders to reflect under the form of an opaque 'Var', that
    -- qualifyExpand can't touch when we do a first pass in 'makeGhcSpec0'. However, once we reflected all
    -- the functions, we are left with a pair (Var, LocSpecType). The latter /needs/ to be qualified and
    -- expanded again, for example in case it has expression aliases derived from 'inlines'.
    expandReflectedSignature :: (Ghc.Var, LocSpecType) -> (Ghc.Var, LocSpecType)
    expandReflectedSignature = fmap (Bare.qualifyExpand env name rtEnv (F.dummyPos "expand-refSigs") [])

    (wreflSigs, reflSigs)   = L.partition ((`elem` gsWiredReft refl) . fst) 
                                 [ (x, t) | (x, t, _) <- gsHAxioms refl ]   
    reflected       = fst <$> (wreflSigs ++ reflSigs)
    notReflected xt = fst xt `notElem` reflected

makeAutoInst :: Bare.Env -> ModName -> Ms.BareSpec -> 
                Bare.Lookup (M.HashMap Ghc.Var (Maybe Int))
makeAutoInst env name spec = M.fromList <$> kvs
  where 
    kvs = forM (M.toList (Ms.autois spec)) $ \(k, val) -> do 
            vk <- Bare.lookupGhcVar env name "Var" k
            return (vk, val)


----------------------------------------------------------------------------------------
makeSpecSig :: Config -> ModName -> Bare.ModSpecs -> Bare.Env -> Bare.SigEnv -> Bare.TycEnv -> Bare.MeasEnv -> [Ghc.CoreBind]
            -> Bare.Lookup GhcSpecSig 
----------------------------------------------------------------------------------------
makeSpecSig cfg name specs env sigEnv tycEnv measEnv cbs = do 
  mySigs     <- makeTySigs  env sigEnv name mySpec
  aSigs      <- F.notracepp ("makeSpecSig aSigs " ++ F.showpp name) $ makeAsmSigs env sigEnv name specs 
  let asmSigs =  Bare.tcSelVars tycEnv 
              ++ aSigs
              ++ [ (x,t) | (_, x, t) <- concatMap snd (Bare.meCLaws measEnv) ]
  let tySigs  = strengthenSigs . concat $ 
                  [ [(v, (0, t)) | (v, t,_) <- mySigs                         ]   -- NOTE: these weights are to priortize 
                  , [(v, (1, t)) | (v, t  ) <- makeMthSigs measEnv            ]   -- user defined sigs OVER auto-generated 
                  , [(v, (2, t)) | (v, t  ) <- makeInlSigs env rtEnv allSpecs ]   -- during the strengthening, i.e. to KEEP 
                  , [(v, (3, t)) | (v, t  ) <- makeMsrSigs env rtEnv allSpecs ]   -- the binders used in USER-defined sigs 
                  ]                                                               -- as they appear in termination metrics
  newTys     <-  makeNewTypes env sigEnv allSpecs 
  return SpSig 
    { gsTySigs   = tySigs 
    , gsAsmSigs  = asmSigs
    , gsRefSigs  = [] 
    , gsDicts    = dicts 
    -- , gsMethods  = if noclasscheck cfg then [] else Bare.makeMethodTypes dicts (Bare.meClasses  measEnv) cbs 
    , gsMethods  = if noclasscheck cfg then [] else Bare.makeMethodTypes (typeclass cfg) dicts (Bare.meClasses  measEnv) cbs 
    , gsInSigs   = mempty
    , gsNewTypes = newTys 
    , gsTexprs   = [ (v, t, es) | (v, t, Just es) <- mySigs ] 
    }
  where 
    dicts      = Bare.makeSpecDictionaries env sigEnv specs  
    mySpec     = M.lookupDefault mempty name specs
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
           -> Bare.Lookup [(Ghc.Var, LocSpecType, Maybe [Located F.Expr])]
makeTySigs env sigEnv name spec = do
  bareSigs   <- bareTySigs env name                spec 
  expSigs    <- makeTExpr  env name bareSigs rtEnv spec 
  let rawSigs = Bare.resolveLocalBinds env expSigs 
  return [ (x, cook x bt, z) | (x, bt, z) <- rawSigs ]
  where 
    rtEnv     = Bare.sigRTEnv sigEnv 
    cook x bt = Bare.cookSpecType env sigEnv name (Bare.HsTV x) bt 

bareTySigs :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup [(Ghc.Var, LocBareType)]
bareTySigs env name spec = checkDuplicateSigs <$> vts 
  where 
    vts = forM ( Ms.sigs spec ++ Ms.localSigs spec ) $ \ (x, t) -> do 
            v <- F.notracepp "LOOKUP-GHC-VAR" $ Bare.lookupGhcVar env name "rawTySigs" x
            return (v, t) 

-- checkDuplicateSigs :: [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)] 
checkDuplicateSigs :: (Symbolic x) => [(x, F.Located t)] -> [(x, F.Located t)]
checkDuplicateSigs xts = case Misc.uniqueByKey symXs  of
  Left (k, ls) -> uError (errDupSpecs (pprint k) (GM.sourcePosSrcSpan <$> ls))
  Right _      -> xts 
  where
    symXs = [ (F.symbol x, F.loc t) | (x, t) <- xts ]


makeAsmSigs :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs -> Bare.Lookup [(Ghc.Var, LocSpecType)]
makeAsmSigs env sigEnv myName specs = do 
  raSigs <- rawAsmSigs env myName specs
  return [ (x, t) | (name, x, bt) <- raSigs, let t = Bare.cookSpecType env sigEnv name (Bare.LqTV x) bt ] 

rawAsmSigs :: Bare.Env -> ModName -> Bare.ModSpecs -> Bare.Lookup [(ModName, Ghc.Var, LocBareType)]
rawAsmSigs env myName specs = do 
  aSigs <- allAsmSigs env myName specs 
  return [ (m, v, t) | (v, sigs) <- aSigs, let (m, t) = myAsmSig v sigs ] 
    
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
          -> Bare.Lookup [(Ghc.Var, LocBareType, Maybe [Located F.Expr])]
makeTExpr env name tySigs rtEnv spec = do 
  vExprs       <- M.fromList <$> makeVarTExprs env name spec
  let vSigExprs = Misc.hashMapMapWithKey (\v t -> (t, M.lookup v vExprs)) vSigs 
  return [ (v, t, qual t <$> es) | (v, (t, es)) <- M.toList vSigExprs ] 
  where 
    qual t es   = qualifyTermExpr env name rtEnv t <$> es
    vSigs       = M.fromList tySigs 
                    
qualifyTermExpr :: Bare.Env -> ModName -> BareRTEnv -> LocBareType -> Located F.Expr 
                -> Located F.Expr 
qualifyTermExpr env name rtEnv t le 
        = F.atLoc le (Bare.qualifyExpand env name rtEnv l bs e)
  where 
    l   = F.loc le 
    e   = F.val le 
    bs  = ty_binds . toRTypeRep . val $ t 

makeVarTExprs :: Bare.Env -> ModName -> Ms.BareSpec -> Bare.Lookup [(Ghc.Var, [Located F.Expr])]
makeVarTExprs env name spec = 
  forM (Ms.termexprs spec) $ \(x, es) -> do 
    vx <- Bare.lookupGhcVar env name "Var" x
    return (vx, es)

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

allAsmSigs :: Bare.Env -> ModName -> Bare.ModSpecs -> 
              Bare.Lookup [(Ghc.Var, [(Bool, ModName, LocBareType)])]
allAsmSigs env myName specs = do 
  let aSigs = [ (name, must, x, t) | (name, spec) <- M.toList specs
                                   , (must, x, t) <- getAsmSigs myName name spec ]
  vSigs    <- forM aSigs $ \(name, must, x, t) -> do
                vMb <- resolveAsmVar env name must x
                return (vMb, (must, name, t))
  return    $ Misc.groupList [ (v, z) | (Just v, z) <- vSigs ]

resolveAsmVar :: Bare.Env -> ModName -> Bool -> LocSymbol -> Bare.Lookup (Maybe Ghc.Var)
resolveAsmVar env name True  lx = Just  <$> Bare.lookupGhcVar env name "resolveAsmVar-True"  lx
resolveAsmVar env name False lx = return $  Bare.maybeResolveSym     env name "resolveAsmVar-False" lx  <|> GM.maybeAuxVar (F.val lx)


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

makeSigEnv :: F.TCEmb Ghc.TyCon -> Bare.TyConMap -> S.HashSet StableName -> BareRTEnv -> Bare.SigEnv 
makeSigEnv embs tyi exports rtEnv = Bare.SigEnv
  { sigEmbs     = embs 
  , sigTyRTyMap = tyi 
  , sigExports  = exports 
  , sigRTEnv    = rtEnv
  } 

makeNewTypes :: Bare.Env -> Bare.SigEnv -> [(ModName, Ms.BareSpec)] -> 
                Bare.Lookup [(Ghc.TyCon, LocSpecType)]
makeNewTypes env sigEnv specs = do 
  fmap concat $ 
    forM nameDecls $ \(name, d) -> 
      makeNewType env sigEnv name d
  where
    nameDecls = [(name, d) | (name, spec) <- specs, d <- Ms.newtyDecls spec] 

makeNewType :: Bare.Env -> Bare.SigEnv -> ModName -> DataDecl -> 
               Bare.Lookup [(Ghc.TyCon, LocSpecType)]
makeNewType env sigEnv name d = do 
  tcMb <- Bare.lookupGhcDnTyCon env name "makeNewType" tcName
  case tcMb of
    Just tc -> return [(tc, t)] 
    _       -> return []
  where 
    tcName                    = tycName d
    t                         = Bare.cookSpecType env sigEnv name Bare.GenTV bt
    bt                        = getTy tcName (tycSrcPos d) (Mb.fromMaybe [] (tycDCons d))
    getTy _ l [c]
      | [(_, t)] <- dcFields c = Loc l l t
    getTy n l _                = Ex.throw (err n l) 
    err n l                    = ErrOther (GM.sourcePosSrcSpan l) ("Bad new type declaration:" <+> F.pprint n) :: UserError

------------------------------------------------------------------------------------------
makeSpecData :: GhcSrc -> Bare.Env -> Bare.SigEnv -> Bare.MeasEnv -> GhcSpecSig -> Bare.ModSpecs
             -> GhcSpecData
------------------------------------------------------------------------------------------
makeSpecData src env sigEnv measEnv sig specs = SpData 
  { gsCtors      = F.notracepp "GS-CTORS" 
                   [ (x, if allowTC then t else tt) 
                       | (x, t) <- Bare.meDataCons measEnv
                       , let tt  = Bare.plugHoles (typeclass $ getConfig env) sigEnv name (Bare.LqTV x) t 
                   ]
  , gsMeas       = [ (F.symbol x, uRType <$> t) | (x, t) <- measVars ] 
  , gsMeasures   = Bare.qualifyTopDummy env name <$> (ms1 ++ ms2)
  , gsInvariants = Misc.nubHashOn (F.loc . snd) invs 
  , gsIaliases   = concatMap (makeIAliases env sigEnv) (M.toList specs)
  , gsUnsorted   = usI ++ concatMap msUnSorted (concatMap measures specs)
  }
  where
    allowTC      = typeclass (getConfig env)
    measVars     = Bare.meSyms      measEnv -- ms'
                ++ Bare.meClassSyms measEnv -- cms' 
                ++ Bare.varMeasures env
    measuresSp   = Bare.meMeasureSpec measEnv  
    ms1          = M.elems (Ms.measMap measuresSp)
    ms2          = Ms.imeas   measuresSp
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
        su          = mkSubst [(v, mkEApp x [EVar v]), (z,EVar v)]
        -- p'          = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p
    in  Just (v, subst su p)
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
    cls        = F.notracepp "meClasses" $ Bare.meClasses measEnv 
    tycons     = Bare.tcTyCons   tycEnv 


-- REBARE: formerly, makeGhcCHOP1
-- split into two to break circular dependency. we need dataconmap for core2logic
-------------------------------------------------------------------------------------------
makeTycEnv0 :: Config -> ModName -> Bare.Env -> TCEmb Ghc.TyCon -> Ms.BareSpec -> Bare.ModSpecs 
           -> (Diagnostics,  [Located DataConP], Bare.TycEnv)
-------------------------------------------------------------------------------------------
makeTycEnv0 cfg myName env embs mySpec iSpecs = (diag0 <> diag1, datacons, Bare.TycEnv 
  { tcTyCons      = tycons                  
  , tcDataCons    = mempty -- val <$> datacons 
  , tcSelMeasures = dcSelectors             
  , tcSelVars     = mempty -- recSelectors            
  , tcTyConMap    = tyi                     
  , tcAdts        = adts                    
  , tcDataConMap  = dm
  , tcEmbs        = embs
  , tcName        = myName
  })
  where
    (tcDds, dcs)   = conTys
    (diag0, conTys) = withDiagnostics $ Bare.makeConTypes myName env specs 
    specs         = (myName, mySpec) : M.toList iSpecs
    tcs           = Misc.snd3 <$> tcDds 
    tyi           = Bare.qualifyTopDummy env myName (makeTyConInfo embs fiTcs tycons)
    -- tycons        = F.tracepp "TYCONS" $ Misc.replaceWith tcpCon tcs wiredTyCons
    -- datacons      =  Bare.makePluggedDataCons embs tyi (Misc.replaceWith (dcpCon . val) (F.tracepp "DATACONS" $ concat dcs) wiredDataCons)
    tycons        = tcs ++ knownWiredTyCons env myName 
    datacons      = Bare.makePluggedDataCon (typeclass cfg) embs tyi <$> (concat dcs ++ knownWiredDataCons env myName)
    tds           = [(name, tcpCon tcp, dd) | (name, tcp, Just dd) <- tcDds]
    (diag1, adts) = Bare.makeDataDecls cfg embs myName tds       datacons
    dm            = Bare.dataConMap adts
    dcSelectors   = concatMap (Bare.makeMeasureSelectors cfg dm) (if reflection cfg then charDataCon:datacons else datacons)
    fiTcs         = _gsFiTcs (Bare.reSrc env)



makeTycEnv1 ::
     Config 
  -> ModName
  -> Bare.Env
  -> (Bare.TycEnv, [Located DataConP])
  -> (Ghc.CoreExpr -> F.Expr)
  -> (Ghc.CoreExpr -> Ghc.TcRn Ghc.CoreExpr)
  -> Ghc.TcRn Bare.TycEnv
makeTycEnv1 cfg myName env (tycEnv, datacons) coreToLg simplifier = do
  -- fst for selector generation, snd for dataconsig generation
  lclassdcs <- forM classdcs $ traverse (Bare.elaborateClassDcp coreToLg simplifier)
  let recSelectors = Bare.makeRecordSelectorSigs env myName (dcs ++ (fmap . fmap) snd lclassdcs)
  pure $
    tycEnv {Bare.tcSelVars = recSelectors, Bare.tcDataCons = F.val <$> ((fmap . fmap) fst lclassdcs ++ dcs )}
  where
    (classdcs, dcs) =
      L.partition
        (Ghc.isClassTyCon . Ghc.dataConTyCon . dcpCon . F.val) datacons

    
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
makeMeasEnv :: Bare.Env -> Bare.TycEnv -> Bare.SigEnv -> Bare.ModSpecs -> 
               Bare.Lookup Bare.MeasEnv 
-------------------------------------------------------------------------------------------
makeMeasEnv env tycEnv sigEnv specs = do 
  laws        <- Bare.makeCLaws env sigEnv name specs
  (cls, mts)  <- Bare.makeClasses        env sigEnv name specs
  let dms      = Bare.makeDefaultMethods env mts  
  measures0   <- mapM (Bare.makeMeasureSpec env sigEnv name) (M.toList specs)
  let measures = mconcat (Ms.mkMSpec' dcSelectors : measures0)
  let (cs, ms) = Bare.makeMeasureSpec'  (typeclass $ getConfig env)   measures
  let cms      = Bare.makeClassMeasureSpec measures
  let cms'     = [ (x, Loc l l' $ cSort t)  | (Loc l l' x, t) <- cms ]
  let ms'      = [ (F.val lx, F.atLoc lx t) | (lx, t) <- ms
                                            , Mb.isNothing (lookup (val lx) cms') ]
  let cs'      = [ (v, txRefs v t) | (v, t) <- Bare.meetDataConSpec (typeclass (getConfig env)) embs cs (datacons ++ cls)]
  return Bare.MeasEnv 
    { meMeasureSpec = measures 
    , meClassSyms   = cms' 
    , meSyms        = ms' 
    , meDataCons    = cs' 
    , meClasses     = cls
    , meMethods     = mts ++ dms 
    , meCLaws       = laws
    }
  where 
    txRefs v t    = Bare.txRefSort tyi embs (t <$ GM.locNamedThing v) 
    tyi           = Bare.tcTyConMap    tycEnv 
    dcSelectors   = Bare.tcSelMeasures tycEnv 
    datacons      = Bare.tcDataCons    tycEnv 
    embs          = Bare.tcEmbs        tycEnv 
    name          = Bare.tcName        tycEnv

-----------------------------------------------------------------------------------------
-- | @makeLiftedSpec@ is used to generate the BareSpec object that should be serialized 
--   so that downstream files that import this target can access the lifted definitions, 
--   e.g. for measures, reflected functions etc.
-----------------------------------------------------------------------------------------
makeLiftedSpec :: ModName -> GhcSrc -> Bare.Env 
               -> GhcSpecRefl -> GhcSpecData -> GhcSpecSig -> GhcSpecQual -> BareRTEnv 
               -> Ms.BareSpec -> Ms.BareSpec 
-----------------------------------------------------------------------------------------
makeLiftedSpec name src _env refl sData sig qual myRTE lSpec0 = lSpec0 
  { Ms.asmSigs    = F.notracepp   ("makeLiftedSpec : ASSUMED-SIGS " ++ F.showpp name ) $ (xbs ++ myDCs) 
  , Ms.reflSigs   = F.notracepp "REFL-SIGS"         xbs
  , Ms.sigs       = F.notracepp   ("makeLiftedSpec : LIFTED-SIGS " ++ F.showpp name )  $ mkSigs (gsTySigs sig)  
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
    myDCs         = [(x,t) | (x,t) <- mkSigs (gsCtors sData)
                           , F.symbol name == fst (GM.splitModuleName $ val x)]
    mkSigs xts    = [ toBare (x, t) | (x, t) <- xts
                    ,  S.member x sigVars && (isExportedVar (view targetSrcIso src) x) 
                    ] 
    toBare (x, t) = (varLocSym x, Bare.specToBare <$> t)
    xbs           = toBare <$> reflTySigs 
    sigVars       = S.difference defVars reflVars
    defVars       = S.fromList (_giDefVars src)
    reflTySigs    = [(x, t) | (x,t,_) <- gsHAxioms refl, x `notElem` gsWiredReft refl]
    reflVars      = S.fromList (fst <$> reflTySigs)
    -- myAliases fld = M.elems . fld $ myRTE 
    srcF          = _giTarget src 

-- | Returns 'True' if the input determines a location within the input file. Due to the fact we might have
-- Haskell sources which have \"companion\" specs defined alongside them, we also need to account for this
-- case, by stripping out the extensions and check that the LHS is a Haskell source and the RHS a spec file.
isLocInFile :: (F.Loc a) => FilePath -> a ->  Bool 
isLocInFile f lx = f == lifted || isCompanion
  where
    lifted :: FilePath
    lifted = locFile lx

    isCompanion :: Bool
    isCompanion =
      (==) (dropExtension f) (dropExtension lifted)
       &&  isExtFile Hs f
       &&  isExtFile Files.Spec lifted

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


withDiagnostics :: (Monoid a) => Bare.Lookup a -> (Diagnostics, a)
withDiagnostics (Left es) = (mkDiagnostics [] es, mempty)
withDiagnostics (Right v) = (emptyDiagnostics, v)
