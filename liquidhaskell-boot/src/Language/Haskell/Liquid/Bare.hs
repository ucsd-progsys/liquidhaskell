{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
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
  ) where

import           Control.Monad                              (forM, mplus, when)
import qualified Control.Exception                          as Ex
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S
import           Text.PrettyPrint.HughesPJ                  hiding (first, (<>)) -- (text, (<+>))
import           System.FilePath                            (dropExtension)
import           Language.Fixpoint.Utils.Files              as Files
import           Language.Fixpoint.Misc                     as Misc
import           Language.Fixpoint.Types                    hiding (dcFields, DataDecl, Error, panic)
import qualified Language.Fixpoint.Types                    as F
import qualified Language.Haskell.Liquid.Misc               as Misc -- (nubHashOn)
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Liquid.GHC.API            as Ghc
import           Language.Haskell.Liquid.GHC.Types          (StableName)
import           Language.Haskell.Liquid.LHNameResolution
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Visitors
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
import qualified Language.Haskell.Liquid.Bare.Resolve       as Resolve
import qualified Language.Haskell.Liquid.Bare.Typeclass     as Bare
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as CoreToLogic
import           Language.Haskell.Liquid.UX.Config
import Data.Hashable (Hashable)
import Data.Bifunctor (bimap, first)
import Data.Function (on)


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
               -> Bare.LocalVars
               -> LogicNameEnv
               -> LogicMap
               -> TargetSrc
               -> BareSpec
               -> TargetDependencies
               -> Ghc.TcRn (Either Diagnostics ([Warning], TargetSpec, LiftedSpec))
makeTargetSpec cfg localVars lnameEnv lmap targetSrc bareSpec dependencies = do
  let targDiagnostics     = Bare.checkTargetSrc cfg targetSrc
  let depsDiagnostics     = mapM (Bare.checkBareSpec . snd) legacyDependencies
  let bareSpecDiagnostics = Bare.checkBareSpec bareSpec
  case targDiagnostics >> depsDiagnostics >> bareSpecDiagnostics of
   Left d | noErrors d -> secondPhase (allWarnings d)
   Left d              -> return $ Left d
   Right ()            -> secondPhase mempty
  where
    secondPhase :: [Warning] -> Ghc.TcRn (Either Diagnostics ([Warning], TargetSpec, LiftedSpec))
    secondPhase phaseOneWarns = do
      diagOrSpec <- makeGhcSpec cfg lnameEnv localVars (fromTargetSrc targetSrc) lmap bareSpec legacyDependencies
      case diagOrSpec of
        Left d -> return $ Left d
        Right (warns, ghcSpec) -> do
          let targetSpec = toTargetSpec ghcSpec
              liftedSpec = ghcSpecToLiftedSpec ghcSpec
          liftedSpec' <- removeUnexportedLocalAssumptions liftedSpec
          return $ Right (phaseOneWarns <> warns, targetSpec, liftedSpec')

    toLegacyDep :: (Ghc.StableModule, LiftedSpec) -> (ModName, BareSpec)
    toLegacyDep (sm, ls) = (ModName SrcImport (Ghc.moduleName . Ghc.unStableModule $ sm), fromBareSpecLHName $ unsafeFromLiftedSpec ls)

    legacyDependencies :: [(ModName, BareSpec)]
    legacyDependencies =
      -- Dependencies are sorted lexicographically to make predictable which
      -- logic names will have preference when exporting conflicting measures.
      --
      -- At the moment it is the measure from the last module after sorting.
      -- But if there is a local conflicting measure, that one is used.
      L.sortOn fst $ map toLegacyDep $ M.toList $ getDependencies dependencies

    -- Assumptions about local functions that are not exported aren't useful for
    -- other modules.
    removeUnexportedLocalAssumptions :: LiftedSpec -> Ghc.TcRn LiftedSpec
    removeUnexportedLocalAssumptions lspec = do
      tcg <- Ghc.getGblEnv
      let exportedNames = Ghc.availsToNameSet (Ghc.tcg_exports tcg)
          exportedAssumption (LHNResolved (LHRGHC n) _) =
            case Ghc.nameModule_maybe n of
              Nothing -> Ghc.elemNameSet n exportedNames
              Just m -> m /= Ghc.tcg_mod tcg || Ghc.elemNameSet n exportedNames
          exportedAssumption _ = True
      return lspec { liftedAsmSigs = S.filter (exportedAssumption . val . fst) (liftedAsmSigs lspec) }

    ghcSpecToLiftedSpec = toLiftedSpec . toBareSpecLHName cfg lnameEnv . _gsLSpec


-------------------------------------------------------------------------------------
-- | @makeGhcSpec@ invokes @makeGhcSpec0@ to construct the @GhcSpec@ and then
--   validates it using @checkGhcSpec@.
-------------------------------------------------------------------------------------
makeGhcSpec :: Config
            -> LogicNameEnv
            -> Bare.LocalVars
            -> GhcSrc
            -> LogicMap
            -> Ms.BareSpec
            -> [(ModName, Ms.BareSpec)]
            -> Ghc.TcRn (Either Diagnostics ([Warning], GhcSpec))
-------------------------------------------------------------------------------------
makeGhcSpec cfg lenv localVars src lmap targetSpec dependencySpecs = do
  ghcTyLookupEnv <- Bare.makeGHCTyLookupEnv (_giCbs src)
  tcg <- Ghc.getGblEnv
  instEnvs <- Ghc.tcGetInstEnvs
  (dg0, sp) <- makeGhcSpec0 cfg ghcTyLookupEnv tcg instEnvs lenv localVars src lmap targetSpec dependencySpecs
  let diagnostics = Bare.checkTargetSpec (targetSpec : map snd dependencySpecs)
                                         (toTargetSrc src)
                                         (ghcSpecEnv sp)
                                         (_giCbs src)
                                         (toTargetSpec sp)
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
makeGhcSpec0
  :: Config
  -> Bare.GHCTyLookupEnv
  -> Ghc.TcGblEnv
  -> Ghc.InstEnvs
  -> LogicNameEnv
  -> Bare.LocalVars
  -> GhcSrc
  -> LogicMap
  -> Ms.BareSpec
  -> [(ModName, Ms.BareSpec)]
  -> Ghc.TcRn (Diagnostics, GhcSpec)
makeGhcSpec0 cfg ghcTyLookupEnv tcg instEnvs lenv localVars src lmap targetSpec dependencySpecs = do
  globalRdrEnv <- Ghc.tcg_rdr_env <$> Ghc.getGblEnv
  -- build up environments
  tycEnv <- makeTycEnv1 env (tycEnv0, datacons) coreToLg simplifier
  let tyi      = Bare.tcTyConMap   tycEnv
  let sigEnv   = makeSigEnv  embs tyi (_gsExports src) rtEnv
  let lSpec1   = makeLiftedSpec1 cfg src tycEnv lmap mySpec1
  let mySpec   = mySpec2 <> lSpec1
  let specs    = M.insert name mySpec iSpecs2
  let myRTE    = myRTEnv       src env sigEnv rtEnv
  -- NB: we first compute a measure environment w/o the opaque reflections, so that we can bootstrap
  -- the signature `sig`. Then we'll add the opaque reflections before we compute `sData` and al.
  let (dg1, measEnv0) = withDiagnostics $ makeMeasEnv      env tycEnv sigEnv       specs
  let (dg2, (specInstances, sig)) = withDiagnostics $ makeSpecSig cfg name mySpec iSpecs2 env sigEnv tycEnv measEnv0 (_giCbs src)
  elaboratedSig <-
    if allowTC then Bare.makeClassAuxTypes (elaborateSpecType coreToLg simplifier) datacons instMethods
                              >>= elaborateSig sig
               else pure sig
  let (dg3, refl)    = withDiagnostics $ makeSpecRefl src specs env name elaboratedSig tycEnv
  let eqs            = gsHAxioms refl
  let (dg4, measEnv) = withDiagnostics $ addOpaqueReflMeas cfg tycEnv env mySpec measEnv0 specs eqs
  let qual = makeSpecQual cfg env globalRdrEnv tycEnv measEnv rtEnv mySpec iSpecs2
  let (dg5, spcVars) = withDiagnostics $ makeSpecVars cfg src mySpec env measEnv
  let (dg6, spcTerm) = withDiagnostics $ makeSpecTerm cfg     mySpec lenv env
  let sData    = makeSpecData  src env sigEnv measEnv elaboratedSig specs
  let finalLiftedSpec = makeLiftedSpec name src env refl sData elaboratedSig qual myRTE (lSpec0 <> lSpec1)
  let diags    = mconcat [dg0, dg1, dg2, dg3, dg4, dg5, dg6]

  -- Dump reflections, if requested
  when (dumpOpaqueReflections cfg) . Ghc.liftIO $ do
    putStrLn ""
    if L.null (Bare.meOpaqueRefl measEnv) then do
      putStrLn "No opaque reflection was generated."
    else do
      putStrLn "Opaque reflections: "
      let sortedRefls = L.sort $ fst <$> Bare.meOpaqueRefl measEnv
      mapM_ (putStrLn . ("- " ++) . show) sortedRefls
    putStrLn ""

  pure (diags, SP
    { _gsConfig = cfg
    , _gsImps   = makeImports mspecs
    , _gsSig    = addReflSigs env name rtEnv measEnv refl elaboratedSig
    , _gsRefl   = refl
    , _gsData   = sData
    , _gsQual   = qual
    , _gsName   = makeSpecName tycEnv measEnv dataConIds
    , _gsVars   = spcVars
    , _gsTerm   = spcTerm

    , _gsLSpec  = finalLiftedSpec
                { expSigs   =
                    [ (lhNameToResolvedSymbol $ reflectGHCName thisModule $ Ghc.getName v, F.sr_sort $ Bare.varSortedReft embs v)
                    | v <- gsReflects refl
                    ]
                , dataDecls = Bare.dataDeclSize mySpec $ dataDecls mySpec
                  -- Placing mySpec at the end causes local measures to take precedence over
                  -- imported measures when their names clash.
                , measures  = mconcat $ map Ms.measures $ map snd dependencySpecs ++ [mySpec]
                  -- We want to export measures in a 'LiftedSpec', especially if they are
                  -- required to check termination of some 'liftedSigs' we export. Due to the fact
                  -- that 'lSpec1' doesn't contain the measures that we compute via 'makeHaskellMeasures',
                  -- we take them from 'mySpec', which has those.
                , asmSigs = Ms.asmSigs finalLiftedSpec ++ Ms.asmSigs mySpec
                  -- Export all the assumptions (not just the ones created out of reflection) in
                  -- a 'LiftedSpec'.
                , omeasures = Ms.omeasures finalLiftedSpec ++ (snd <$> Bare.meOpaqueRefl measEnv)
                  -- Preserve 'o-measures': they are the opaque reflections
                , imeasures = Ms.imeasures finalLiftedSpec ++ Ms.imeasures mySpec
                  -- Preserve user-defined 'imeasures'.
                , dvariance = Ms.dvariance finalLiftedSpec ++ Ms.dvariance mySpec
                  -- Preserve user-defined 'dvariance'.
                , rinstance = specInstances
                  -- Preserve rinstances.
                , asmReflectSigs = Ms.asmReflectSigs mySpec
                , reflects = Ms.reflects mySpec0
                , cmeasures  = mconcat $ map Ms.cmeasures $ map snd dependencySpecs ++ [targetSpec]
                , embeds = Ms.embeds targetSpec
                , privateReflects = mconcat $ map (privateReflects . snd) mspecs
                , defines = Ms.defines targetSpec
                , usedDataCons = usedDcs
                }
    })
  where
    thisModule = Ghc.tcg_mod tcg
    -- typeclass elaboration

    coreToLg ce =
      case CoreToLogic.runToLogic
             embs
             lmap
             dm
             cfg
             (\x -> todo Nothing ("coreToLogic not working " ++ x))
             (CoreToLogic.coreToLogic ce) of
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
    mySpec2  = Bare.expand rtEnv (F.dummyPos "expand-mySpec2") mySpec1
    iSpecs2  = Bare.expand rtEnv (F.dummyPos "expand-iSpecs2") (M.fromList dependencySpecs)
    rtEnv    = Bare.makeRTEnv env name mySpec1 dependencySpecs lmap
    mspecs   = (name, mySpec0) : dependencySpecs
    (mySpec0, instMethods)  = if allowTC
                              then Bare.compileClasses src env (name, targetSpec) dependencySpecs
                              else (targetSpec, [])
    mySpec1  = mySpec0 <> lSpec0
    lSpec0   = makeLiftedSpec0 cfg src embs lmap mySpec0
    embs     = makeEmbeds          src ghcTyLookupEnv (mySpec0 : map snd dependencySpecs)
    dm       = Bare.tcDataConMap tycEnv0
    (dg0, datacons, tycEnv0) = makeTycEnv0   cfg name env embs mySpec2 iSpecs2
    env      = Bare.makeEnv cfg ghcTyLookupEnv dataConIds tcg instEnvs localVars src lmap ((name, targetSpec) : dependencySpecs)
    -- check barespecs
    name     = F.notracepp ("ALL-SPECS" ++ zzz) $ _giTargetMod  src
    zzz      = F.showpp (fst <$> mspecs)

    usedDcs  = collectAllDataCons (_giCbs src) $ targetSpec : map snd dependencySpecs
    dataConIds =
      [ Ghc.dataConWorkId dc
      | lhn <- S.toList usedDcs
      , Just (Ghc.AConLike (Ghc.RealDataCon dc)) <-
          [maybeReflectedLHName lhn >>= Resolve.lookupGhcTyThingFromName ghcTyLookupEnv]
      ]


collectAllDataCons :: Ghc.CoreProgram -> [BareSpec] -> S.HashSet LHName
collectAllDataCons cbs =
    S.unions .  (castDCs :) . (usedInCoreDCs :) . map usedDataCons
  where
    -- Constraint generation might inserts data constructors which are not
    -- present in the original program.
    -- See Note [Type classes with a single method] in
    -- Haskell.Liquid.Constraint.Generate
    castDCs =
      S.fromList $
      map makeLogicLHNameFromDC $
      Mb.mapMaybe isClassConCoDC $
      collectCastCoercions cbs

    makeLogicLHNameFromDC dc =
      let n = Ghc.getName dc
          s = symbol (Ghc.getOccString dc)
       in makeLogicLHName
            s
            (Mb.fromMaybe (error "expected module") $ Ghc.nameModule_maybe n)
            (Just n)

    usedInCoreDCs =
      S.fromList $
      map makeLogicLHNameFromDC $
      [ dc
      | v <- freeVars S.empty cbs
      , dc <- case Ghc.idDetails v of
          Ghc.DataConWrapId dc -> [dc]
          Ghc.DataConWorkId dc -> [dc]
          _ -> []
      ]

    isClassConCoDC :: Ghc.Coercion -> Maybe Ghc.DataCon
    -- See Note [Type classes with a single method] in
    -- Haskell.Liquid.Constraint.Generate
    isClassConCoDC co
      | Ghc.Pair _t1 t2 <- Ghc.coercionKind co
      , Ghc.isClassPred t2
      , (tc,_ts) <- Ghc.splitTyConApp t2
      , [dc]    <- Ghc.tyConDataCons tc
      = Just dc
      | otherwise
      = Nothing

    collectCastCoercions :: [Ghc.CoreBind] -> [Ghc.Coercion]
    collectCastCoercions = gos [] . concatMap Ghc.rhssOfBind
      where
        go acc e = case e of
          Ghc.Var{} -> acc
          Ghc.Lit{} -> acc
          Ghc.Type{} -> acc
          Ghc.Coercion{} -> acc
          Ghc.App e1 e2 -> go (go acc e1) e2
          Ghc.Cast e1 c -> go (c:acc) e1
          Ghc.Tick _ e1 -> go acc e1
          Ghc.Lam _ e1 -> go acc e1
          Ghc.Let b e1 -> go (gos acc (Ghc.rhssOfBind b)) e1
          Ghc.Case e1 _ _ alts -> go (gos acc (Ghc.rhssOfAlts alts)) e1

        gos acc = foldr ($) acc . map (flip go)


makeImports :: [(ModName, Ms.BareSpec)] -> [(F.Symbol, F.Sort)]
makeImports specs = concatMap (expSigs . snd) specs'
  where specs' = filter (isSrcImport . fst) specs


makeEmbeds :: GhcSrc -> Bare.GHCTyLookupEnv -> [Ms.BareSpec] -> F.TCEmb Ghc.TyCon
makeEmbeds src env
  = Bare.addClassEmbeds (_gsCls src) (_gsFiTcs src)
  . mconcat
  . map (makeTyConEmbeds env)

makeTyConEmbeds :: Bare.GHCTyLookupEnv -> Ms.BareSpec -> F.TCEmb Ghc.TyCon
makeTyConEmbeds env spec
  = F.tceFromList [ (tc, t) | (c,t) <- F.tceToList (Ms.embeds spec), tc <- symTc c ]
    where
      symTc = Mb.maybeToList . either (const Nothing) Just . Bare.lookupGhcTyConLHName env

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
  { Ms.measures  = Bare.makeHaskellMeasures config src tycEnv lmap mySpec }

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
  { Ms.ealiases  = lmapEAlias . snd <$> Bare.makeHaskellInlines cfg src embs lmap mySpec
  , Ms.dataDecls = Bare.makeHaskellDataDecls cfg mySpec tcs
  }
  where
    tcs          = uniqNub (_gsTcs src ++ refTcs)
    refTcs       = reflectedTyCons cfg embs cbs  mySpec
    cbs          = _giCbs       src

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
                    $ reflectedVars spec cbs ++ measureVars spec cbs
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

reflectedVars :: Ms.BareSpec -> [Ghc.CoreBind] -> [Ghc.Var]
reflectedVars spec cbs =
    filter
      (isReflSym . makeGHCLHNameLocatedFromId)
      (Ghc.bindersOfBinds cbs)
  where
    isReflSym x =
      S.member x (Ms.reflects spec) ||
      S.member (fmap lhNameToResolvedSymbol x) (Ms.privateReflects spec)

measureVars :: Ms.BareSpec -> [Ghc.CoreBind] -> [Ghc.Var]
measureVars spec cbs =
    filter
      ((`S.member` measureSyms) . makeGHCLHNameLocatedFromId)
      (Ghc.bindersOfBinds cbs)
  where
    measureSyms = Ms.hmeas spec

------------------------------------------------------------------------------------------
makeSpecVars :: Config -> GhcSrc -> Ms.BareSpec -> Bare.Env -> Bare.MeasEnv
             -> Bare.Lookup GhcSpecVars
------------------------------------------------------------------------------------------
makeSpecVars cfg src mySpec env measEnv = do
  let tgtVars = Mb.mapMaybe (`M.lookup` hvars) (checks     cfg)
  igVars      <-  sMapM (Bare.lookupGhcIdLHName env) (Ms.ignores mySpec)
  lVars       <-  sMapM (Bare.lookupGhcIdLHName env) (Ms.lvars   mySpec)
  return (SpVar tgtVars igVars lVars cMethods)
  where
    cMethods   = snd3 <$> Bare.meMethods measEnv
    hvars = M.fromList
      [ (Ghc.occNameString $ Ghc.getOccName b, b)
      | b <- Ghc.bindersOfBinds (_giCbs src)
      ]

sMapM :: (Monad m, Eq b, Hashable b) => (a -> m b) -> S.HashSet a -> m (S.HashSet b)
sMapM f xSet = do
 ys <- mapM f (S.toList xSet)
 return (S.fromList ys)

sForM :: (Monad m, Eq b, Hashable b) =>S.HashSet a -> (a -> m b) -> m (S.HashSet b)
sForM xs f = sMapM f xs

------------------------------------------------------------------------------------------
makeSpecQual
  :: Config
  -> Bare.Env
  -> Ghc.GlobalRdrEnv
  -> Bare.TycEnv
  -> Bare.MeasEnv
  -> BareRTEnv
  -> BareSpec
  -> Bare.ModSpecs
  -> GhcSpecQual
------------------------------------------------------------------------------------------
makeSpecQual _cfg env globalRdrEnv tycEnv measEnv _rtEnv mySpec depSpecs = SpQual
  { gsQualifiers = filter okQual quals
  , gsRTAliases  = [] -- makeSpecRTAliases env rtEnv -- TODO-REBARE
  }
  where
    quals =
      makeQualifiers env globalRdrEnv tycEnv mySpec ++
      concatMap qualifiers (M.elems depSpecs)
    -- mSyms        = F.tracepp "MSYMS" $ M.fromList (Bare.meSyms measEnv ++ Bare.meClassSyms measEnv)
    okQual q     = F.notracepp ("okQual: " ++ F.showpp q)
                   $ all (`S.member` mSyms) (F.syms q)
    mSyms        = F.notracepp "MSYMS" . S.fromList
                   $  (fst <$> wiredSortedSyms)
                   ++ (fst <$> Bare.meSyms measEnv)
                   ++ (fst <$> Bare.meClassSyms measEnv)

makeQualifiers
  :: Bare.Env
  -> Ghc.GlobalRdrEnv
  -> Bare.TycEnv
  -> Ms.Spec F.Symbol ty
  -> [F.Qualifier]
makeQualifiers env globalRdrEnv tycEnv spec =
    Mb.mapMaybe (resolveQParams env globalRdrEnv tycEnv) $ Ms.qualifiers spec


-- | @resolveQualParams@ converts the sorts of parameters from, e.g.
--     'Int' ===> 'GHC.Types.Int' or
--     'Ptr' ===> 'GHC.Ptr.Ptr'
--   It would not be required if _all_ qualifiers are scraped from
--   function specs, but we're keeping it around for backwards compatibility.

resolveQParams
  :: Bare.Env
  -> Ghc.GlobalRdrEnv
  -> Bare.TycEnv
  -> F.Qualifier
  -> Maybe F.Qualifier
resolveQParams env globalRdrEnv tycEnv q = do
     qps   <- mapM goQP (F.qParams q)
     return $ q { F.qParams = qps }
  where
    goQP qp          = do { s <- go (F.qpSort qp) ; return qp { F.qpSort = s } }
    go               :: F.Sort -> Maybe F.Sort
    go (FAbs i s)    = FAbs i <$> go s
    go (FFunc s1 s2) = FFunc  <$> go s1 <*> go s2
    go (FApp  s1 s2) = FApp   <$> go s1 <*> go s2
    go (FTC c)       = qualifyFTycon env globalRdrEnv tycEnv c
    go s             = Just s

qualifyFTycon
  :: Bare.Env
  -> Ghc.GlobalRdrEnv
  -> Bare.TycEnv
  -> F.FTycon
  -> Maybe F.Sort
qualifyFTycon env globalRdrEnv tycEnv c
  | isPrimFTC           = Just (FTC c)
  | otherwise           = tyConSort embs . F.atLoc tcs <$> ty
  where
    ty                  = case resolveSymbolToTcName globalRdrEnv tcs of
      Left e -> Ex.throw [e]
      Right lhname -> either Ex.throw Just $
                        Bare.lookupGhcTyConLHName (Bare.reTyLookupEnv env) lhname
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
makeSpecTerm :: Config -> Ms.BareSpec -> LogicNameEnv -> Bare.Env ->
                Bare.Lookup GhcSpecTerm
------------------------------------------------------------------------------------------
makeSpecTerm cfg mySpec lenv env = do
  sizes  <- if structuralTerm cfg then pure mempty else makeSize lenv env mySpec
  lazies <- makeLazy     env mySpec
  autos  <- makeAutoSize env mySpec
  gfail  <- makeFail env mySpec
  return  $ SpTerm
    { gsLazy       = S.insert dictionaryVar (lazies `mappend` sizes)
    , gsFail       = gfail
    , gsStTerm     = sizes
    , gsAutosize   = autos
    , gsNonStTerm  = mempty
    }

makeRelation :: Bare.Env -> ModName -> Bare.SigEnv ->
  [(Located LHName, Located LHName, LocBareType, LocBareType, RelExpr, RelExpr)] -> Bare.Lookup [(Ghc.Var, Ghc.Var, LocSpecType, LocSpecType, RelExpr, RelExpr)]
makeRelation env name sigEnv = mapM go
 where
  go (x, y, tx, ty, a, e) = do
    vx <- Bare.lookupGhcIdLHName env x
    vy <- Bare.lookupGhcIdLHName env y
    return
        ( vx
        , vy
        , Bare.cookSpecType env sigEnv name (Bare.HsTV vx) tx
        , Bare.cookSpecType env sigEnv name (Bare.HsTV vy) ty
        , a
        , e
        )


makeLazy :: Bare.Env -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.Var)
makeLazy env spec =
  sMapM (Bare.lookupGhcIdLHName env) (Ms.lazy spec)

makeFail :: Bare.Env -> Ms.BareSpec -> Bare.Lookup (S.HashSet (Located Ghc.Var))
makeFail env spec =
  sForM (Ms.fails spec) $ \x -> do
    vx <- Bare.lookupGhcIdLHName env x
    return x { val = vx }

makeRewrite :: Bare.Env -> Ms.BareSpec -> Bare.Lookup (S.HashSet (Located Ghc.Var))
makeRewrite env spec =
  sForM (Ms.rewrites spec) $ \x -> do
    vx <-  Bare.lookupGhcIdLHName env x
    return x { val = vx }

makeRewriteWith :: Bare.Env -> Ms.BareSpec -> Bare.Lookup (M.HashMap Ghc.Var [Ghc.Var])
makeRewriteWith env spec = M.fromList <$> makeRewriteWith' env spec

makeRewriteWith' :: Bare.Env -> Spec lname ty -> Bare.Lookup [(Ghc.Var, [Ghc.Var])]
makeRewriteWith' env spec =
  forM (M.toList $ Ms.rewriteWith spec) $ \(x, xs) -> do
    xv  <- Bare.lookupGhcIdLHName env x
    xvs <- mapM (Bare.lookupGhcIdLHName env) xs
    return (xv, xvs)

makeAutoSize :: Bare.Env -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.TyCon)
makeAutoSize env
  = fmap S.fromList
  . mapM (Bare.lookupGhcTyConLHName (Bare.reTyLookupEnv env))
  . S.toList
  . Ms.autosize

makeSize :: LogicNameEnv -> Bare.Env -> Ms.BareSpec -> Bare.Lookup (S.HashSet Ghc.Var)
makeSize lenv env
  = fmap S.fromList
  . mapM lookupGhcSize
  . Mb.mapMaybe getSizeFuns
  . Ms.dataDecls
  where
    lookupGhcSize :: LocSymbol -> Bare.Lookup Ghc.Var
    lookupGhcSize s =
      case lookupSEnv (val s) (lneLHName lenv) of
        Nothing -> panic (Just $ GM.fSrcSpan s) $ "symbol not in scope: " ++ show (val s)
        Just n -> case maybeReflectedLHName n of
          Nothing -> panic (Just $ GM.fSrcSpan s) $ "symbol not reflected: " ++ show (val s)
          Just rn -> Bare.lookupGhcIdLHName env (makeGHCLHName rn (symbol rn) <$ s)

getSizeFuns :: DataDecl -> Maybe LocSymbol
getSizeFuns decl
  | Just x       <- tycSFun decl
  , SymSizeFun f <- x
  = Just f
  | otherwise
  = Nothing


------------------------------------------------------------------------------------------
makeSpecRefl :: GhcSrc -> Bare.ModSpecs -> Bare.Env -> ModName -> GhcSpecSig -> Bare.TycEnv
             -> Bare.Lookup GhcSpecRefl
------------------------------------------------------------------------------------------
makeSpecRefl src specs env name sig tycEnv = do
  autoInst <- makeAutoInst env mySpec
  rwr      <- makeRewrite env mySpec
  rwrWith  <- makeRewriteWith env mySpec
  xtes     <- Bare.makeHaskellAxioms src env tycEnv lmap sig mySpec
  asmReflAxioms <- Bare.makeAssumeReflectAxioms src env tycEnv sig mySpec
  let otherAxioms = thd3 <$> asmReflAxioms
  let myAxioms =
        [ e {eqRec = S.member (eqName e) (exprSymbolsSet (eqBody e))}
        | (_, _, e) <- xtes
        ] ++ otherAxioms
  let asmReflEls = eqName <$> otherAxioms
  let impAxioms  = concatMap (filter ((`notElem` asmReflEls) . eqName) . Ms.axeqs . snd) (M.toList specs)
  case anyNonReflFn of
    Just (actSym , preSym) ->
      let preSym' = symbolString $ lhNameToUnqualifiedSymbol (val preSym) in
      let errorMsg = preSym' ++ " must be reflected first using {-@ reflect " ++ preSym' ++ " @-}"
      in Ex.throw
           (ErrHMeas
             (GM.sourcePosSrcSpan $ loc actSym)
             (pprint $ val actSym)
             (text errorMsg) :: Error)
    Nothing -> return SpRefl
      { gsLogicMap   = lmap
      , gsAutoInst   = autoInst
      , gsImpAxioms  = impAxioms
      , gsMyAxioms   = myAxioms
      , gsReflects   = (fst3 <$> xtes) ++ (fst <$> gsAsmReflects sig)
      , gsHAxioms    = F.notracepp "gsHAxioms" $ xtes ++ asmReflAxioms
      , gsRewrites   = rwr
      , gsRewritesWith = rwrWith
      }
  where
    mySpec       = M.lookupDefault mempty name specs
    lmap         = Bare.reLMap env
    notInReflOnes (_, a) = not $
      a `S.member` Ms.reflects mySpec ||
      fmap lhNameToResolvedSymbol a `S.member` Ms.privateReflects mySpec
    anyNonReflFn = L.find notInReflOnes (Ms.asmReflectSigs mySpec)

------------------------------------------------------------------------------------------
-- | @updateReflSpecSig@ uses the information about reflected functions (included the opaque ones) to update the
--   "assumed" signatures.
------------------------------------------------------------------------------------------
addReflSigs :: Bare.Env -> ModName -> BareRTEnv -> Bare.MeasEnv -> GhcSpecRefl -> GhcSpecSig -> GhcSpecSig
------------------------------------------------------------------------------------------
addReflSigs env name rtEnv measEnv refl sig =
  sig { gsRefSigs = F.notracepp ("gsRefSigs for " ++ F.showpp name) $ map expandReflectedSignature reflSigs
      , gsAsmSigs = F.notracepp ("gsAsmSigs for " ++ F.showpp name) combinedOpaqueAndReflectedAsmSigs
      }
  where
    -- We make sure that the reflected functions are excluded from `gsAsmSigs`, except for the signatures of
    -- actual functions in assume-reflect. The latter are added here because 1. it's what makes tests work
    -- and 2. so that we probably "shadow" the old signatures of the actual function correctly. Note that even if the
    -- signature of the actual function was asserted and not assumed, we do not put our new signature for the actual function
    -- in `gsTySigs` (which is for asserted signatures). Indeed, the new signature will *always* be an assumption since we
    -- add the extra post-condition that the actual and pretended function behave in the same way.
    -- Also, we add here the strengthened post-conditions relative to opaque reflections.
    -- We may redefine assumptions because of opaque reflections, so we just take the union of maps and ignore duplicates.
    -- Based on `M.union`'s handling of duplicates, the leftmost elements in the chain of `M.union` will precede over those
    -- after, which is why we put the opaque reflection first in the chain. The signatures for opaque reflections are created
    -- by strengthening the post-conditions, as in (assume-)reflection.
    combinedOpaqueAndReflectedAsmSigs = M.toList $
        M.fromList (createUpdatedSpecs . fst <$> Bare.meOpaqueRefl measEnv)
        `M.union` M.fromList (filter notReflected (gsAsmSigs sig))
    -- Strengthen the post-condition of each of the opaque reflections.
    createUpdatedSpecs var = (var, Bare.aty <$> Bare.strengthenSpecWithMeasure sig env var (Bare.varLocSym var))
    -- See T1738. We need to expand and qualify any reflected signature /here/, after any
    -- relevant binder has been detected and \"promoted\". The problem stems from the fact that any input
    -- 'BareSpec' will have a 'reflects' list of binders to reflect under the form of an opaque 'Var', that
    -- qualifyExpand can't touch when we do a first pass in 'makeGhcSpec0'. However, once we reflected all
    -- the functions, we are left with a pair (Var, LocSpecType). The latter /needs/ to be qualified and
    -- expanded again, for example in case it has expression aliases derived from 'inlines'.
    expandReflectedSignature :: (Ghc.Var, LocSpecType) -> (Ghc.Var, LocSpecType)
    expandReflectedSignature = fmap (Bare.expand rtEnv (F.dummyPos "expand-refSigs"))

    reflSigs = [ (x, t) | (x, t, _) <- gsHAxioms refl ]
    -- Get the set of all the actual functions (in assume-reflects)
    actualFnsInAssmRefl     = S.fromList $ fst <$> gsAsmReflects sig
    isActualFn           x  = S.member x actualFnsInAssmRefl
    -- Get all the variables from the axioms that are not actual functions (in assume-reflects)
    notReflActualTySigs     = L.filter (not . isActualFn . fst) reflSigs
    -- Get the list of reflected elements. We do not count actual functions in assume reflect as reflected
    reflected               = S.fromList $ fst <$> notReflActualTySigs
    notReflected xt         = fst xt `notElem` reflected

makeAutoInst :: Bare.Env -> Ms.BareSpec ->
                Bare.Lookup (S.HashSet Ghc.Var)
makeAutoInst env spec = S.fromList <$> kvs
  where
    kvs = forM (S.toList (Ms.autois spec)) $
            Bare.lookupGhcIdLHName env


----------------------------------------------------------------------------------------
makeSpecSig :: Config -> ModName -> Ms.BareSpec -> Bare.ModSpecs -> Bare.Env -> Bare.SigEnv -> Bare.TycEnv -> Bare.MeasEnv -> [Ghc.CoreBind]
            -> Bare.Lookup ([RInstance LocBareType], GhcSpecSig)
----------------------------------------------------------------------------------------
makeSpecSig cfg name mySpec specs env sigEnv tycEnv measEnv cbs = do
  mySigs     <- makeTySigs  env sigEnv name mySpec
  aSigs      <- F.notracepp ("makeSpecSig aSigs " ++ F.showpp name) $ makeAsmSigs env sigEnv name allSpecs
  let asmSigs =  Bare.tcSelVars tycEnv ++ aSigs
  let tySigs  = strengthenSigs . concat $
                  [ [(v, (0, t)) | (v, t,_) <- mySigs                         ]   -- NOTE: these weights are to priortize
                  , [(v, (1, t)) | (v, t  ) <- makeMthSigs measEnv            ]   -- user defined sigs OVER auto-generated
                  , [(v, (2, t)) | (v, t  ) <- makeInlSigs env rtEnv allSpecs ]   -- during the strengthening, i.e. to KEEP
                  , [(v, (3, t)) | (v, t  ) <- makeMsrSigs env rtEnv allSpecs ]   -- the binders used in USER-defined sigs
                  ]                                                               -- as they appear in termination metrics
  newTys     <-  makeNewTypes env sigEnv allSpecs
  relation   <-  makeRelation env name sigEnv (Ms.relational mySpec)
  asmRel     <-  makeRelation env name sigEnv (Ms.asmRel mySpec)
  return (instances, SpSig
    { gsTySigs   = tySigs
    , gsAsmSigs  = asmSigs
    , gsAsmReflects = bimap getVar getVar <$> concatMap (asmReflectSigs . snd) allSpecs
    , gsRefSigs  = []
    , gsDicts    = dicts
    -- , gsMethods  = if noclasscheck cfg then [] else Bare.makeMethodTypes dicts (Bare.meClasses  measEnv) cbs
    , gsMethods  = if noclasscheck cfg then [] else Bare.makeMethodTypes (typeclass cfg) dicts (Bare.meClasses  measEnv) cbs
    , gsInSigs   = mempty
    , gsNewTypes = newTys
    , gsTexprs   = [ (v, t, es) | (v, t, Just es) <- mySigs ]
    , gsRelation = relation
    , gsAsmRel   = asmRel
    })
  where
    (instances, dicts) = Bare.makeSpecDictionaries env sigEnv (name, mySpec) (M.toList specs)
    allSpecs   = (name, mySpec) : M.toList specs
    rtEnv      = Bare.sigRTEnv sigEnv
    getVar sym = case Bare.lookupGhcIdLHName env sym of
      Right x -> x
      Left _ -> panic (Just $ GM.fSrcSpan sym) "function to reflect not in scope"

strengthenSigs :: [(Ghc.Var, (Int, LocSpecType))] ->[(Ghc.Var, LocSpecType)]
strengthenSigs sigs = go <$> Misc.groupList sigs
  where
    go (v, ixs)     = (v,) $ L.foldl1' (flip meetLoc) (F.notracepp ("STRENGTHEN-SIGS: " ++ F.showpp v) (prio ixs))
    prio            = fmap snd . Misc.sortOn fst
    meetLoc         :: LocSpecType -> LocSpecType -> LocSpecType
    meetLoc t1 t2   = t1 {val = val t1 `meet` val t2}

makeMthSigs :: Bare.MeasEnv -> [(Ghc.Var, LocSpecType)]
makeMthSigs measEnv = [ (v, t) | (_, v, t) <- Bare.meMethods measEnv ]

makeInlSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)]
makeInlSigs env rtEnv
  = makeLiftedSigs rtEnv (CoreToLogic.inlineSpecType (typeclass (getConfig env)))
  . concatMap (map (lookupFunctionId env) . S.toList . Ms.inlines . snd)

makeMsrSigs :: Bare.Env -> BareRTEnv -> [(ModName, Ms.BareSpec)] -> [(Ghc.Var, LocSpecType)]
makeMsrSigs env rtEnv
  = makeLiftedSigs rtEnv (CoreToLogic.inlineSpecType (typeclass (getConfig env)))
  . concatMap (map (lookupFunctionId env) . S.toList . Ms.hmeas . snd)

lookupFunctionId :: Bare.Env -> Located LHName -> Ghc.Id
lookupFunctionId env x =
    either (panic (Just $ GM.fSrcSpan x) "function not found") id $
    Bare.lookupGhcIdLHName env x

makeLiftedSigs :: BareRTEnv -> (Ghc.Var -> SpecType) -> [Ghc.Var] -> [(Ghc.Var, LocSpecType)]
makeLiftedSigs rtEnv f xs
  = [(x, lt) | x <- xs
             , let lx = GM.locNamedThing x
             , let lt = expand $ lx {val = f x}
    ]
  where
    expand   = Bare.specExpandType rtEnv

makeTySigs :: Bare.Env -> Bare.SigEnv -> ModName -> Ms.BareSpec
           -> Bare.Lookup [(Ghc.Var, LocSpecType, Maybe [Located F.Expr])]
makeTySigs env sigEnv name spec = do
  bareSigs   <- bareTySigs env                     spec
  expSigs    <- makeTExpr  env bareSigs rtEnv spec
  let rawSigs = Bare.resolveLocalBinds env expSigs
  return [ (x, cook x bt, z) | (x, bt, z) <- rawSigs ]
  where
    rtEnv     = Bare.sigRTEnv sigEnv
    cook x bt = Bare.cookSpecType env sigEnv name (Bare.HsTV x) bt

bareTySigs :: Bare.Env -> Ms.BareSpec -> Bare.Lookup [(Ghc.Var, LocBareType)]
bareTySigs env spec = checkDuplicateSigs <$> vts
  where
    vts = forM ( Ms.sigs spec ) $ \ (x, t) -> do
            v <- F.notracepp "LOOKUP-GHC-VAR" $ Bare.lookupGhcIdLHName env x
            return (v, t)

-- checkDuplicateSigs :: [(Ghc.Var, LocSpecType)] -> [(Ghc.Var, LocSpecType)]
checkDuplicateSigs :: (Symbolic x) => [(x, F.Located t)] -> [(x, F.Located t)]
checkDuplicateSigs xts = case Misc.uniqueByKey symXs  of
  Left (k, ls) -> uError (errDupSpecs (pprint k) (GM.sourcePosSrcSpan <$> ls))
  Right _      -> xts
  where
    symXs = [ (F.symbol x, F.loc t) | (x, t) <- xts ]


makeAsmSigs :: Bare.Env -> Bare.SigEnv -> ModName -> [(ModName, Ms.BareSpec)] -> Bare.Lookup [(Ghc.Var, LocSpecType)]
makeAsmSigs env sigEnv myName specs = do
  raSigs <- rawAsmSigs env myName specs
  return [ (x, t) | (name, x, bt) <- raSigs, let t = Bare.cookSpecType env sigEnv name (Bare.LqTV x) bt ]

rawAsmSigs :: Bare.Env -> ModName -> [(ModName, Ms.BareSpec)] -> Bare.Lookup [(ModName, Ghc.Var, LocBareType)]
rawAsmSigs env myName specs = do
  aSigs <- allAsmSigs env myName specs
  return [ (m, v, t) | (v, sigs) <- aSigs, let (m, t) = myAsmSig v sigs ]

myAsmSig :: Ghc.Var -> [(Bool, ModName, LocBareType)] -> (ModName, LocBareType)
myAsmSig v sigs = Mb.fromMaybe errImp (mbHome `mplus` mbImp)
  where
    mbHome      = takeUnique mkErr                  sigsHome
    -- In case we import multiple specifications for the same function stemming from `assume-reflect` from different modules, we want
    -- to follow the same convention as in other places and so take the last one in alphabetical order and shadow the others
    mbImp       = takeBiggest   fst (Misc.firstGroup sigsImp) -- see [NOTE:Prioritize-Home-Spec]
    sigsHome    = [(m, t)      | (True,  m, t) <- sigs ]
    sigsImp     = F.notracepp ("SIGS-IMP: " ++ F.showpp v)
                  [(d, (m, t)) | (False, m, t) <- sigs, let d = nameDistance vName m]
    mkErr ts    = ErrDupSpecs (Ghc.getSrcSpan v) (F.pprint v) (GM.sourcePosSrcSpan . F.loc . snd <$> ts) :: UserError
    errImp      = impossible Nothing "myAsmSig: cannot happen as sigs is non-null"
    vName       = GM.takeModuleNames (F.symbol v)

makeTExpr :: Bare.Env -> [(Ghc.Var, LocBareType)] -> BareRTEnv -> Ms.BareSpec
          -> Bare.Lookup [(Ghc.Var, LocBareType, Maybe [Located F.Expr])]
makeTExpr env tySigs rtEnv spec = do
  vExprs       <- M.fromList <$> makeVarTExprs env spec
  let vSigExprs = Misc.hashMapMapWithKey (\v t -> (t, M.lookup v vExprs)) vSigs
  return [ (v, t, qual <$> es) | (v, (t, es)) <- M.toList vSigExprs ]
  where
    qual es = expandTermExpr rtEnv <$> es
    vSigs = M.fromList tySigs

expandTermExpr :: BareRTEnv -> Located F.Expr -> Located F.Expr
expandTermExpr rtEnv le
        = F.atLoc le (Bare.expand rtEnv l e)
  where
    l   = F.loc le
    e   = F.val le

makeVarTExprs :: Bare.Env -> Ms.BareSpec -> Bare.Lookup [(Ghc.Var, [Located F.Expr])]
makeVarTExprs env spec =
  forM (Ms.termexprs spec) $ \(x, es) -> do
    vx <- Bare.lookupGhcIdLHName env x
    return (vx, es)

----------------------------------------------------------------------------------------
-- [NOTE:Prioritize-Home-Spec] Prioritize spec for THING defined in
-- `Foo.Bar.Baz.Quux.x` over any other specification, IF GHC's
-- fully qualified name for THING is `Foo.Bar.Baz.Quux.x`.
--
-- For example, see tests/names/neg/T1078.hs for example,
-- which assumes a spec for `head` defined in both
--
--   (1) Data/ByteString_LHAssumptions.hs
--   (2) Data/ByteString/Char8_LHAssumptions.hs
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

takeBiggest :: (Ord b) => (a -> b) -> [a] -> Maybe a
takeBiggest _ []  = Nothing
takeBiggest f xs  = Just $ L.maximumBy (compare `on` f) xs

allAsmSigs :: Bare.Env -> ModName -> [(ModName, Ms.BareSpec)] ->
              Bare.Lookup [(Ghc.Var, [(Bool, ModName, LocBareType)])]
allAsmSigs env myName specs = do
  let aSigs = [ (name, locallyDefined, x, t) | (name, spec) <- specs
                                   , (locallyDefined, x, t) <- getAsmSigs myName name spec ]
  vSigs    <- forM aSigs $ \(name, locallyDefined, x, t) -> do
                v <- Bare.lookupGhcIdLHName env x
                return (v, (locallyDefined, name, t))
  return $ Misc.groupList
    [ (v, z) | (v, z) <- vSigs
      -- TODO: we require signatures to be in scope because LH includes them in
      -- the environment of contraints sometimes. The criteria to add bindings to
      -- constraints should account instead for what logic functions are used in
      -- the constraints, which should be easier to do when precise renaming has
      -- been implemented for expressions and reflected functions.
    , isUsedExternalVar v ||
      isInScope v ||
      isNonTopLevelVar v -- Keep assumptions about non-top-level bindings
    ]
  where
    isUsedExternalVar :: Ghc.Var -> Bool
    isUsedExternalVar v = case Ghc.idDetails v of
      Ghc.DataConWrapId dc ->
        Ghc.getName v `Ghc.elemNameSet` Bare.reUsedExternals env
         ||
        Ghc.getName (Ghc.dataConWorkId dc) `Ghc.elemNameSet` Bare.reUsedExternals env
      _ ->
        Ghc.getName v `Ghc.elemNameSet` Bare.reUsedExternals env

    isInScope :: Ghc.Var -> Bool
    isInScope v0 =
      let inScope v = not $ null $
            Ghc.lookupGRE_Name
              (Ghc.tcg_rdr_env $ Bare.reTcGblEnv env)
              (Ghc.getName v)
       in -- Names of data constructors are not found in the variable namespace
          -- so we look them instead in the data constructor namespace.
          case Ghc.idDetails v0 of
            Ghc.DataConWrapId dc -> inScope dc
            Ghc.DataConWorkId dc -> inScope dc
            _ -> inScope v0

    isNonTopLevelVar = Mb.isNothing . Ghc.nameModule_maybe . Ghc.getName

getAsmSigs :: ModName -> ModName -> Ms.BareSpec -> [(Bool, Located LHName, LocBareType)]
getAsmSigs myName name spec
  | myName == name = [ (True, x,  t) | (x, t) <- Ms.asmSigs spec ] -- MUST    resolve, or error
  | otherwise      =
      [ (False, x, t)
      | (x, t) <- Ms.asmSigs spec
                  ++ Ms.sigs spec
      ]

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
    forM nameDecls $ uncurry (makeNewType env sigEnv)
  where
    nameDecls = [(name, d) | (name, spec) <- specs, d <- Ms.newtyDecls spec]

makeNewType :: Bare.Env -> Bare.SigEnv -> ModName -> DataDecl ->
               Bare.Lookup [(Ghc.TyCon, LocSpecType)]
makeNewType env sigEnv name d = do
  tcMb <- Bare.lookupGhcDnTyCon env name tcName
  case tcMb of
    Just tc -> return [(tc, lst)]
    _       -> return []
  where
    tcName                    = tycName d
    lst                       = Bare.cookSpecType env sigEnv name Bare.GenTV bt
    bt                        = getTy tcName (tycSrcPos d) (Mb.fromMaybe [] (tycDCons d))
    getTy _ l [c]
      | [(_, t)] <- dcFields c = Loc l l t
    getTy n l _                = Ex.throw (mkErr n l)
    mkErr n l                  = ErrOther (GM.sourcePosSrcSpan l) ("Bad new type declaration:" <+> F.pprint n) :: UserError

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
  , gsMeasures   = ms1 ++ ms2
  , gsOpaqueRefls = fst <$> Bare.meOpaqueRefl measEnv
  , gsInvariants = Misc.nubHashOn (F.loc . snd) invs
  , gsIaliases   = concatMap (makeIAliases env sigEnv) (M.toList specs)
  , gsUnsorted   = usI ++ concatMap msUnSorted (concatMap measures specs)
  }
  where
    allowTC      = typeclass (getConfig env)
    measVars     = Bare.getMeasVars env measEnv
    measuresSp   = Bare.meMeasureSpec measEnv
    ms1          = M.elems (Ms.measMap measuresSp)
    ms2          = Ms.imeas   measuresSp
    mySpec       = M.lookupDefault mempty name specs
    name         = _giTargetMod      src
    (minvs,usI)  = makeMeasureInvariants sig mySpec
    invs         = minvs ++ concatMap (makeInvariants env sigEnv) (M.toList specs)

makeIAliases :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> [(LocSpecType, LocSpecType)]
makeIAliases env sigEnv (name, spec)
  = [ z | Right z <- mkIA <$> Ms.ialiases spec ]
  where
    -- mkIA :: (LocBareType, LocBareType) -> Either _ (LocSpecType, LocSpecType)
    mkIA (t1, t2) = (,) <$> mkI' t1 <*> mkI' t2
    mkI'          = Bare.cookSpecTypeE env sigEnv name Bare.GenTV

makeInvariants :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec) -> [(Maybe Ghc.Var, Located SpecType)]
makeInvariants env sigEnv (name, spec) =
  [ (Nothing, t)
    | (_, bt) <- Ms.invariants spec
    , Bare.knownGhcType env bt
    , let t = Bare.cookSpecType env sigEnv name Bare.GenTV bt
  ] ++
  concat [ (Nothing,) . makeSizeInv l <$>  ts
    | (bts, l) <- Ms.dsize spec
    , all (Bare.knownGhcType env) bts
    , let ts = Bare.cookSpecType env sigEnv name Bare.GenTV <$> bts
  ]

makeSizeInv :: F.Symbol -> Located SpecType -> Located SpecType
makeSizeInv s lst = lst{val = go (val lst)}
  where go (RApp c ts rs r) = RApp c ts rs (r `meet` nat)
        go (RAllT a t r)    = RAllT a (go t) r
        go t = t
        nat  = MkUReft (Reft (vv_, PAtom Le (ECon $ I 0) (EApp (EVar s) (eVar vv_))))
                       mempty

makeMeasureInvariants :: GhcSpecSig -> Ms.BareSpec -> ([(Maybe Ghc.Var, LocSpecType)], [UnSortedExpr])
makeMeasureInvariants sig mySpec
  = Mb.catMaybes <$>
    unzip (measureTypeToInv <$> [(x, (y, ty)) | x <- xs, (y, ty) <- sigs
                                         , x == makeGHCLHNameLocatedFromId y ])
  where
    sigs = gsTySigs sig
    xs   = S.toList (Ms.hmeas  mySpec)

measureTypeToInv :: (Located LHName, (Ghc.Var, LocSpecType)) -> ((Maybe Ghc.Var, LocSpecType), Maybe UnSortedExpr)
measureTypeToInv (x, (v, t))
  = notracepp "measureTypeToInv" ((Just v, t {val = mtype}), usorted)
  where
    trep = toRTypeRep (val t)
    rts  = ty_args  trep
    args = ty_binds trep
    res  = ty_res   trep
    z    = last args
    tz   = last rts
    usorted =
      if isSimpleADT tz then
        Nothing
      else
        first (:[]) <$> mkReft (dummyLoc $ val $ makeGHCLHNameLocatedFromId v) z tz res
    mtype
      | null rts
      = uError $ ErrHMeas (GM.sourcePosSrcSpan $ loc t) (pprint x) "Measure has no arguments!"
      | otherwise
      = mkInvariant x z tz res
    isSimpleADT (RApp _ ts _ _) = all isRVar ts
    isSimpleADT _               = False

mkInvariant :: Located LHName -> Symbol -> SpecType -> SpecType -> SpecType
mkInvariant x z t tr = strengthen (top <$> t) (MkUReft reft' mempty)
      where
        reft' = Mb.maybe mempty Reft mreft
        mreft = mkReft x z t tr


mkReft :: Located LHName -> Symbol -> SpecType -> SpecType -> Maybe (Symbol, Expr)
mkReft x z _t tr
  | Just q <- stripRTypeBase tr
  = let Reft (v, p) = toReft q
        su          = mkSubst [(v, mkEApp (fmap lhNameToResolvedSymbol x) [EVar v]), (z,EVar v)]
        -- p'          = pAnd $ filter (\e -> z `notElem` syms e) $ conjuncts p
    in  Just (v, subst su p)
mkReft _ _ _ _
  = Nothing


-- REBARE: formerly, makeGhcSpec3
-------------------------------------------------------------------------------------------
makeSpecName :: Bare.TycEnv -> Bare.MeasEnv -> [Ghc.Id] -> GhcSpecNames
-------------------------------------------------------------------------------------------
makeSpecName tycEnv measEnv dataConIds = SpNames
  { gsDconsP   = [ F.atLoc dc (dcpCon dc) | dc <- datacons ++ cls ]
  , gsTconsP   = tycons
  -- , gsLits = mempty                                              -- TODO-REBARE, redundant with gsMeas
  , gsTcEmbeds = Bare.tcEmbs     tycEnv
  , gsADTs     = Bare.tcAdts     tycEnv
  , gsTyconEnv = Bare.tcTyConMap tycEnv
  , gsDataConIds = dataConIds
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
    -- See the documentation of @addOpaqueReflMeas@. The selectors here are only
    -- those belonging to types mentioned in the types of functions defined in
    -- the current module.
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
    tyi           = makeTyConInfo embs fiTcs tycons
    -- tycons        = F.tracepp "TYCONS" $ Misc.replaceWith tcpCon tcs wiredTyCons
    -- datacons      =  Bare.makePluggedDataCons embs tyi (Misc.replaceWith (dcpCon . val) (F.tracepp "DATACONS" $ concat dcs) wiredDataCons)
    tycons        = tcs ++ wiredTyCons
    datacons      = Bare.makePluggedDataCon (typeclass cfg) embs tyi <$> (concat dcs ++ wiredDataCons)
    tds           = [(name, tcpCon tcp, dd) | (name, tcp, Just dd) <- tcDds]
    (diag1, adts) = Bare.makeDataDecls cfg embs myName tds       datacons
    dm            = Bare.dataConMap adts
    dcSelectors   = concatMap (Bare.makeMeasureSelectors cfg dm) (if reflection cfg then charDataCon:datacons else datacons)
    fiTcs         = _gsFiTcs (Bare.reSrc env)



makeTycEnv1 ::
     Bare.Env
  -> (Bare.TycEnv, [Located DataConP])
  -> (Ghc.CoreExpr -> F.Expr)
  -> (Ghc.CoreExpr -> Ghc.TcRn Ghc.CoreExpr)
  -> Ghc.TcRn Bare.TycEnv
makeTycEnv1 env (tycEnv, datacons) coreToLg simplifier = do
  -- fst for selector generation, snd for dataconsig generation
  lclassdcs <- forM classdcs $ traverse (Bare.elaborateClassDcp coreToLg simplifier)
  let recSelectors = Bare.makeRecordSelectorSigs env (dcs ++ (fmap . fmap) snd lclassdcs)
  pure $
    tycEnv {Bare.tcSelVars = recSelectors, Bare.tcDataCons = F.val <$> ((fmap . fmap) fst lclassdcs ++ dcs )}
  where
    (classdcs, dcs) =
      L.partition
        (Ghc.isClassTyCon . Ghc.dataConTyCon . dcpCon . F.val) datacons

-- REBARE: formerly, makeGhcCHOP2
-------------------------------------------------------------------------------------------
makeMeasEnv :: Bare.Env -> Bare.TycEnv -> Bare.SigEnv -> Bare.ModSpecs ->
               Bare.Lookup Bare.MeasEnv
-------------------------------------------------------------------------------------------
makeMeasEnv env tycEnv sigEnv specs = do
  (cls, mts)  <- Bare.makeClasses        env sigEnv name specs
  let dms      = Bare.makeDefaultMethods env mts
  measures0   <- mapM (Bare.makeMeasureSpec env sigEnv name) (M.toList specs)
  let measures = mconcat (Ms.mkMSpec' dcSelectors : measures0)
  let (cs, ms) = Bare.makeMeasureSpec'  (typeclass $ getConfig env)   measures
  let cms      = Bare.makeClassMeasureSpec measures
  let cms'     = [ (val l, cSort t <$ l)  | (l, t) <- cms ]
  let ms'      = [ (lhNameToResolvedSymbol (F.val lx), F.atLoc lx t)
                 | (lx, t) <- ms
                 , Mb.isNothing (lookup (val lx) cms')
                 ]
  let cs'      = [ (v, txRefs v t) | (v, t) <- Bare.meetDataConSpec (typeclass (getConfig env)) embs cs (datacons ++ cls)]
  return Bare.MeasEnv
    { meMeasureSpec = measures
    , meClassSyms   = map (first lhNameToResolvedSymbol) cms'
    , meSyms        = ms'
    , meDataCons    = cs'
    , meClasses     = cls
    , meMethods     = mts ++ dms
    , meOpaqueRefl  = mempty
    }
  where
    txRefs v t    = Bare.txRefSort tyi embs (t <$ GM.locNamedThing v)
    tyi           = Bare.tcTyConMap    tycEnv
    dcSelectors   = Bare.tcSelMeasures tycEnv
    datacons      = Bare.tcDataCons    tycEnv
    embs          = Bare.tcEmbs        tycEnv
    name          = Bare.tcName        tycEnv


-- | Adds the opaque reflections to the measure environment
--
-- Returns a new environment that is the old one enhanced with the opaque
-- reflections.
--
-- At the moment this function also has the effect of adding selector and
-- checker measures for data constructors that are needed by reflected
-- functions. This even adds measures that are needed by functions reflected
-- from unfoldings (public and private), whose datatypes come from imported
-- modules. This overlaps a bit with 'makeTycEnv0', which also adds measures for
-- selectors and checkers, but only for datatypes mentioned in the type
-- signatures of functions defined in the current module.
-------------------------------------------------------------------------------------------
addOpaqueReflMeas :: Config -> Bare.TycEnv -> Bare.Env -> Ms.BareSpec -> Bare.MeasEnv -> Bare.ModSpecs ->
               [(Ghc.Var, LocSpecType, F.Equation)] ->
               Bare.Lookup Bare.MeasEnv
----------------------- --------------------------------------------------------------------
addOpaqueReflMeas cfg tycEnv env spec measEnv specs eqs = do
  dcs   <- snd <$> Bare.makeConTypes'' env name spec dataDecls []
  let datacons      = Bare.makePluggedDataCon (typeclass cfg) embs tyi <$> concat dcs
  let dcSelectors   = concatMap (Bare.makeMeasureSelectors cfg dm) datacons
  -- Rest of the code is the same idea as for makeMeasEnv, only we just care on how to get
  -- `meSyms` (no class, data constructor or other stuff here).
  let measures = mconcat (Ms.mkMSpec' dcSelectors : measures0)
  let (cs, ms) = Bare.makeMeasureSpec'  (typeclass $ getConfig env)   measures
  let ms'      = [ (lhNameToResolvedSymbol (F.val lx), F.atLoc lx t) | (lx, t) <- ms ]
  let cs'      = [ (v, txRefs v t) | (v, t) <- Bare.meetDataConSpec (typeclass (getConfig env)) embs cs (val <$> datacons)]
  return $ measEnv <> mempty
    { Bare.meMeasureSpec = measures
    , Bare.meSyms        = ms'
    , Bare.meDataCons    = cs'
    , Bare.meOpaqueRefl  = opaqueRefl
    }
  where
    -- We compute things in the same way as in makeMeasEnv
    txRefs v t    = Bare.txRefSort tyi embs (t <$ GM.locNamedThing v)
    (measures0, opaqueRefl) = Bare.makeOpaqueReflMeasures env measEnv specs eqs
    -- Note: it is important to do toList after applying `dataConTyCon` because
    -- obviously several data constructors can refer to the same `TyCon` so we
    -- could have duplicates
    -- We skip the variables from the axiom equations that correspond to the actual functions
    -- of opaque reflections, since we never need to look at the unfoldings of those
    actualFns = S.fromList $ val . fst <$> Ms.asmReflectSigs spec
    shouldBeUsedForScanning sym = not (sym `S.member` actualFns)
    varsUsedForTcScanning =
      [ v
      | (v, _, _) <- eqs
      , shouldBeUsedForScanning $ makeGHCLHName (Ghc.getName v) (symbol v)
      ]
    tcs           = S.toList $ Ghc.dataConTyCon `S.map` Bare.getReflDCs measEnv varsUsedForTcScanning
    dataDecls     = Bare.makeHaskellDataDecls cfg spec tcs
    tyi           = Bare.tcTyConMap    tycEnv
    embs          = Bare.tcEmbs        tycEnv
    dm            = Bare.tcDataConMap  tycEnv
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
makeLiftedSpec name src env refl sData sig qual myRTE lSpec0 = lSpec0
  { Ms.asmSigs    = F.notracepp   ("makeLiftedSpec : ASSUMED-SIGS " ++ F.showpp name ) (xbs ++ myDCs)
  , Ms.sigs       = F.notracepp   ("makeLiftedSpec : LIFTED-SIGS " ++ F.showpp name ) $
                      mkSigs (gsTySigs sig)
  , Ms.invariants = [ (Bare.varLocSym <$> x, Bare.specToBare <$> t)
                       | (x, t) <- gsInvariants sData
                       , isLocInFile srcF t
                    ]
  , Ms.axeqs      = gsMyAxioms refl
  , Ms.aliases    = F.notracepp "MY-ALIASES" $ M.elems . typeAliases $ myRTE
  , Ms.ealiases   = M.elems . exprAliases $ myRTE
  , Ms.qualifiers = filter (isLocInFile srcF) (gsQualifiers qual)
  }
  where
    myDCs         = filter (isLocalName . val . fst) $ mkSigs (gsCtors sData)
    mkSigs xts    = [ toBare (x, t) | (x, t) <- xts
                    , not (S.member x reflVars) && isExportedVar (toTargetSrc src) x
                    ]
    toBare (x, t) = (makeGHCLHNameLocatedFromId x, Bare.specToBare <$> t)
    xbs           = toBare <$> reflTySigs
    reflTySigs    = [(x, t) | (x,t,_) <- gsHAxioms refl]
    reflVars      = S.fromList (fst <$> reflTySigs)
    -- myAliases fld = M.elems . fld $ myRTE
    srcF          = _giTarget src

    isLocalName = \case
      LHNResolved (LHRGHC n) _ ->
        Just (Ghc.tcg_mod (Bare.reTcGblEnv env)) == Ghc.nameModule_maybe n
      _ ->
        False

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
