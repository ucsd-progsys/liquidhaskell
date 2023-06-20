{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PartialTypeSignatures      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wwarn=deprecations #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Liquid.GHC.Interface (

  -- * Printer
    pprintCBs

  -- * predicates
  -- , isExportedVar
  -- , exportedVars

  -- * Internal exports (provisional)
  , extractSpecComments
  , extractSpecQuotes'
  , makeLogicMap
  , classCons
  , derivedVars
  , importVars
  , makeGhcSrc
  , allImports
  , qualifiedImports
  , modSummaryHsFile
  , makeFamInstEnv
  , parseSpecFile
  , clearSpec
  , checkFilePragmas
  , keepRawTokenStream
  , ignoreInline
  , lookupTyThings
  , availableTyCons
  , availableVars
  , updLiftedSpec
  , getTyThingsFromExternalModules
  ) where

import Prelude hiding (error)

import           Liquid.GHC.API as Ghc hiding ( text
                                                               , (<+>)
                                                               , panic
                                                               , vcat
                                                               , showPpr
                                                               , mkStableModule
                                                               , Target
                                                               , Located
                                                               )
import qualified Liquid.GHC.API as Ghc

import Control.Exception
import Control.Monad

import Data.Data
import Data.IORef
import Data.List hiding (intersperse)
import Data.Maybe

import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)

import qualified Data.HashSet        as S

import System.Console.CmdArgs.Verbosity hiding (Loud)
import System.IO
import Text.Megaparsec.Error
import Text.PrettyPrint.HughesPJ        hiding (first, (<>))
import Language.Fixpoint.Types          hiding (err, panic, Error, Result, Expr)
import qualified Language.Fixpoint.Misc as Misc
import Liquid.GHC.Misc
import Liquid.GHC.Types (MGIModGuts(..), miModGuts)
import Liquid.GHC.Play
import qualified Liquid.GHC.GhcMonadLike as GhcMonadLike
import Liquid.GHC.GhcMonadLike (GhcMonadLike, askHscEnv)
import Language.Haskell.Liquid.WiredIn (isDerivedInstance)
import qualified Language.Haskell.Liquid.Measure  as Ms
import qualified Language.Haskell.Liquid.Misc     as Misc
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Transforms.ANF
import Language.Haskell.Liquid.Types hiding (Spec)
-- import Language.Haskell.Liquid.Types.PrettyPrint
-- import Language.Haskell.Liquid.Types.Visitors
import Language.Haskell.Liquid.UX.QuasiQuoter
import Language.Haskell.Liquid.UX.Tidy

import Optics hiding (ix)

import qualified Debug.Trace as Debug


--------------------------------------------------------------------------------
-- | Extract Ids ---------------------------------------------------------------
--------------------------------------------------------------------------------

classCons :: Maybe [ClsInst] -> [Id]
classCons Nothing   = []
classCons (Just cs) = concatMap (dataConImplicitIds . head . tyConDataCons . classTyCon . is_cls) cs

derivedVars :: Config -> MGIModGuts -> [Var]
derivedVars cfg mg  = concatMap (dFunIdVars cbs . is_dfun) derInsts
  where
    derInsts
      | checkDer    = insts
      | otherwise   = filter isDerivedInstance insts
    insts           = mgClsInstances mg
    checkDer        = checkDerived cfg
    cbs             = mgi_binds mg


mgClsInstances :: MGIModGuts -> [ClsInst]
mgClsInstances = fromMaybe [] . mgi_cls_inst

dFunIdVars :: CoreProgram -> DFunId -> [Id]
dFunIdVars cbs fd  = notracepp msg $ concatMap bindersOf cbs' ++ deps
  where
    msg            = "DERIVED-VARS-OF: " ++ showpp fd
    cbs'           = filter f cbs
    f (NonRec x _) = eqFd x
    f (Rec xes)    = any eqFd (fst <$> xes)
    eqFd x         = varName x == varName fd
    deps           = concatMap unfoldDep unfolds
    unfolds        = unfoldingInfo . idInfo <$> concatMap bindersOf cbs'

unfoldDep :: Unfolding -> [Id]
unfoldDep (DFunUnfolding _ _ e)       = concatMap exprDep e
unfoldDep CoreUnfolding {uf_tmpl = e} = exprDep e
unfoldDep _                           = []

exprDep :: CoreExpr -> [Id]
exprDep = freeVars S.empty

importVars :: CoreProgram -> [Id]
importVars = freeVars S.empty

_definedVars :: CoreProgram -> [Id]
_definedVars = concatMap defs
  where
    defs (NonRec x _) = [x]
    defs (Rec xes)    = map fst xes

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

updLiftedSpec :: Ms.BareSpec -> Maybe Ms.BareSpec -> Ms.BareSpec
updLiftedSpec s1 Nothing   = s1
updLiftedSpec s1 (Just s2) = clearSpec s1 `mappend` s2

clearSpec :: Ms.BareSpec -> Ms.BareSpec
clearSpec s = s { sigs = [], asmSigs = [], aliases = [], ealiases = [], qualifiers = [], dataDecls = [] }

keepRawTokenStream :: ModSummary -> ModSummary
keepRawTokenStream modSummary = modSummary
  { ms_hspp_opts = ms_hspp_opts modSummary `gopt_set` Opt_KeepRawTokenStream }

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen
---------------------------------------------------------------------------------------

makeGhcSrc :: Config -> FilePath -> TypecheckedModule -> ModSummary -> Ghc GhcSrc
makeGhcSrc cfg file typechecked modSum = do
  modGuts'          <- GhcMonadLike.desugarModule modSum typechecked

  let modGuts        = makeMGIModGuts modGuts'
  hscEnv            <- getSession
  coreBinds         <- liftIO $ anormalize cfg hscEnv modGuts'
  _                 <- liftIO $ whenNormal $ Misc.donePhase Misc.Loud "A-Normalization"
  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) (mgi_tcs modGuts)
  (fiTcs, fiDcs)    <- makeFamInstEnv <$> liftIO (getFamInstances hscEnv)
  things            <- lookupTyThings hscEnv modSum (fst $ tm_internals_ typechecked)

  availableTcs      <- availableTyCons hscEnv modSum (fst $ tm_internals_ typechecked) (mg_exports modGuts')

  let impVars        = importVars coreBinds ++ classCons (mgi_cls_inst modGuts)

  --liftIO $ do
  --  print $ "_gsTcs   => " ++ show (nub $ (mgi_tcs      modGuts) ++ availableTcs)
  --  print $ "_gsFiTcs => " ++ show fiTcs
  --  print $ "_gsFiDcs => " ++ show fiDcs
  --  print $ "dataCons => " ++ show dataCons
  --  print $ "defVars  => " ++ show (dataCons ++ (letVars coreBinds))

  return $ Src
    { _giTarget    = file
    , _giTargetMod = ModName Target (moduleName (ms_mod modSum))
    , _giCbs       = coreBinds
    , _giImpVars   = impVars
    , _giDefVars   = dataCons ++ letVars coreBinds
    , _giUseVars   = readVars coreBinds
    , _giDerVars   = S.fromList (derivedVars cfg modGuts)
    , _gsExports   = mgi_exports  modGuts
    , _gsTcs       = nub $ mgi_tcs modGuts ++ availableTcs
    , _gsCls       = mgi_cls_inst modGuts
    , _gsFiTcs     = fiTcs
    , _gsFiDcs     = fiDcs
    , _gsPrimTcs   = Ghc.primTyCons
    , _gsQualImps  = qualifiedImports (maybe mempty (view _2) (tm_renamed_source typechecked))
    , _gsAllImps   = allImports       (maybe mempty (view _2) (tm_renamed_source typechecked))
    , _gsTyThings  = [ t | (_, Just t) <- things ]
    }

_impThings :: [Var] -> [TyThing] -> [TyThing]
_impThings vars  = filter ok
  where
    vs          = S.fromList vars
    ok (AnId x) = S.member x vs
    ok _        = True

allImports :: [LImportDecl GhcRn] -> S.HashSet Symbol
allImports = \case
  []-> Debug.trace "WARNING: Missing RenamedSource" mempty
  imps -> S.fromList (symbol . unLoc . ideclName . unLoc <$> imps)

qualifiedImports :: [LImportDecl GhcRn] -> QImports
qualifiedImports = \case
  []   -> Debug.trace "WARNING: Missing RenamedSource" (qImports mempty)
  imps -> qImports [ (qn, n) | i         <- imps
                                          , let decl   = unLoc i
                                          , let m      = unLoc (ideclName decl)
                                          , qm        <- maybeToList (unLoc <$> ideclAs decl)
                                          , let [n,qn] = symbol <$> [m, qm]
                                          ]

qImports :: [(Symbol, Symbol)] -> QImports
qImports qns  = QImports
  { qiNames   = Misc.group qns
  , qiModules = S.fromList (snd <$> qns)
  }


---------------------------------------------------------------------------------------
-- | @lookupTyThings@ grabs all the @Name@s and associated @TyThing@ known to GHC
--   for this module; we will use this to create our name-resolution environment
--   (see `Bare.Resolve`)
---------------------------------------------------------------------------------------
lookupTyThings :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> m [(Name, Maybe TyThing)]
lookupTyThings hscEnv modSum tcGblEnv = forM names (lookupTyThing hscEnv modSum tcGblEnv)
  where
    names :: [Ghc.Name]
    names  = liftM2 (++)
             (fmap Ghc.greMangledName . Ghc.globalRdrEnvElts . tcg_rdr_env)
             (fmap is_dfun_name . tcg_insts) tcGblEnv
-- | Lookup a single 'Name' in the GHC environment, yielding back the 'Name' alongside the 'TyThing',
-- if one is found.
lookupTyThing :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> Name -> m (Name, Maybe TyThing)
lookupTyThing hscEnv modSum tcGblEnv n = do
  mi  <- GhcMonadLike.moduleInfoTc modSum tcGblEnv
  tt1 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n
  tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n
  tt3 <-          GhcMonadLike.modInfoLookupName mi n
  tt4 <- liftIO $ Ghc.lookupType hscEnv n
  return (n, Misc.firstMaybes [tt1, tt2, tt3, tt4])

availableTyThings :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> [AvailInfo] -> m [TyThing]
availableTyThings hscEnv modSum tcGblEnv avails =
    fmap catMaybes $
      mapM (fmap snd . lookupTyThing hscEnv modSum tcGblEnv) $
      availableNames avails

-- | Returns all the available (i.e. exported) 'TyCon's (type constructors) for the input 'Module'.
availableTyCons :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> [AvailInfo] -> m [Ghc.TyCon]
availableTyCons hscEnv modSum tcGblEnv avails =
  fmap (\things -> [tyCon | (ATyCon tyCon) <- things]) (availableTyThings hscEnv modSum tcGblEnv avails)

-- | Returns all the available (i.e. exported) 'Var's for the input 'Module'.
availableVars :: GhcMonadLike m => HscEnv -> ModSummary -> TcGblEnv -> [AvailInfo] -> m [Ghc.Var]
availableVars hscEnv modSum tcGblEnv avails =
  fmap (\things -> [var | (AnId var) <- things]) (availableTyThings hscEnv modSum tcGblEnv avails)

-- | TyThings of modules in external packages
getTyThingsFromExternalModules :: GhcMonadLike m => [Module] -> m [TyThing]
getTyThingsFromExternalModules mods = do
    hscEnv <- askHscEnv
    eps <- liftIO $ readIORef $ hsc_EPS hscEnv
    let names = availableNames $ concatMap mi_exports $ mapMaybe (lookupModuleEnv $ eps_PIT eps) mods
    fmap catMaybes $ liftIO $ mapM (Ghc.hscTcRcLookupName hscEnv) names

availableNames :: [AvailInfo] -> [Name]
availableNames =
    concatMap $ \case
      Avail n -> [Ghc.greNameMangledName n]
      AvailTC n ns -> n : map Ghc.greNameMangledName ns

-- lookupTyThings :: HscEnv -> TypecheckedModule -> MGIModGuts -> Ghc [(Name, Maybe TyThing)]
-- lookupTyThings hscEnv tcm mg =
--   forM (mgNames mg ++ instNames mg) $ \n -> do
--     tt1 <-          lookupName                   n
--     tt2 <- liftIO $ Ghc.hscTcRcLookupName hscEnv n
--     tt3 <-          modInfoLookupName mi         n
--     tt4 <-          lookupGlobalName             n
--     return (n, Misc.firstMaybes [tt1, tt2, tt3, tt4])
--     where
--       mi = tm_checked_module_info tcm


-- lookupName        :: GhcMonad m => Name -> m (Maybe TyThing)
-- hscTcRcLookupName :: HscEnv -> Name -> IO (Maybe TyThing)
-- modInfoLookupName :: GhcMonad m => ModuleInfo -> Name -> m (Maybe TyThing)
-- lookupGlobalName  :: GhcMonad m => Name -> m (Maybe TyThing)

_dumpTypeEnv :: TypecheckedModule -> IO ()
_dumpTypeEnv tm = do
  print ("DUMP-TYPE-ENV" :: String)
  print (showpp <$> tcmTyThings tm)

tcmTyThings :: TypecheckedModule -> Maybe [Name]
tcmTyThings
  =
  -- typeEnvElts
  -- . tcg_type_env . fst
  -- . md_types . snd
  -- . tm_internals_
  modInfoTopLevelScope
  . tm_checked_module_info


_dumpRdrEnv :: HscEnv -> MGIModGuts -> IO ()
_dumpRdrEnv _hscEnv modGuts = do
  print ("DUMP-RDR-ENV" :: String)
  print (mgNames modGuts)
  -- print (hscNames hscEnv)
  -- print (mgDeps modGuts)
  where
    _mgDeps   = Ghc.dep_mods . mgi_deps
    _hscNames = fmap showPpr . Ghc.ic_tythings . Ghc.hsc_IC

mgNames :: MGIModGuts -> [Ghc.Name]
mgNames  = fmap Ghc.greMangledName . Ghc.globalRdrEnvElts .  mgi_rdr_env

modSummaryHsFile :: ModSummary -> FilePath
modSummaryHsFile modSummary =
  fromMaybe
    (panic Nothing $
      "modSummaryHsFile: missing .hs file for " ++
      showPpr (ms_mod modSummary))
    (ml_hs_file $ ms_location modSummary)

checkFilePragmas :: GhcMonadLike m => [Located String] -> m ()
checkFilePragmas = Misc.applyNonNull (return ()) throw . mapMaybe err
  where
    err pragma
      | check (val pragma) = Just (ErrFilePragma $ fSrcSpan pragma :: Error)
      | otherwise          = Nothing
    check pragma           = any (`isPrefixOf` pragma) bad
    bad =
      [ "-i", "--idirs"
      , "-g", "--ghc-option"
      , "--c-files", "--cfiles"
      ]

--------------------------------------------------------------------------------
-- | Family instance information
--------------------------------------------------------------------------------
makeFamInstEnv :: [FamInst] -> ([Ghc.TyCon], [(Symbol, DataCon)])
makeFamInstEnv famInsts =
  let fiTcs = [ tc            | FamInst { fi_flavor = DataFamilyInst tc } <- famInsts ]
      fiDcs = [ (symbol d, d) | tc <- fiTcs, d <- tyConDataCons tc ]
  in (fiTcs, fiDcs)

getFamInstances :: HscEnv -> IO [FamInst]
getFamInstances env = do
  (_, Just (pkg_fie, home_fie)) <- runTcInteractive env tcGetFamInstEnvs
  return $ famInstEnvElts home_fie ++ famInstEnvElts pkg_fie

--------------------------------------------------------------------------------
-- | Extract Specifications from GHC -------------------------------------------
--------------------------------------------------------------------------------
extractSpecComments :: ParsedModule -> [(SourcePos, String)]
extractSpecComments = mapMaybe extractSpecComment . GhcMonadLike.apiComments

-- | 'extractSpecComment' pulls out the specification part from a full comment
--   string, i.e. if the string is of the form:
--   1. '{-@ S @-}' then it returns the substring 'S',
--   2. '{-@ ... -}' then it throws a malformed SPECIFICATION ERROR, and
--   3. Otherwise it is just treated as a plain comment so we return Nothing.

extractSpecComment :: Ghc.Located GhcMonadLike.ApiComment -> Maybe (SourcePos, String)
extractSpecComment (Ghc.L sp (GhcMonadLike.ApiBlockComment txt))
  | isPrefixOf "{-@" txt && isSuffixOf "@-}" txt          -- valid   specification
  = Just (offsetPos, take (length txt - 6) $ drop 3 txt)
  | isPrefixOf "{-@" txt                                   -- invalid specification
  = uError $ ErrParseAnn sp "A valid specification must have a closing '@-}'."
  where
    offsetPos = case srcSpanSourcePos sp of
      SourcePos file line col -> safeSourcePos file (unPos line) (unPos col + 3)
extractSpecComment _ = Nothing

extractSpecQuotes' :: (a -> Module) -> (a -> [Annotation]) -> a -> [BPspec]
extractSpecQuotes' thisModule getAnns a = mapMaybe extractSpecQuote anns
  where
    anns = map ann_value $
           filter (isOurModTarget . ann_target) $
           getAnns a

    isOurModTarget (ModuleTarget mod1) = mod1 == thisModule a
    isOurModTarget _ = False

extractSpecQuote :: AnnPayload -> Maybe BPspec
extractSpecQuote payload =
  case Ghc.fromSerialized Ghc.deserializeWithData payload of
    Nothing -> Nothing
    Just qt -> Just $ refreshSymbols $ liquidQuoteSpec qt

refreshSymbols :: Data a => a -> a
refreshSymbols = everywhere (mkT refreshSymbol)

refreshSymbol :: Symbol -> Symbol
refreshSymbol = symbol . symbolText

--------------------------------------------------------------------------------
-- | Finding & Parsing Files ---------------------------------------------------
--------------------------------------------------------------------------------

-- | Parse a spec file by path.
--
-- On a parse error, we fail.
--
-- TODO, Andres: It would be better to fail more systematically, but currently we
-- seem to have an option between throwing an error which will be reported badly,
-- or printing the error ourselves.
--
parseSpecFile :: FilePath -> IO (ModName, Ms.BareSpec)
parseSpecFile file = do
  contents <- Misc.sayReadFile file
  case specSpecificationP file contents of
    Left peb -> do
      hPutStrLn stderr (errorBundlePretty peb)
      panic Nothing "parsing spec file failed"
    Right x  -> pure x

--------------------------------------------------------------------------------
-- Assemble Information for Spec Extraction ------------------------------------
--------------------------------------------------------------------------------

makeMGIModGuts :: ModGuts -> MGIModGuts
makeMGIModGuts modGuts = miModGuts deriv modGuts
  where
    deriv   = Just $ instEnvElts $ mg_inst_env modGuts

makeLogicMap :: IO LogicMap
makeLogicMap = do
  lg    <- Misc.getCoreToLogicPath
  lspec <- Misc.sayReadFile lg
  case parseSymbolToLogic lg lspec of
    Left peb -> do
      hPutStrLn stderr (errorBundlePretty peb)
      panic Nothing "makeLogicMap failed"
    Right lm -> return (lm <> listLMap)

listLMap :: LogicMap -- TODO-REBARE: move to wiredIn
listLMap  = toLogicMap [ (dummyLoc nilName , []     , hNil)
                       , (dummyLoc consName, [x, xs], hCons (EVar <$> [x, xs])) ]
  where
    x     = "x"
    xs    = "xs"
    hNil  = mkEApp (dcSym Ghc.nilDataCon ) []
    hCons = mkEApp (dcSym Ghc.consDataCon)
    dcSym = dummyLoc . dropModuleUnique . symbol



--------------------------------------------------------------------------------
-- | Pretty Printing -----------------------------------------------------------
--------------------------------------------------------------------------------

instance PPrint TargetSpec where
  pprintTidy k spec = vcat
    [ "******* Target Variables ********************"
    , pprintTidy k $ gsTgtVars (gsVars spec)
    , "******* Type Signatures *********************"
    , pprintLongList k (gsTySigs (gsSig spec))
    , "******* Assumed Type Signatures *************"
    , pprintLongList k (gsAsmSigs (gsSig spec))
    , "******* DataCon Specifications (Measure) ****"
    , pprintLongList k (gsCtors (gsData spec))
    , "******* Measure Specifications **************"
    , pprintLongList k (gsMeas (gsData spec))       ]

instance PPrint TargetInfo where
  pprintTidy k info = vcat
    [ -- "*************** Imports *********************"
      -- , intersperse comma $ text <$> imports info
      -- , "*************** Includes ********************"
      -- , intersperse comma $ text <$> includes info
      "*************** Imported Variables **********"
    , pprDoc $ _giImpVars (review targetSrcIso $ giSrc info)
    , "*************** Defined Variables ***********"
    , pprDoc $ _giDefVars (review targetSrcIso $ giSrc info)
    , "*************** Specification ***************"
    , pprintTidy k $ giSpec info
    , "*************** Core Bindings ***************"
    , pprintCBs $ _giCbs (review targetSrcIso $ giSrc info) ]

pprintCBs :: [CoreBind] -> Doc
pprintCBs = pprDoc . tidyCBs
    -- To print verbosely
    --    = text . O.showSDocDebug unsafeGlobalDynFlags . O.ppr . tidyCBs

instance Show TargetInfo where
  show = showpp

instance PPrint TargetVars where
  pprintTidy _ AllVars   = text "All Variables"
  pprintTidy k (Only vs) = text "Only Variables: " <+> pprintTidy k vs

------------------------------------------------------------------------
-- Dealing with Errors ---------------------------------------------------
------------------------------------------------------------------------

instance Result SourceError where
  result e = Crash ((, Nothing) <$> sourceErrors "" e) "Invalid Source"
