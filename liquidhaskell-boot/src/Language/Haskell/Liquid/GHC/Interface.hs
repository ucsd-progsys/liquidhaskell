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
{-# OPTIONS_GHC -Wno-x-partial #-}

module Language.Haskell.Liquid.GHC.Interface (

  -- * Printer
    pprintCBs

  -- * predicates
  -- , isExportedVar
  -- , exportedVars

  -- * Internal exports (provisional)
  , extractSpecComments
  , listLMap
  , classCons
  , derivedVars
  , importVars
  , modSummaryHsFile
  , makeFamInstEnv
  , clearSpec
  , checkFilePragmas
  , lookupTyThing
  , updLiftedSpec
  ) where

import Prelude hiding (error)

import           Liquid.GHC.API as Ghc hiding ( text
                                                               , (<+>)
                                                               , panic
                                                               , vcat
                                                               , showPpr
                                                               , mkStableModule
                                                               , Located
                                                               )
import qualified Liquid.GHC.API as Ghc

import Control.Exception
import Control.Monad
import Control.Monad.Trans.Maybe

import Data.List hiding (intersperse)
import Data.Maybe

import qualified Data.HashSet        as S

import Text.PrettyPrint.HughesPJ        hiding (first, (<>))
import Language.Fixpoint.Types          hiding (err, panic, Error, Result, Expr)
import qualified Language.Fixpoint.Misc as Misc
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.GHC.Types (MGIModGuts(..))
import Language.Haskell.Liquid.GHC.Play
import Language.Haskell.Liquid.WiredIn (isDerivedInstance)
import qualified Language.Haskell.Liquid.Measure  as Ms
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.PrettyPrint
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types
import Language.Haskell.Liquid.Types.Visitors
import Language.Haskell.Liquid.UX.Config
import Language.Haskell.Liquid.UX.Tidy


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
    unfolds        = realUnfoldingInfo . idInfo <$> concatMap bindersOf cbs'

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

lookupTyThing :: (GhcMonad m) => Ghc.TypeEnv -> Name -> m (Maybe TyThing)
lookupTyThing tyEnv name = do
    runMaybeT . msum . map MaybeT $
        [ pure (lookupTypeEnv tyEnv name)
        , lookupName name
        ]

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

modSummaryHsFile :: ModSummary -> FilePath
modSummaryHsFile modSummary =
  fromMaybe
    (panic Nothing $
      "modSummaryHsFile: missing .hs file for " ++
      showPpr (ms_mod modSummary))
    (ml_hs_file $ ms_location modSummary)

checkFilePragmas :: [Located String] -> IO ()
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

--------------------------------------------------------------------------------
-- | Extract Specifications from GHC -------------------------------------------
--------------------------------------------------------------------------------
extractSpecComments :: HsParsedModule -> [(Maybe RealSrcLoc, String)]
extractSpecComments = mapMaybe extractSpecComment . apiComments

-- | 'extractSpecComment' pulls out the specification part from a full comment
--   string, i.e. if the string is of the form:
--   1. '{-@ S @-}' then it returns the substring 'S',
--   2. '{-@ ... -}' then it throws a malformed SPECIFICATION ERROR, and
--   3. Otherwise it is just treated as a plain comment so we return Nothing.

extractSpecComment :: Ghc.Located ApiComment -> Maybe (Maybe RealSrcLoc, String)
extractSpecComment (Ghc.L sp (ApiBlockComment txt))
  | isPrefixOf "{-@" txt && isSuffixOf "@-}" txt          -- valid   specification
  = Just (offsetPos, take (length txt - 6) $ drop 3 txt)
  | isPrefixOf "{-@" txt                                   -- invalid specification
  = uError $ ErrParseAnn sp "A valid specification must have a closing '@-}'."
  where
    offsetPos = offsetRealSrcLoc . realSrcSpanStart <$> srcSpanToRealSrcSpan sp
    offsetRealSrcLoc s =
      mkRealSrcLoc (srcLocFile s) (srcLocLine s) (srcLocCol s + 3)

extractSpecComment _ = Nothing

--------------------------------------------------------------------------------
-- Information for Spec Extraction ---------------------------------------------
--------------------------------------------------------------------------------

listLMap :: LogicMap -- TODO-REBARE: move to wiredIn
listLMap  = toLogicMap [ (dummyLoc nilName , ([]     , hNil))
                       , (dummyLoc consName, ([x, xs], hCons (EVar <$> [x, xs]))) ]
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
    , pprDoc $ _giImpVars (fromTargetSrc $ giSrc info)
    , "*************** Defined Variables ***********"
    , pprDoc $ _giDefVars (fromTargetSrc $ giSrc info)
    , "*************** Specification ***************"
    , pprintTidy k $ giSpec info
    , "*************** Core Bindings ***************"
    , pprintCBs $ _giCbs (fromTargetSrc $ giSrc info) ]

pprintCBs :: [CoreBind] -> Doc
pprintCBs = pprDoc . tidyCBs
    -- To print verbosely
    --    = text . O.showSDocDebug unsafeGlobalDynFlags . O.ppr . tidyCBs

instance Show TargetInfo where
  show = showpp

------------------------------------------------------------------------
-- Dealing with Errors ---------------------------------------------------
------------------------------------------------------------------------

instance Result SourceError where
  result e = Crash ((, Nothing) <$> sourceErrors "" e) "Invalid Source"
