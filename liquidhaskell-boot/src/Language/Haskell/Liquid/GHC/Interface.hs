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
  , manualInstSpans
  , importVars
  , modSummaryHsFile
  , makeFamInstEnv
  , clearSpec
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

import Control.Monad
import Control.Monad.Trans.Maybe

import Data.List hiding (intersperse)
import Data.Maybe

import qualified Data.HashSet        as S

import Text.PrettyPrint.HughesPJ        hiding (first, (<>))
import Language.Fixpoint.Types          hiding (err, panic, Error, Result, Expr)
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.GHC.Types (MGIModGuts(..))
import Language.Haskell.Liquid.GHC.Play
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

derivedVars :: Config -> S.HashSet Ghc.SrcSpan -> MGIModGuts -> [Var]
derivedVars cfg manualSpans mg = concatMap (dFunIdVars cbs . is_dfun) derInsts
  where
    derInsts
      | checkDer  = insts
      | otherwise = filter (not . isManual manualSpans) insts
    insts         = mgClsInstances mg
    checkDer      = checkDerived cfg
    cbs           = mgi_binds mg

-- | Returns True if the instance DFun's source span falls within one of the
-- manually-written instance declaration spans.  Instances not in any such span
-- (e.g. derived via 'deriving') are treated as auto-generated.
isManual :: S.HashSet Ghc.SrcSpan -> ClsInst -> Bool
isManual manualSpans inst =
  any (Ghc.getSrcSpan (is_dfun inst) `Ghc.isSubspanOf`) (S.toList manualSpans)

-- | Collect the source spans of all 'ClsInstDecl' nodes in the renamed AST.
-- These cover the full body of every manually-written instance declaration.
manualInstSpans :: Ghc.TcGblEnv -> S.HashSet Ghc.SrcSpan
manualInstSpans tcg = case Ghc.tcg_rn_decls tcg of
  Nothing  -> S.empty
  Just grp -> S.fromList
    [ Ghc.getLocA d
    | d <- Ghc.hsGroupInstDecls grp
    , Ghc.ClsInstD {} <- [Ghc.unLoc d]
    ]


mgClsInstances :: MGIModGuts -> [ClsInst]
mgClsInstances = fromMaybe [] . mgi_cls_inst

dFunIdVars :: CoreProgram -> DFunId -> [Id]
dFunIdVars cbs fd  = notracepp msg $ go S.empty [fd]
  where
    msg            = "DERIVED-VARS-OF: " ++ showpp fd
    localVars      = S.fromList (concatMap bindersOf cbs)
    -- Compute transitive closure of local dependencies
    go seen []     = S.toList seen
    go seen (x:ws)
      | S.member x seen = go seen ws
      | otherwise       = go seen' (newDeps ++ ws)
      where
        seen'    = S.insert x seen
        newDeps  = filter (`S.member` localVars) (depsOf x)
    -- Get local dependencies of a var: co-binders + free vars in the binding RHS
    depsOf x     = let xBinds = filter (bindsVar x) cbs
                   in concatMap bindersOf xBinds
                      ++ concatMap (freeVars S.empty) xBinds
                      ++ unfoldingDeps x
    bindsVar x (NonRec y _) = varName y == varName x
    bindsVar x (Rec xes)    = any (\(y,_) -> varName y == varName x) xes
    unfoldingDeps x =
      let xBinds' = filter (bindsVar x) cbs
          xBndrs  = concatMap bindersOf xBinds'
      in concatMap (unfoldDep . realUnfoldingInfo . idInfo) xBndrs

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

modSummaryHsFile :: ModSummary -> FilePath
modSummaryHsFile modSummary =
  fromMaybe
    (panic Nothing $
      "modSummaryHsFile: missing .hs file for " ++
      showPpr (ms_mod modSummary))
    (ml_hs_file $ ms_location modSummary)

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
