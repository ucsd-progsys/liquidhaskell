{-| This module re-exports all identifiers that LH needs
    from the GHC API.

The intended use of this module is to provide a quick look of what
GHC API features LH depends upon.

The transitive dependencies of this module shouldn't contain modules
from Language.Haskell.Liquid.* or other non-boot libraries. This makes
it easy to discover breaking changes in the GHC API.

-}

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}

module Liquid.GHC.API (
    module Ghc
  ) where

import Liquid.GHC.API.Extra as Ghc

import           GHC                                               as Ghc hiding ( Warning
                                                                                 , SrcSpan(RealSrcSpan, UnhelpfulSpan)
                                                                                 , exprType
                                                                                 )

import GHC.Builtin.Names              as Ghc
import GHC.Builtin.Types              as Ghc
import GHC.Builtin.Types.Prim         as Ghc
import GHC.Builtin.Utils              as Ghc
import GHC.Core                       as Ghc hiding (AnnExpr, AnnExpr' (..), AnnRec, AnnCase)
import GHC.Core.Class                 as Ghc hiding (FunDep)
import GHC.Core.Coercion              as Ghc
import GHC.Core.Coercion.Axiom        as Ghc
import GHC.Core.ConLike               as Ghc
import GHC.Core.DataCon               as Ghc
import GHC.Core.FamInstEnv            as Ghc hiding (pprFamInst)
import GHC.Core.InstEnv               as Ghc
import GHC.Core.Lint                  as Ghc hiding (dumpIfSet)
import GHC.Core.Make                  as Ghc
import GHC.Core.Opt.Monad             as Ghc (CoreToDo(..))
import GHC.Core.Opt.WorkWrap.Utils    as Ghc
import GHC.Core.Predicate             as Ghc (getClassPredTys_maybe, getClassPredTys, isEvVarType, isEqPrimPred, isEqPred, isClassPred, isDictId, mkClassPred)
import GHC.Core.Subst                 as Ghc (deShadowBinds, emptySubst, extendCvSubst)
import GHC.Core.TyCo.Rep              as Ghc
import GHC.Core.TyCon                 as Ghc
import GHC.Core.Type                  as Ghc hiding (typeKind , isPredTy, extendCvSubst, linear)
import GHC.Core.Unify                 as Ghc
import GHC.Core.Utils                 as Ghc (exprType)
import GHC.Data.Bag                   as Ghc
import GHC.Data.FastString            as Ghc
import GHC.Data.Graph.Directed        as Ghc
import GHC.Data.Pair                  as Ghc
import GHC.Driver.Main                as Ghc
import GHC.Driver.Phases              as Ghc (Phase(StopLn))
import GHC.Driver.Pipeline            as Ghc (compileFile)
import GHC.Driver.Session             as Ghc
import GHC.Driver.Monad               as Ghc (withSession)
import GHC.HsToCore.Monad             as Ghc
import GHC.Iface.Syntax               as Ghc
import GHC.Plugins                    as Ghc ( deserializeWithData
                                             , fromSerialized
                                             , toSerialized
                                             , defaultPlugin
                                             , Plugin(..)
                                             , CommandLineOption
                                             , purePlugin
                                             , extendIdSubst
                                             , substExpr
                                             )
import GHC.Core.FVs                   as Ghc (exprFreeVarsList)
import GHC.Core.Opt.OccurAnal         as Ghc
    ( occurAnalysePgm )
import GHC.Driver.Env                 as Ghc
    ( HscEnv(hsc_EPS, hsc_HPT, hsc_dflags, hsc_plugins, hsc_static_plugins) )
import GHC.Driver.Ppr                 as Ghc
    ( showPpr
    , showSDoc
    , showSDocDump
    )
import GHC.HsToCore.Expr              as Ghc
    ( dsLExpr )
import GHC.Iface.Load                 as Ghc
    ( cannotFindModule
    , loadInterface
    )
import GHC.Rename.Expr                as Ghc (rnLExpr)
import GHC.Tc.Gen.App                 as Ghc (tcInferSigma)
import GHC.Tc.Gen.Bind                as Ghc (tcValBinds)
import GHC.Tc.Gen.Expr                as Ghc (tcInferRho)
import GHC.Tc.Module                  as Ghc
    ( getModuleInterface
    , tcRnLookupRdrName
    )
import GHC.Tc.Solver                  as Ghc
    ( InferMode(NoRestrictions)
    , captureTopConstraints
    , simplifyInfer
    , simplifyInteractive
    )
import GHC.Tc.Types                   as Ghc
    ( Env(env_top)
    , TcGblEnv(tcg_anns, tcg_exports, tcg_insts, tcg_mod, tcg_rdr_env, tcg_rn_imports)
    , TcM
    , TcRn
    , WhereFrom(ImportBySystem)
    )
import GHC.Tc.Types.Evidence          as Ghc
    ( TcEvBinds(EvBinds) )
import GHC.Tc.Types.Origin            as Ghc (lexprCtOrigin)
import GHC.Tc.Utils.Monad             as Ghc
    ( captureConstraints
    , discardConstraints
    , getEnv
    , failIfErrsM
    , failM
    , failWithTc
    , initIfaceTcRn
    , liftIO
    , mkLongErrAt
    , pushTcLevelM
    , reportError
    , reportErrors
    )
import GHC.Tc.Utils.TcType            as Ghc (tcSplitDFunTy, tcSplitMethodTy)
import GHC.Tc.Utils.Zonk              as Ghc
    ( zonkTopLExpr )
import GHC.Types.Annotations          as Ghc
    ( AnnPayload
    , AnnTarget(ModuleTarget)
    , Annotation(Annotation, ann_target, ann_value)
    , findAnns
    )
import GHC.Types.Avail                as Ghc
    ( AvailInfo(Avail, AvailTC)
    , availNames
    , greNameMangledName
    )
import GHC.Types.Basic                as Ghc
    ( Arity
    , Boxity(Boxed)
    , PprPrec
    , PromotionFlag(NotPromoted)
    , TopLevelFlag(NotTopLevel)
    , funPrec
    , InlinePragma(inl_act, inl_inline, inl_rule, inl_sat, inl_src)
    , isDeadOcc
    , isStrongLoopBreaker
    , noOccInfo
    , topPrec
    )
import GHC.Types.CostCentre           as Ghc
    ( CostCentre(cc_loc)
    )
import GHC.Types.Error                as Ghc
    ( Messages
    , DecoratedSDoc
    , MsgEnvelope(errMsgSpan)
    )
import GHC.Types.Fixity               as Ghc
    ( Fixity(Fixity) )
import GHC.Types.Id                   as Ghc
    ( idDetails
    , isDFunId
    , idInfo
    , idOccInfo
    , isConLikeId
    , modifyIdInfo
    , mkExportedLocalId
    , mkUserLocal
    , realIdUnfolding
    , setIdInfo
    )
import GHC.Types.Id.Info              as Ghc
    ( CafInfo(NoCafRefs)
    , IdDetails(DataConWorkId, DataConWrapId, RecSelId, VanillaId)
    , IdInfo(occInfo, unfoldingInfo)
    , cafInfo
    , inlinePragInfo
    , mayHaveCafRefs
    , setCafInfo
    , setOccInfo
    , vanillaIdInfo
    )
import GHC.Types.Literal              as Ghc
    ( LitNumType(LitNumInt)
    , Literal(LitChar, LitDouble, LitFloat, LitNumber, LitString)
    , literalType
    )
import GHC.Types.Name                 as Ghc
    ( OccName
    , getOccString
    , getSrcSpan
    , isInternalName
    , isSystemName
    , mkInternalName
    , mkSystemName
    , mkTcOcc
    , mkTyVarOcc
    , mkVarOcc
    , mkVarOccFS
    , nameModule_maybe
    , nameOccName
    , nameSrcLoc
    , nameStableString
    , occNameFS
    , occNameString
    , stableNameCmp
    )
import GHC.Types.Name.Reader          as Ghc
    ( ImpDeclSpec(ImpDeclSpec, is_as, is_dloc, is_mod, is_qual)
    , ImportSpec(ImpSpec)
    , ImpItemSpec(ImpAll)
    , getRdrName
    , globalRdrEnvElts
    , gresFromAvails
    , greMangledName
    , lookupGRE_RdrName
    , mkGlobalRdrEnv
    , mkQual
    , mkVarUnqual
    , mkUnqual
    , nameRdrName
    )
import GHC.Types.SourceError          as Ghc
    ( SourceError
    , srcErrorMessages
    )
import GHC.Types.SourceText           as Ghc
    ( SourceText(SourceText,NoSourceText)
    , mkIntegralLit
    , mkTHFractionalLit
    )
import GHC.Types.SrcLoc               as Ghc
    ( SrcSpan(RealSrcSpan, UnhelpfulSpan)
    , UnhelpfulSpanReason
        ( UnhelpfulGenerated
        , UnhelpfulInteractive
        , UnhelpfulNoLocationInfo
        , UnhelpfulOther
        , UnhelpfulWiredIn
        )
    , combineSrcSpans
    , mkGeneralSrcSpan
    , mkRealSrcLoc
    , mkRealSrcSpan
    , realSrcSpanStart
    , srcSpanFileName_maybe
    , srcSpanToRealSrcSpan
    )
import GHC.Types.Tickish              as Ghc (CoreTickish, GenTickish(..))
import GHC.Types.Unique               as Ghc
    ( getKey, mkUnique )
import GHC.Types.Unique.Set           as Ghc (mkUniqSet)
import GHC.Types.Unique.Supply        as Ghc
    ( MonadUnique, getUniqueM )
import GHC.Types.Var                  as Ghc
    ( VarBndr(Bndr)
    , mkLocalVar
    , mkTyVar
    , setVarName
    , setVarType
    , setVarUnique
    , varName
    , varUnique
    )
import GHC.Types.Var.Env              as Ghc
    ( emptyInScopeSet, mkRnEnv2 )
import GHC.Types.Var.Set              as Ghc
    ( VarSet
    , elemVarSet
    , emptyVarSet
    , extendVarSet
    , extendVarSetList
    , unitVarSet
    )
import GHC.Unit.External              as Ghc
    ( ExternalPackageState (eps_ann_env)
    )
import GHC.Unit.Finder                as Ghc
    ( FindResult(Found, NoPackage, FoundMultiple, NotFound)
    , findExposedPackageModule
    , findImportedModule
    )
import GHC.Unit.Home.ModInfo          as Ghc
    ( HomePackageTable, HomeModInfo(hm_iface), lookupHpt )
import GHC.Unit.Module                as Ghc
    ( GenWithIsBoot(gwib_isBoot, gwib_mod)
    , IsBootInterface(NotBoot, IsBoot)
    , ModuleNameWithIsBoot
    , UnitId
    , fsToUnit
    , mkModuleNameFS
    , moduleNameFS
    , moduleStableString
    , toUnitId
    , unitString
    )
import GHC.Unit.Module.ModGuts        as Ghc
    ( ModGuts
      ( mg_binds
      , mg_exports
      , mg_fam_inst_env
      , mg_inst_env
      , mg_module
      , mg_tcs
      , mg_usages
      )
    )
import GHC.Utils.Error                as Ghc (withTiming)
import GHC.Utils.Logger               as Ghc (putLogMsg)
import GHC.Utils.Outputable           as Ghc hiding ((<>))
import GHC.Utils.Panic                as Ghc (panic, throwGhcException, throwGhcExceptionIO)
