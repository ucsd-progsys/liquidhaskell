{-| This module re-exports a bunch of the GHC API.

The intended use of this module is to shelter LiquidHaskell from changes to the GHC API, so this is the
/only/ module LiquidHaskell should import when trying to access any ghc-specific functionality.

--}

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
  , module StableModule
  ) where

import           Liquid.GHC.API.StableModule      as StableModule
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
import GHC.Driver.Env                 as Ghc
import GHC.Driver.Ppr                 as Ghc
import GHC.HsToCore.Expr              as Ghc
import GHC.Iface.Load                 as Ghc
import GHC.Rename.Expr                as Ghc (rnLExpr)
import GHC.Runtime.Context            as Ghc
import GHC.Tc.Gen.App                 as Ghc (tcInferSigma)
import GHC.Tc.Gen.Bind                as Ghc (tcValBinds)
import GHC.Tc.Gen.Expr                as Ghc (tcInferRho)
import GHC.Tc.Instance.Family         as Ghc
import GHC.Tc.Module                  as Ghc
import GHC.Tc.Solver                  as Ghc
import GHC.Tc.Types                   as Ghc
import GHC.Tc.Types.Evidence          as Ghc
import GHC.Tc.Types.Origin            as Ghc (lexprCtOrigin)
import GHC.Tc.Utils.Monad             as Ghc hiding (getGHCiMonad)
import GHC.Tc.Utils.TcType            as Ghc (tcSplitDFunTy, tcSplitMethodTy)
import GHC.Tc.Utils.Zonk              as Ghc
import GHC.Types.Annotations          as Ghc
import GHC.Types.Avail                as Ghc
import GHC.Types.Basic                as Ghc
import GHC.Types.CostCentre           as Ghc
import GHC.Types.Error                as Ghc
import GHC.Types.Fixity               as Ghc
import GHC.Types.Id                   as Ghc hiding (lazySetIdInfo, setIdExported, setIdNotExported)
import GHC.Types.Id.Info              as Ghc
import GHC.Types.Literal              as Ghc
import GHC.Types.Name                 as Ghc hiding (varName, isWiredIn)
import GHC.Types.Name.Reader          as Ghc
import GHC.Types.Name.Set             as Ghc
import GHC.Types.SourceError          as Ghc
import GHC.Types.SourceText           as Ghc
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.Tickish              as Ghc (CoreTickish, GenTickish(..))
import GHC.Types.TypeEnv              as Ghc
import GHC.Types.Unique               as Ghc
import GHC.Types.Unique.DFM           as Ghc
import GHC.Types.Unique.FM            as Ghc
import GHC.Types.Unique.Set           as Ghc (mkUniqSet)
import GHC.Types.Unique.Supply        as Ghc
import GHC.Types.Var                  as Ghc
import GHC.Types.Var.Env              as Ghc
import GHC.Types.Var.Set              as Ghc
import GHC.Unit.External              as Ghc
import GHC.Unit.Finder                as Ghc
import GHC.Unit.Home.ModInfo          as Ghc
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
