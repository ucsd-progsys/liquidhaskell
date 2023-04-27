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
  , tyConRealArity
  , dataConExTyVars
  , fsToUnitId
  , moduleUnitId
  , thisPackage
  , renderWithStyle
  , pattern LitNumber
  , dataConSig
  , getDependenciesModuleNames
  , gcatch
  ) where

import           Liquid.GHC.API.StableModule      as StableModule
import           GHC                                               as Ghc hiding ( Warning
                                                                                 , SrcSpan(RealSrcSpan, UnhelpfulSpan)
                                                                                 , exprType
                                                                                 )

import Optics
import qualified Control.Monad.Catch as Ex

import Data.Foldable                  (asum)
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
import GHC.Types.Literal              as Ghc hiding (LitNumber)
import qualified GHC.Types.Literal    as Ghc
import GHC.Types.Name                 as Ghc hiding (varName, isWiredIn)
import GHC.Types.Name.Reader          as Ghc
import GHC.Types.Name.Set             as Ghc
import GHC.Types.SourceError          as Ghc
import GHC.Types.SourceText           as Ghc
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.Tickish              as Ghc
import GHC.Types.TypeEnv              as Ghc
import GHC.Types.Unique               as Ghc
import GHC.Types.Unique.DFM           as Ghc
import GHC.Types.Unique.FM            as Ghc
import GHC.Types.Unique.Set           as Ghc
import GHC.Types.Unique.Supply        as Ghc
import GHC.Types.Var                  as Ghc
import GHC.Types.Var.Env              as Ghc
import GHC.Types.Var.Set              as Ghc
import GHC.Unit.External              as Ghc
import GHC.Unit.Finder                as Ghc
import GHC.Unit.Home.ModInfo          as Ghc
import GHC.Unit.Module                as Ghc
import GHC.Unit.Module.Deps           as Ghc
import GHC.Unit.Module.Graph          as Ghc
import GHC.Unit.Module.ModDetails     as Ghc
import GHC.Unit.Module.ModGuts        as Ghc
import GHC.Unit.Module.ModSummary     as Ghc
import GHC.Utils.Error                as Ghc
import GHC.Utils.Logger               as Ghc
import GHC.Utils.Misc                 as Ghc (zipEqual)
import GHC.Utils.Outputable           as Ghc (mkUserStyle)
import GHC.Utils.Outputable           as Ghc hiding ((<>), integer, mkUserStyle)
import GHC.Utils.Panic                as Ghc

-- 'fsToUnitId' is gone in GHC 9, but we can bring code it in terms of 'fsToUnit' and 'toUnitId'.
fsToUnitId :: FastString -> UnitId
fsToUnitId = toUnitId . fsToUnit

moduleUnitId :: Module -> UnitId
moduleUnitId = toUnitId . moduleUnit

thisPackage :: DynFlags -> UnitId
thisPackage = homeUnitId_

-- See NOTE [tyConRealArity].
tyConRealArity :: TyCon -> Int
tyConRealArity tc = go 0 (tyConKind tc)
  where
    go :: Int -> Kind -> Int
    go !acc k =
      case asum [fmap (view _3) (splitFunTy_maybe k), fmap snd (splitForAllTyCoVar_maybe k)] of
        Nothing -> acc
        Just ks -> go (acc + 1) ks

dataConExTyVars :: DataCon -> [TyVar]
dataConExTyVars = dataConExTyCoVars

getDependenciesModuleNames :: Dependencies -> [ModuleNameWithIsBoot]
getDependenciesModuleNames = dep_mods

renderWithStyle :: DynFlags -> SDoc -> PprStyle -> String
renderWithStyle dynflags sdoc style = Ghc.renderWithContext (Ghc.initSDocContext dynflags style) sdoc

--
-- Literal
--

-- In GHC 9 'LitNumber' doesn't have the extra 3rd argument, so we simply ignore it in the construction.

pattern LitNumber :: Ghc.LitNumType -> Integer -> Ghc.Type -> Ghc.Literal
pattern LitNumber numType integer ty <- ((intPrimTy,) -> (ty, Ghc.LitNumber numType integer))
  where
    LitNumber numType integer _ = Ghc.LitNumber numType integer

-- This function is gone in GHC 9.
dataConSig :: DataCon -> ([TyCoVar], ThetaType, [Type], Type)
dataConSig dc
  = (dataConUnivAndExTyCoVars dc, dataConTheta dc, map irrelevantMult $ dataConOrigArgTys dc, dataConOrigResTy dc)

gcatch :: (Ex.MonadCatch m, Exception e) => m a -> (e -> m a) -> m a
gcatch = Ex.catch
