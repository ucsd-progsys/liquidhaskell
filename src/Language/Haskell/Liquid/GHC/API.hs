{-| This module re-exports a bunch of the GHC API.

The intended use of this module is to shelter LiquidHaskell from changes to the GHC API, so this is the
/only/ module LiquidHaskell should import when trying to access any ghc-specific functionality.

--}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.GHC.API (
    module Ghc
  , module StableModule

-- Specific exports for 8.6.5
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,8,1,0)
  , pattern Bndr
  , pattern LitString
  , pattern LitFloat
  , pattern LitDouble
  , pattern LitChar
  , VarBndr
#endif
#endif

-- Specific exports for 8.6.5 and 8.8.x
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)
  , AnonArgFlag(..)
  , pattern FunTy
  , pattern AnonTCB
  , ft_af, ft_mult, ft_arg, ft_res
  , bytesFS
  , mkFunTy
  , isEvVarType
  , isEqPrimPred
  , noExtField
  , Mult
  , pattern Many
#endif
#endif

  , tyConRealArity
  , dataConExTyVars

-- Specific exports for 8.8.x
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,8,1,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)
  , isEqPred
#endif
#endif

-- Specific exports for 8.10.x
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0) && !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
  , Mult
  , pattern Many
  , pattern FunTy
  , mkFunTy
  , ft_af, ft_mult, ft_arg, ft_res
#endif
#endif

-- Shared exports for GHC < 9
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
  , pattern RealSrcSpan
  , pattern UnhelpfulSpan
  , UnhelpfulSpanReason(..)
  , scaledThing
  , Scaled(..)
  , mkScaled
  , irrelevantMult
  , dataConInstArgTys
  , dataConOrigArgTys
  , dataConRepArgTys
  , mkLocalVar
  , DataConAppContext(..)
  , deepSplitProductType_maybe
  , splitFunTys
  , mkUserLocal
  , dataConWrapperType
  , apiAnnComments
  , getDependenciesModuleNames
  , GenWithIsBoot(..)
  , ModuleNameWithIsBoot
  , IsBootInterface
  , isBootSummary
  , mkIntExprInt
  , dataConFullSig
#endif
#endif

-- Specific exports for 9.x
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
  , fsToUnitId
  , moduleUnitId
  , thisPackage
  , renderWithStyle
  , mkUserStyle
  , pattern LitNumber
  , dataConSig
  , getDependenciesModuleNames
  , gcatch
#endif
#endif

  ) where

import           Language.Haskell.Liquid.GHC.API.StableModule      as StableModule
import           GHC                                               as Ghc hiding ( Warning
                                                                                 , SrcSpan(RealSrcSpan, UnhelpfulSpan)
                                                                                 , exprType
                                                                                 )

-- Shared imports for GHC < 9
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)

import CoreFVs                  as Ghc (exprFreeVarsList)
import OccurAnal                as Ghc (occurAnalysePgm)
import Annotations              as Ghc
import ApiAnnotation            as Ghc
import Avail                    as Ghc
import Bag                      as Ghc
import BasicTypes               as Ghc
import Class                    as Ghc
import CoAxiom                  as Ghc
import Coercion                 as Ghc
import ConLike                  as Ghc
import CoreLint                 as Ghc hiding (dumpIfSet)
import CoreMonad                as Ghc (CoreToDo(..))
import CoreSubst                as Ghc (deShadowBinds, substExpr, emptySubst, extendCvSubst)
import CoreSyn                  as Ghc hiding (AnnExpr, AnnExpr' (..), AnnRec, AnnCase)
import CoreUtils                as Ghc (exprType)
import CostCentre               as Ghc
import Data.Map.Strict (Map)
import DataCon                  as Ghc hiding (dataConInstArgTys, dataConOrigArgTys, dataConRepArgTys, dataConFullSig)
import qualified DataCon        as Ghc
import Digraph                  as Ghc
import DriverPhases             as Ghc (Phase(StopLn))
import DriverPipeline           as Ghc hiding (P, getLocation)
import DsMonad                  as Ghc
import DynFlags                 as Ghc
import ErrUtils                 as Ghc
import FamInst                  as Ghc
import FamInstEnv               as Ghc hiding (pprFamInst)
import Finder                   as Ghc
import ForeignCall              (CType)
import GHC                      as Ghc (SrcSpan)
import GhcMonad                 as Ghc (withSession)
import GhcPlugins               as Ghc (deserializeWithData , fromSerialized , toSerialized, extendIdSubst)
import HscMain                  as Ghc
import HscTypes                 as Ghc hiding (IsBootInterface, isBootSummary)
import Id                       as Ghc hiding (lazySetIdInfo, setIdExported, setIdNotExported, mkUserLocal)
import IdInfo                   as Ghc
import IfaceSyn                 as Ghc
import InstEnv                  as Ghc
import Literal                  as Ghc
import MkCore                   as Ghc hiding (mkIntExprInt)
import MkId                     (mkDataConWorkId)
import Module                   as Ghc
import Name                     as Ghc hiding (varName)
import NameEnv                  (lookupNameEnv_NF)
import NameSet                  as Ghc
import Outputable               as Ghc hiding ((<>))
import Pair                     as Ghc
import Panic                    as Ghc
import Plugins                  as Ghc (defaultPlugin, Plugin(..), CommandLineOption, purePlugin)
import PrelInfo                 as Ghc
import PrelNames                as Ghc hiding (wildCardName)
import RdrName                  as Ghc
import SrcLoc                   as Ghc hiding (RealSrcSpan, SrcSpan(UnhelpfulSpan))
import TcRnDriver               as Ghc
import TcRnMonad                as Ghc hiding (getGHCiMonad)
import TysPrim                  as Ghc
import TysWiredIn               as Ghc
import Unify                    as Ghc
import UniqDFM                  as Ghc
import UniqFM                   as Ghc
import UniqSet                  as Ghc
import UniqSupply               as Ghc
import Unique                   as Ghc
import Var                      as Ghc hiding (mkLocalVar)
import VarEnv                   as Ghc
import VarSet                   as  Ghc
import qualified                SrcLoc
import qualified Data.Bifunctor as Bi
import qualified Data.Data      as Data
import qualified GhcMake
import qualified HscTypes       as Ghc
import qualified Id             as Ghc
import qualified MkCore         as Ghc
import qualified Var            as Ghc
import qualified WwLib          as Ghc
import           RnExpr         as Ghc (rnLExpr)
import           TcExpr         as Ghc (tcInferSigma)
import           TcBinds        as Ghc (tcValBinds)
import           Inst           as Ghc (deeplyInstantiate)
import           TcSimplify     as Ghc ( simplifyInfer, simplifyInteractive
                                       , InferMode (..))
import           TcHsSyn        as Ghc (zonkTopLExpr)
import           TcEvidence     as Ghc ( TcEvBinds (EvBinds))
import           DsExpr         as Ghc (dsLExpr)
#endif
#endif

--
-- Compatibility layer for different GHC versions.
--

--
-- Specific imports for GHC 8.6.5
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,8,1,0)

import qualified Literal as Lit
import FastString        as Ghc hiding (bytesFS, LitString)
import TcType            as Ghc hiding (typeKind, mkFunTy)
import Type              as Ghc hiding (typeKind, mkFunTy, splitFunTys, extendCvSubst)
import qualified Type    as Ghc
import qualified Var     as Var
import qualified GHC.Real
-- import PrelNames      (eqPrimTyConKey, eqReprPrimTyConKey, gHC_REAL, varQual_RDR)
#endif
#endif

--
-- Specific imports for GHC 8.6.5 & 8.8.x
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)

import                   Binary
import                   Data.ByteString (ByteString)
import                   Data.Data (Data)
import Kind              as Ghc
import TyCoRep           as Ghc hiding (Type (FunTy), mkFunTy, extendCvSubst)
import TyCon             as Ghc hiding (mkAnonTyConBinders, TyConBndrVis(AnonTCB))
import qualified TyCoRep as Ty hiding (extendCvSubst)
import qualified TyCon   as Ty
import Platform as Ghc
import qualified HsExtension
-- import PrelNames      (eqPrimTyConKey, eqReprPrimTyConKey, gHC_REAL, varQual_RDR)

#endif
#endif

--
-- Specific imports for 8.8.x
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,8,1,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)

import FastString           as Ghc hiding (bytesFS)
import TcType               as Ghc hiding (typeKind, mkFunTy, isEqPred)
import Type                 as Ghc hiding (typeKind, mkFunTy, isEvVarType, isEqPred, splitFunTys, extendCvSubst)
import qualified Type       as Ghc
import qualified Type       as Ghc (isEvVarType)
import qualified PrelNames  as Ghc
import Data.Foldable        (asum)
-- import PrelNames      (eqPrimTyConKey, eqReprPrimTyConKey, gHC_REAL, varQual_RDR)
#endif
#endif

--
-- Specific imports for GHC 8.10
--
#ifdef MIN_VERSION_GLASGOW_HASKELL

#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0) && !MIN_VERSION_GLASGOW_HASKELL (9,0,0,0)
import GHC.Platform      as  Ghc (Platform)
import Type              as  Ghc hiding (mapType, typeKind, isPredTy, splitFunTys, extendCvSubst)
import qualified Type    as  Ghc hiding (extendCvSubst)
import TyCon             as  Ghc
import qualified TyCoRep as  Ty
import TcType            as  Ghc
import TyCoRep           as  Ghc hiding (Type (FunTy), mkFunTy, ft_arg, ft_res, ft_af)
import FastString        as  Ghc
import Predicate      as Ghc (getClassPredTys_maybe, isEvVarType, getClassPredTys, isDictId)
import TcOrigin       as Ghc (lexprCtOrigin)
import Data.Foldable  (asum)
#endif
#endif

--
-- Specific imports for GHC 9
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0) && !MIN_VERSION_GLASGOW_HASKELL (9,1,0,0)

import Optics
import qualified Control.Monad.Catch as Ex

import Data.Foldable                  (asum)
import GHC.Builtin.Names              as Ghc
import GHC.Builtin.Types              as Ghc
import GHC.Builtin.Types.Prim         as Ghc
import GHC.Builtin.Utils              as Ghc
import GHC.Core                       as Ghc hiding (AnnExpr, AnnExpr' (..), AnnRec, AnnCase)
import GHC.Core.Class                 as Ghc
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
import GHC.Core.Predicate             as Ghc (getClassPredTys_maybe, getClassPredTys, isEvVarType, isEqPrimPred, isEqPred, isClassPred, isDictId)
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
import GHC.Driver.Finder              as Ghc
import GHC.Driver.Main                as Ghc
import GHC.Driver.Phases              as Ghc (Phase(StopLn))
import GHC.Driver.Pipeline            as Ghc (compileFile)
import GHC.Driver.Session             as Ghc hiding (isHomeModule)
import GHC.Driver.Types               as Ghc
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
import GHC.Tc.Instance.Family         as Ghc
import GHC.Tc.Module                  as Ghc
import GHC.Tc.Types                   as Ghc
import GHC.Tc.Utils.Monad             as Ghc hiding (getGHCiMonad)
import GHC.Tc.Utils.TcType            as Ghc (tcSplitDFunTy, tcSplitMethodTy)
import GHC.Types.Annotations          as Ghc
import GHC.Types.Avail                as Ghc
import GHC.Types.Basic                as Ghc
import GHC.Types.CostCentre           as Ghc
import GHC.Types.Id                   as Ghc hiding (lazySetIdInfo, setIdExported, setIdNotExported)
import GHC.Types.Id.Info              as Ghc
import GHC.Types.Literal              as Ghc hiding (LitNumber)
import GHC.Types.Name                 as Ghc hiding (varName, isWiredIn)
import GHC.Types.Name.Reader          as Ghc
import GHC.Types.Name.Set             as Ghc
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.Unique               as Ghc
import GHC.Types.Unique.DFM           as Ghc
import GHC.Types.Unique.FM            as Ghc
import GHC.Types.Unique.Set           as Ghc
import GHC.Types.Unique.Supply        as Ghc
import GHC.Types.Var                  as Ghc
import GHC.Types.Var.Env              as Ghc
import GHC.Types.Var.Set              as Ghc
import GHC.Unit.Module                as Ghc
import GHC.Utils.Error                as Ghc
import GHC.Utils.Outputable           as Ghc hiding ((<>), renderWithStyle, mkUserStyle)
import GHC.Utils.Panic                as Ghc
import qualified GHC.Types.Literal    as Ghc
import qualified GHC.Utils.Outputable as Ghc
import GHC.Tc.Types.Origin            as Ghc (lexprCtOrigin)
import GHC.Rename.Expr                as Ghc (rnLExpr)
import GHC.Tc.Gen.Expr                as Ghc (tcInferSigma, tcInferRho)
import GHC.Tc.Gen.Bind                as Ghc (tcValBinds)
import GHC.Tc.Solver                  as Ghc
import GHC.Tc.Utils.Zonk              as Ghc
import GHC.Core.FVs                   as Ghc (exprFreeVarsList)
import GHC.Tc.Types.Evidence          as Ghc
import GHC.HsToCore.Expr              as Ghc
import GHC.Core.Predicate             as Ghc (mkClassPred)
import GHC.Core.Opt.OccurAnal         as Ghc
#endif
#endif

--
-- Compat shim for GHC < 9 (shared parts)
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)

data BufSpan

pattern RealSrcSpan :: SrcLoc.RealSrcSpan -> Maybe BufSpan -> SrcLoc.SrcSpan
pattern RealSrcSpan rss mbSpan <- ((,Nothing) -> (SrcLoc.RealSrcSpan rss, mbSpan))
  where
    RealSrcSpan rss _mbSpan = SrcLoc.RealSrcSpan rss

data UnhelpfulSpanReason
  = UnhelpfulNoLocationInfo
  | UnhelpfulWiredIn
  | UnhelpfulInteractive
  | UnhelpfulGenerated
  | UnhelpfulOther !FastString
  deriving (Eq, Show)

pattern UnhelpfulSpan :: UnhelpfulSpanReason -> SrcLoc.SrcSpan
pattern UnhelpfulSpan reason <- (toUnhelpfulReason -> Just reason)
  where
    UnhelpfulSpan reason = SrcLoc.UnhelpfulSpan (fromUnhelpfulReason reason)

fromUnhelpfulReason :: UnhelpfulSpanReason -> FastString
fromUnhelpfulReason = \case
  UnhelpfulNoLocationInfo -> fsLit "UnhelpfulNoLocationInfo"
  UnhelpfulWiredIn        -> fsLit "UnhelpfulWiredIn"
  UnhelpfulInteractive    -> fsLit "UnhelpfulInteractive"
  UnhelpfulGenerated      -> fsLit "UnhelpfulGenerated"
  UnhelpfulOther fs       -> fs

toUnhelpfulReason :: SrcLoc.SrcSpan -> Maybe UnhelpfulSpanReason
toUnhelpfulReason (SrcLoc.RealSrcSpan _) = Nothing
toUnhelpfulReason (SrcLoc.UnhelpfulSpan fs) = Just $ case unpackFS fs of
  "UnhelpfulNoLocationInfo" -> UnhelpfulNoLocationInfo
  "UnhelpfulWiredIn"        -> UnhelpfulWiredIn
  "UnhelpfulInteractive"    -> UnhelpfulInteractive
  "UnhelpfulGenerated"      -> UnhelpfulGenerated
  _                         -> UnhelpfulOther fs

-- Backporting multiplicity

data Scaled a = Scaled Mult a
  deriving (Data.Data)

instance (Outputable a) => Outputable (Scaled a) where
   ppr (Scaled _cnt t) = ppr t

irrelevantMult :: Scaled a -> a
irrelevantMult = scaledThing

mkScaled :: Mult -> a -> Scaled a
mkScaled = Scaled

scaledThing :: Scaled a -> a
scaledThing (Scaled _ t) = t

type Mult = Type

pcDataCon :: Name -> [TyVar] -> [Type] -> TyCon -> DataCon
pcDataCon n univs tys tycon = data_con
  where
    data_con = mkDataCon n
                         False
                         (mkPrelTyConRepName n)
                         (map (const (HsSrcBang NoSourceText NoSrcUnpack NoSrcStrict)) tys)
                         []
                         univs
                         []
                         (error "[TyVarBinder]")
                         []
                         []
                         tys
                         (mkTyConApp tycon (mkTyVarTys univs))
                         NoRRI
                         tycon
                         (lookupNameEnv_NF (mkTyConTagMap tycon) n)
                         []
                         (mkDataConWorkId (mkDataConWorkerName data_con (dataConWorkerUnique (nameUnique n))) data_con)
                         NoDataConRep


mkDataConWorkerName :: DataCon -> Unique -> Name
mkDataConWorkerName data_con wrk_key =
    mkWiredInName modu wrk_occ wrk_key
                  (AnId (dataConWorkId data_con)) UserSyntax
  where
    modu    = nameModule dc_name
    dc_name = dataConName data_con
    dc_occ  = nameOccName dc_name
    wrk_occ = mkDataConWorkerOcc dc_occ

pcTyCon :: Name -> Maybe CType -> [TyVar] -> [DataCon] -> TyCon
pcTyCon name cType tyvars cons
  = mkAlgTyCon name
                (mkAnonTyConBinders VisArg tyvars)
                liftedTypeKind
                (map (const Representational) tyvars)
                cType
                []              -- No stupid theta
                (mkDataTyConRhs cons)
                (VanillaAlgTyCon (mkPrelTyConRepName name))
                False           -- Not in GADT syntax


mkWiredInDataConName :: BuiltInSyntax -> Module -> FastString -> Unique -> DataCon -> Name
mkWiredInDataConName built_in modu fs unique datacon
  = mkWiredInName modu (mkDataOccFS fs) unique
                  (AConLike (RealDataCon datacon))    -- Relevant DataCon
                  built_in

multiplicityTyConKey :: Unique
multiplicityTyConKey = mkPreludeTyConUnique 192

multiplicityTyConName :: Name
multiplicityTyConName = mkWiredInTyConName UserSyntax gHC_TYPES (fsLit "Multiplicity")
                          multiplicityTyConKey multiplicityTyCon

manyDataConName :: Name
manyDataConName = mkWiredInDataConName BuiltInSyntax gHC_TYPES (fsLit "Many") manyDataConKey manyDataCon

multiplicityTyCon :: TyCon
multiplicityTyCon = pcTyCon multiplicityTyConName Nothing [] [manyDataCon]

manyDataCon :: DataCon
manyDataCon = pcDataCon manyDataConName [] [] multiplicityTyCon

manyDataConKey :: Unique
manyDataConKey = mkPreludeDataConUnique 116

manyDataConTy :: Type
manyDataConTy = mkTyConTy manyDataConTyCon

manyDataConTyCon :: TyCon
manyDataConTyCon = promoteDataCon manyDataCon

pattern Many :: Mult
pattern Many <- (isManyDataConTy -> True)
  where Many = manyDataConTy

isManyDataConTy :: Mult -> Bool
isManyDataConTy ty
  | Just tc <- tyConAppTyCon_maybe ty
  = tc `hasKey` manyDataConKey
isManyDataConTy _ = False

--
-- Dependencies and Boot
--
type IsBootInterface = GhcMake.IsBoot

-- | This data type just pairs a value 'mod' with an IsBootInterface flag. In
-- practice, 'mod' is usually a @Module@ or @ModuleName@'.
data GenWithIsBoot mod = GWIB
  { gwib_mod :: mod
  , gwib_isBoot :: IsBootInterface
  } deriving ( Eq, Ord, Show
             , Functor, Foldable, Traversable
             )

type ModuleNameWithIsBoot = GenWithIsBoot ModuleName

isBootSummary :: ModSummary -> IsBootInterface
isBootSummary ms = case Ghc.isBootSummary ms of
  True  -> GhcMake.IsBoot
  False -> GhcMake.NotBoot

getDependenciesModuleNames :: Dependencies -> [ModuleNameWithIsBoot]
getDependenciesModuleNames = map f . dep_mods
  where
    f :: (ModuleName, Bool) -> ModuleNameWithIsBoot
    f (modName, b) = let isBoot = if b then GhcMake.IsBoot else GhcMake.NotBoot in GWIB modName isBoot

dataConInstArgTys :: DataCon -> [Type] -> [Scaled Type]
dataConInstArgTys dc tys = map (mkScaled Many) (Ghc.dataConInstArgTys dc tys)

dataConOrigArgTys :: DataCon -> [Scaled Type]
dataConOrigArgTys dc = map (mkScaled Many) (Ghc.dataConOrigArgTys dc)

dataConRepArgTys :: DataCon -> [Scaled Type]
dataConRepArgTys dc = map (mkScaled Many) (Ghc.dataConRepArgTys dc)

mkLocalVar :: IdDetails -> Name -> Mult -> Type -> IdInfo -> Id
mkLocalVar idDetails' name _ ty info = Ghc.mkLocalVar idDetails' name ty info

mkUserLocal :: OccName -> Unique -> Mult -> Type -> SrcSpan -> Id
mkUserLocal occName' u _mult ty srcSpan = Ghc.mkUserLocal occName' u ty srcSpan

dataConWrapperType :: DataCon -> Type
dataConWrapperType = dataConUserType

-- WWlib

data DataConAppContext
  = DataConAppContext
  { dcac_dc      :: !DataCon
  , dcac_tys     :: ![Type]
  , dcac_arg_tys :: ![(Scaled Type, StrictnessMark)]
  , dcac_co      :: !Coercion
  }

deepSplitProductType_maybe :: FamInstEnvs -> Type -> Maybe DataConAppContext
deepSplitProductType_maybe famInstEnv ty = do
  (dc, tys, tysWithStricts, co) <- Ghc.deepSplitProductType_maybe famInstEnv ty
  pure $ DataConAppContext dc tys (map (Bi.first (mkScaled Many)) tysWithStricts) co

splitFunTys :: Type -> ([Scaled Type], Type)
splitFunTys ty = Bi.first (map (mkScaled Many)) $ Ghc.splitFunTys ty

apiAnnComments :: (Map ApiAnnKey [SrcSpan], Map SrcSpan [Located AnnotationComment])
               -> Map SrcSpan [Located AnnotationComment]
apiAnnComments = snd

mkIntExprInt :: Platform -> Int -> CoreExpr
mkIntExprInt _ int' = Ghc.mkIntExprInt unsafeGlobalDynFlags int'

dataConFullSig :: DataCon -> ([TyVar], [TyCoVar], [EqSpec], ThetaType, [Scaled Type], Type)
dataConFullSig dc =
  let (tyvars, tycovars, eqspecs, theta, tys, ty) = Ghc.dataConFullSig dc
  in  (tyvars, tycovars, eqspecs, theta, map (mkScaled Many) tys, ty)


#endif
#endif

--
-- Compat shim for GHC 8.6.5

#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,8,1,0)

pattern LitString :: ByteString -> Lit.Literal
pattern LitString bs <- Lit.MachStr bs where
    LitString bs = Lit.MachStr bs

pattern LitFloat :: GHC.Real.Ratio Integer -> Lit.Literal
pattern LitFloat f <- Lit.MachFloat f where
    LitFloat f = Lit.MachFloat f

pattern LitDouble :: GHC.Real.Ratio Integer -> Lit.Literal
pattern LitDouble d <- Lit.MachDouble d where
    LitDouble d = Lit.MachDouble d

pattern LitChar :: Char -> Lit.Literal
pattern LitChar c <- Lit.MachChar c where
    LitChar c = Lit.MachChar c

pattern Bndr :: var -> argf -> Var.TyVarBndr var argf
pattern Bndr var argf <- TvBndr var argf where
    Bndr var argf = TvBndr var argf

type VarBndr = TyVarBndr

isEqPrimPred :: Type -> Bool
isEqPrimPred = Ghc.isPredTy

-- See NOTE [isEvVarType].
isEvVarType :: Type -> Bool
isEvVarType = Ghc.isPredTy

tyConRealArity :: TyCon -> Int
tyConRealArity = tyConArity

#endif
#endif

--
-- Compat shim for GHC-8.6.5 and GHC-8.8.x
--
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)

-- | The non-dependent version of 'ArgFlag'.

-- Appears here partly so that it's together with its friend ArgFlag,
-- but also because it is used in IfaceType, rather early in the
-- compilation chain
-- See Note [AnonArgFlag vs. ForallVisFlag]
data AnonArgFlag
  = VisArg    -- ^ Used for @(->)@: an ordinary non-dependent arrow.
              --   The argument is visible in source code.
  | InvisArg  -- ^ Used for @(=>)@: a non-dependent predicate arrow.
              --   The argument is invisible in source code.
  deriving (Eq, Ord, Data)

instance Outputable AnonArgFlag where
  ppr VisArg   = text "[vis]"
  ppr InvisArg = text "[invis]"

instance Binary AnonArgFlag where
  put_ bh VisArg   = putByte bh 0
  put_ bh InvisArg = putByte bh 1

  get bh = do
    h <- getByte bh
    case h of
      0 -> return VisArg
      _ -> return InvisArg

mkAnonTyConBinders :: AnonArgFlag -> [TyVar] -> [TyConBinder]
mkAnonTyConBinders _ = Ty.mkAnonTyConBinders

bytesFS :: FastString -> ByteString
bytesFS = fastStringToByteString

mkFunTy :: AnonArgFlag -> Mult -> Type -> Type -> Type
mkFunTy _ _ = Ty.FunTy

pattern FunTy :: AnonArgFlag -> Mult -> Type -> Type -> Type
pattern FunTy { ft_af, ft_mult, ft_arg, ft_res } <- ((VisArg,Many,) -> (ft_af, ft_mult, Ty.FunTy ft_arg ft_res)) where
    FunTy _ft_af _ft_mult ft_arg ft_res = Ty.FunTy ft_arg ft_res

pattern AnonTCB :: AnonArgFlag -> Ty.TyConBndrVis
pattern AnonTCB af <- ((VisArg,) -> (af, Ty.AnonTCB)) where
    AnonTCB _af = Ty.AnonTCB

noExtField :: NoExt
noExtField = NoExt

#endif

-- Compat shim for GHC 8.8.x

#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,8,1,0) && !MIN_VERSION_GLASGOW_HASKELL(8,10,1,0)

isEqPrimPred :: Type -> Bool
isEqPrimPred ty
  | Just tc <- tyConAppTyCon_maybe ty
  = tc `hasKey` Ghc.eqPrimTyConKey || tc `hasKey` Ghc.eqReprPrimTyConKey
  | otherwise
  = False

isEqPred :: Type -> Bool
isEqPred ty
  | Just tc <- tyConAppTyCon_maybe ty
  , Just cls <- tyConClass_maybe tc
  = cls `hasKey` Ghc.eqTyConKey || cls `hasKey` Ghc.heqTyConKey
  | otherwise
  = False

-- See NOTE [isEvVarType].
isEvVarType :: Type -> Bool
isEvVarType = Ghc.isEvVarType

#endif
#endif

{- | [NOTE:tyConRealArity]

The semantics of 'tyConArity' changed between GHC 8.6.5 and GHC 8.10, mostly due to the
Visible Dependent Quantification (VDQ). As a result, given the following:

data family EntityField record :: * -> *

Calling `tyConArity` on this would yield @2@ for 8.6.5 but @1@ an 8.10, so we try to backport
the old behaviour in 8.10 by \"looking\" at the 'Kind' of the input 'TyCon' and trying to recursively
split the type apart with either 'splitFunTy_maybe' or 'splitForAllTy_maybe'.

-}

{- | [NOTE:isEvVarType]

For GHC < 8.8.1 'isPredTy' is effectively the same as the new 'isEvVarType', which covers the cases
for coercion types and \"normal\" type coercions. The 8.6.5 version of 'isPredTy' had a special case to
handle a 'TyConApp' in the case of type equality (i.e. ~ ) which was removed in the implementation
for 8.8.1, which essentially calls 'tcIsConstraintKind' straight away.
-}

--
-- Support for GHC >= 8.8
--

#if MIN_VERSION_GLASGOW_HASKELL(8,8,1,0) && !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)

-- See NOTE [tyConRealArity].
tyConRealArity :: TyCon -> Int
tyConRealArity tc = go 0 (tyConKind tc)
  where
    go :: Int -> Kind -> Int
    go !acc k =
      case asum [fmap snd (splitFunTy_maybe k), fmap snd (splitForAllTy_maybe k)] of
        Nothing -> acc
        Just ks -> go (acc + 1) ks

dataConExTyVars :: DataCon -> [TyVar]
dataConExTyVars = dataConExTyCoVars

#endif

--
-- Compat shim for 8.10.x
--

#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0) && !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
pattern FunTy :: AnonArgFlag -> Mult -> Type -> Type -> Type
pattern FunTy { ft_af, ft_mult, ft_arg, ft_res } <- ((Many,) -> (ft_mult, Ty.FunTy ft_af ft_arg ft_res)) where
    FunTy ft_af' _ft_mult ft_arg' ft_res' = Ty.FunTy ft_af' ft_arg' ft_res'

mkFunTy :: AnonArgFlag -> Mult -> Type -> Type -> Type
mkFunTy af _ arg res = Ty.FunTy af arg res
#endif

--
-- Compat shim for 9.0.x

#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)

-- 'fsToUnitId' is gone in GHC 9, but we can bring code it in terms of 'fsToUnit' and 'toUnitId'.
fsToUnitId :: FastString -> UnitId
fsToUnitId = toUnitId . fsToUnit

moduleUnitId :: Module -> UnitId
moduleUnitId = toUnitId . moduleUnit

thisPackage :: DynFlags -> UnitId
thisPackage = toUnitId . homeUnit

-- See NOTE [tyConRealArity].
tyConRealArity :: TyCon -> Int
tyConRealArity tc = go 0 (tyConKind tc)
  where
    go :: Int -> Kind -> Int
    go !acc k =
      case asum [fmap (view _3) (splitFunTy_maybe k), fmap snd (splitForAllTy_maybe k)] of
        Nothing -> acc
        Just ks -> go (acc + 1) ks

dataConExTyVars :: DataCon -> [TyVar]
dataConExTyVars = dataConExTyCoVars

getDependenciesModuleNames :: Dependencies -> [ModuleNameWithIsBoot]
getDependenciesModuleNames = dep_mods

renderWithStyle :: DynFlags -> SDoc -> PprStyle -> String
renderWithStyle dynflags sdoc style = Ghc.renderWithStyle (Ghc.initSDocContext dynflags style) sdoc

mkUserStyle :: DynFlags -> PrintUnqualified -> Depth -> PprStyle
mkUserStyle _ = Ghc.mkUserStyle

--
-- Literal
--

-- In GHC 9 'LitNumber' doesn't have the extra 3rd argument, so we simply ignore it in the construction.

pattern LitNumber :: Ghc.LitNumType -> Integer -> Ghc.Type -> Ghc.Literal
pattern LitNumber numType integer' ty <- ((intPrimTy,) -> (ty, Ghc.LitNumber numType integer'))
  where
    LitNumber numType integer' _ = Ghc.LitNumber numType integer'

-- This function is gone in GHC 9.
dataConSig :: DataCon -> ([TyCoVar], ThetaType, [Type], Type)
dataConSig dc
  = (dataConUnivAndExTyCoVars dc, dataConTheta dc, map irrelevantMult $ dataConOrigArgTys dc, dataConOrigResTy dc)

gcatch :: (Ex.MonadCatch m, Exception e) => m a -> (e -> m a) -> m a
gcatch = Ex.catch

#endif

--
-- End of compatibility shim.
--
#endif
