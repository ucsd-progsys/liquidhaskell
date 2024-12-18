{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Liquid.GHC.API.Extra (
    module StableModule
  , ApiComment(..)
  , addNoInlinePragmasToBinds
  , apiComments
  , apiCommentsParsedSource
  , dataConSig
  , directImports
  , fsToUnitId
  , isPatErrorAlt
  , minus_RDR
  , qualifiedNameFS
  , renderWithStyle
  , showPprQualified
  , showPprDebug
  , showSDocQualified
  , splitDollarApp
  , strictNothing
  , thisPackage
  , tyConRealArity
  , untick
  ) where

import           Liquid.GHC.API.StableModule      as StableModule
import GHC hiding (modInfoLookupName)
import Data.Data (Data, gmapQr, gmapT)
import Data.Generics (extQ, extT)
import Data.Foldable                  (asum)
import Data.List                      (sortOn)
import GHC.Builtin.Names ( dollarIdKey, minusName )
import GHC.Core                       as Ghc
import GHC.Core.Coercion              as Ghc
import GHC.Core.DataCon               as Ghc
import GHC.Core.Make                  (pAT_ERROR_ID)
import GHC.Core.Type                  as Ghc hiding (typeKind , isPredTy, extendCvSubst, linear)
import GHC.Data.FastString            as Ghc
import GHC.Data.Maybe
import qualified GHC.Data.Strict
import GHC.Driver.Session             as Ghc
import GHC.Tc.Types
import GHC.Types.Id
import GHC.Types.Basic
import GHC.Types.Name                 (isSystemName, nameModule_maybe, occNameFS)
import GHC.Types.Name.Reader          (nameRdrName)
import GHC.Types.SrcLoc               as Ghc
import GHC.Types.Unique               (getUnique, hasKey)

import GHC.Utils.Outputable           as Ghc hiding ((<>))

import GHC.Unit.Module

-- 'fsToUnitId' is gone in GHC 9, but we can bring code it in terms of 'fsToUnit' and 'toUnitId'.
fsToUnitId :: FastString -> UnitId
fsToUnitId = toUnitId . fsToUnit

thisPackage :: DynFlags -> UnitId
thisPackage = homeUnitId_

-- See NOTE [tyConRealArity].
tyConRealArity :: TyCon -> Int
tyConRealArity tc = go 0 (tyConKind tc)
  where
    go :: Int -> Kind -> Int
    go !acc k =
      case asum [fmap (\(_, _, _, c) -> c) (splitFunTy_maybe k), fmap snd (splitForAllTyCoVar_maybe k)] of
        Nothing -> acc
        Just ks -> go (acc + 1) ks

renderWithStyle :: DynFlags -> SDoc -> PprStyle -> String
renderWithStyle dynflags sdoc style = Ghc.renderWithContext (Ghc.initSDocContext dynflags style) sdoc

-- This function is gone in GHC 9.
dataConSig :: DataCon -> ([TyCoVar], ThetaType, [Type], Type)
dataConSig dc
  = (dataConUnivAndExTyCoVars dc, dataConTheta dc, map irrelevantMult $ dataConOrigArgTys dc, dataConOrigResTy dc)

-- | Extracts the direct imports of a module.
directImports :: TcGblEnv -> [Module]
directImports = moduleEnvKeys . imp_mods . tcg_imports

-- | Abstraction of 'EpaComment'.
data ApiComment
  = ApiLineComment String
  | ApiBlockComment String
  deriving (Eq, Show)

-- | Extract top-level comments from a module.
apiComments :: HsParsedModule -> [Ghc.Located ApiComment]
apiComments = apiCommentsParsedSource . hpm_module

apiCommentsParsedSource :: Located (HsModule GhcPs) -> [Ghc.Located ApiComment]
apiCommentsParsedSource ps =
    let hs = unLoc ps
        go :: forall a. Data a => a -> [LEpaComment]
        go = gmapQr (++) [] go `extQ` (id @[LEpaComment])
     in Data.List.sortOn (spanToLineColumn . getLoc) $
          mapMaybe (tokComment . toRealSrc) $ go hs
  where
    tokComment (L sp (EpaComment (EpaLineComment s) _)) = Just (L sp (ApiLineComment s))
    tokComment (L sp (EpaComment (EpaBlockComment s) _)) = Just (L sp (ApiBlockComment s))
    tokComment _ = Nothing

    -- TODO: take into account anchor_op, which only matters if the source was
    -- pre-processed by an exact-print-aware tool.
    toRealSrc (L a e) = L (RealSrcSpan (anchor a) strictNothing) e

    spanToLineColumn =
      fmap (\s -> (srcSpanStartLine s, srcSpanStartCol s)) . srcSpanToRealSrcSpan

-- | Adds NOINLINE pragmas to all bindings in the module.
--
-- This prevents the simple optimizer from inlining such bindings which might
-- have specs that would otherwise be left dangling.
--
-- https://gitlab.haskell.org/ghc/ghc/-/issues/24386
--
addNoInlinePragmasToBinds :: TcGblEnv -> TcGblEnv
addNoInlinePragmasToBinds tcg = tcg{ tcg_binds = go (tcg_binds tcg) }
  where
    go :: forall a. Data a => a -> a
    go = gmapT $ go `extT` markHsBind

    -- Mark all user-originating `Id` binders as `NOINLINE`.
    markHsBind :: HsBind GhcTc -> HsBind GhcTc
    markHsBind = \case
        bind@VarBind{ var_id = var, var_rhs = rhs } -> bind{ var_id = markId var, var_rhs = go rhs }
        bind@FunBind{ fun_id = var, fun_matches = matches } -> bind{ fun_id = markId <$> var, fun_matches = go matches }
        bind@PatBind{ pat_lhs = lhs, pat_rhs = rhs } -> bind{ pat_lhs = markPat <$> lhs, pat_rhs = go rhs }
        PatSynBind{} -> error "markNoInline: unexpected PatSynBind, should have been eliminated by the typechecker"
        XHsBindsLR absBinds -> XHsBindsLR (markAbsBinds absBinds)

    markPat :: Pat GhcTc -> Pat GhcTc
    markPat = \case
        VarPat ext var -> VarPat ext (markId <$> var)
        pat -> gmapT (id `extT` markPat) pat

    markId :: Id -> Id
    markId var = var `setInlinePragma` neverInlinePragma

    -- The AbsBinds come from the GHC typechecker to handle polymorphism,
    -- overloading, and recursion, so those don't correspond directly to
    -- user-written `Id`s except for those in @abs_exports@. For instance,
    -- @tests/pos/Map0.hs@ would fail if Ids in @abs_exports@ are not marked.
    --
    -- See
    -- https://github.com/ucsd-progsys/liquidhaskell/issues/2257 for more
    -- context.
    markAbsBinds :: AbsBinds -> AbsBinds
    markAbsBinds absBinds0@AbsBinds{ abs_binds = binds, abs_exports = exports }  =
        absBinds0
          { abs_binds = fmap skipFirstHsBind <$> binds
          , abs_exports = map markABE exports
          }
      where
        skipFirstHsBind :: HsBind GhcTc -> HsBind GhcTc
        skipFirstHsBind = \case
          XHsBindsLR absBinds -> XHsBindsLR (markAbsBinds absBinds)
          b -> gmapT go b

        markABE :: ABExport -> ABExport
        markABE abe@ABE{ abe_poly = poly
                       , abe_mono = mono } = abe
          { abe_poly = markId poly
          , abe_mono = markId mono }

-- | Tells if a case alternative calls to patError
isPatErrorAlt :: CoreAlt -> Bool
isPatErrorAlt (Alt _ _ exprCoreBndr) = hasPatErrorCall exprCoreBndr
  where
   hasPatErrorCall :: CoreExpr -> Bool
   -- auto generated undefined case: (\_ -> (patError @levity @type "error message")) void
   -- Type arguments are erased before calling isUndefined
   hasPatErrorCall (App e _)
     | Var x <- unTick e = x == pAT_ERROR_ID
     | otherwise = hasPatErrorCall e
   -- another auto generated undefined case:
   -- let lqanf_... = patError "error message") in case lqanf_... of {}
   hasPatErrorCall (Let (NonRec x e) ec)
     | Case e0 _ _ [] <- unTick ec
     , Var v <- unTick e0
     , x == v = hasPatErrorCall e
   hasPatErrorCall (Case e _ _ _) = hasPatErrorCall e
   hasPatErrorCall (Let _ e) = hasPatErrorCall e
   hasPatErrorCall (Tick _ e) = hasPatErrorCall e
   -- otherwise
   hasPatErrorCall _ = False

   unTick (Tick _ e) = unTick e
   unTick e = e


qualifiedNameFS :: Name -> FastString
qualifiedNameFS n = concatFS [modFS, occFS, uniqFS]
  where
  modFS = case nameModule_maybe n of
            Nothing -> fsLit ""
            Just m  -> concatFS [moduleNameFS (moduleName m), fsLit "."]

  occFS = occNameFS (getOccName n)
  uniqFS
    | isSystemName n
    = concatFS [fsLit "_",  fsLit (showPprQualified (getUnique n))]
    | otherwise
    = fsLit ""

-- Variants of Outputable functions which now require DynFlags!
showPprQualified :: Outputable a => a -> String
showPprQualified = showSDocQualified . ppr

showSDocQualified :: Ghc.SDoc -> String
showSDocQualified = Ghc.renderWithContext ctx
  where
    style = Ghc.mkUserStyle myQualify Ghc.AllTheWay
    ctx = Ghc.defaultSDocContext { sdocStyle = style }

myQualify :: Ghc.NamePprCtx
myQualify = Ghc.neverQualify { Ghc.queryQualifyName = Ghc.alwaysQualifyNames }
-- { Ghc.queryQualifyName = \_ _ -> Ghc.NameNotInScope1 }

showPprDebug :: Outputable a => a -> String
showPprDebug = showSDocDebug . ppr

showSDocDebug :: Ghc.SDoc -> String
showSDocDebug = Ghc.renderWithContext ctx
  where
    style = Ghc.mkUserStyle myQualify Ghc.AllTheWay
    ctx = Ghc.defaultSDocContext {
        sdocStyle = style
      , sdocPprDebug = True
      }

strictNothing :: GHC.Data.Strict.Maybe a
strictNothing = GHC.Data.Strict.Nothing

splitDollarApp :: CoreExpr -> Maybe (CoreExpr, CoreExpr)
splitDollarApp e
     -- matches `$ t1 t2 t3 t4 f a`
     | App e1 a  <- untick e
     , App e2 f  <- untick e1
     , App e3 t4 <- untick e2
     , App e4 t3 <- untick e3
     , App e5 t2 <- untick e4
     , App d t1  <- untick e5
     , Var v     <- untick d
     , v `hasKey` dollarIdKey
     , Type _    <- untick t1
     , Type _    <- untick t2
     , Type _    <- untick t3
     , Type _    <- untick t4
     = Just (f, a)
     | otherwise
     = Nothing

untick :: CoreExpr -> CoreExpr
untick (Tick _ e) = untick e
untick e = e

minus_RDR :: RdrName
minus_RDR = nameRdrName minusName
