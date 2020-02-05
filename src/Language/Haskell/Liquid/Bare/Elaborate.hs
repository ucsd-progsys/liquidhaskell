{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE ExplicitForAll            #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE LambdaCase                #-}
-- | This module uses GHC API to elaborate the resolves expressions

module Language.Haskell.Liquid.Bare.Elaborate
  ( fixExprToHsExpr
  , elaborateSpecType
  )
where

import qualified Language.Fixpoint.Types       as F
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType
import qualified Data.List                     as L
import           Language.Haskell.Liquid.Types.Errors
import           Control.Monad.Free
import           Data.Functor.Foldable
import           GHC
import           OccName
import           FastString
import           HsPat
import           SrcLoc
import           Control.Monad
import           CoreSyn
import           Exception
import           Inst
import           Panic                   hiding ( panic )
import           Desugar
import           TcRnMonad
import           TcHsSyn
import           RnExpr
import           GhcMonad
import           TcSimplify
import           PrelNames
import           Outputable              hiding ( panic )
import           TysWiredIn                     ( boolTyCon )
import           HscTypes
import           ErrUtils
import           HscMain
import           TcExpr
import           HsExpr
import           RdrName
import           TysWiredIn
import           BasicTypes
import           PrelNames
import           Data.Default                   ( def )


-- | Base functor of RType
data RTypeF c tv r f
  = RVarF {
      rtf_var    :: !tv
    , rtf_reft   :: !r
    }

  | RFunF  {
      rtf_bind   :: !F.Symbol
    , rtf_in     :: !f
    , rtf_out    :: !f
    , rtf_reft   :: !r
    }

  | RImpFF  {
      rtf_bind   :: !F.Symbol
    , rtf_in     :: !f
    , rtf_out    :: !f
    , rtf_reft   :: !r
    }

  | RAllTF {
      rtf_tvbind :: !(RTVU c tv) -- RTVar tv (RType c tv ()))
    , rtf_ty     :: !f
    , rtf_ref    :: !r
    }

  -- | "forall x y <z :: Nat, w :: Int> . TYPE"
  --               ^^^^^^^^^^^^^^^^^^^ (rtf_pvbind)
  | RAllPF {
      rtf_pvbind :: !(PVU c tv)  -- ar (RType c tv ()))
    , rtf_ty     :: !f
    }

  -- | For example, in [a]<{\h -> v > h}>, we apply (via `RApp`)
  --   * the `RProp`  denoted by `{\h -> v > h}` to
  --   * the `RTyCon` denoted by `[]`.
  | RAppF  {
      rtf_tycon  :: !c
    , rtf_args   :: ![f]
    , rtf_pargs  :: ![RTPropF c tv f]
    , rtf_reft   :: !r
    }

  | RAllEF {
      rtf_bind   :: !F.Symbol
    , rtf_allarg :: !f
    , rtf_ty     :: !f
    }

  | RExF {
      rtf_bind   :: !F.Symbol
    , rtf_exarg  :: !f
    , rtf_ty     :: !f
    }

  | RExprArgF (F.Located F.Expr)

  | RAppTyF{
      rtf_arg   :: !f
    , rtf_res   :: !f
    , rtf_reft  :: !r
    }

  | RRTyF  {
      rtf_env   :: ![(F.Symbol, f)]
    , rtf_ref   :: !r
    , rtf_obl   :: !Oblig
    , rtf_ty    :: !f
    }

  | RHoleF r
  deriving (Functor)

-- It's probably ok to treat (RType c tv ()) as a leaf..
type RTPropF c tv f = Ref (RType c tv ()) f


-- | SpecType with Holes.
--   It provides us a context to construct the ghc queries.
--   I don't think we can reuse RHole since it is not intended
--   for this use case

type SpecTypeF = RTypeF RTyCon RTyVar RReft
type PartialSpecType = Free (RTypeF RTyCon RTyVar RReft) ()

type instance Base (RType c tv r) = RTypeF c tv r

instance Recursive (RType c tv r) where
  project (RVar var reft           ) = RVarF var reft
  project (RFun  bind tin tout reft) = RFunF bind tin tout reft
  project (RImpF bind tin tout reft) = RImpFF bind tin tout reft
  project (RAllT tvbind ty ref     ) = RAllTF tvbind ty ref
  project (RAllP pvbind ty         ) = RAllPF pvbind ty
  project (RApp c args pargs reft  ) = RAppF c args pargs reft
  project (RAllE bind allarg ty    ) = RAllEF bind allarg ty
  project (REx   bind exarg  ty    ) = RExF bind exarg ty
  project (RExprArg e              ) = RExprArgF e
  project (RAppTy arg res reft     ) = RAppTyF arg res reft
  project (RRTy env ref obl ty     ) = RRTyF env ref obl ty
  project (RHole r                 ) = RHoleF r

instance Corecursive (RType c tv r) where
  embed (RVarF var reft           ) = RVar var reft
  embed (RFunF  bind tin tout reft) = RFun bind tin tout reft
  embed (RImpFF bind tin tout reft) = RImpF bind tin tout reft
  embed (RAllTF tvbind ty ref     ) = RAllT tvbind ty ref
  embed (RAllPF pvbind ty         ) = RAllP pvbind ty
  embed (RAppF c args pargs reft  ) = RApp c args pargs reft
  embed (RAllEF bind allarg ty    ) = RAllE bind allarg ty
  embed (RExF   bind exarg  ty    ) = REx bind exarg ty
  embed (RExprArgF e              ) = RExprArg e
  embed (RAppTyF arg res reft     ) = RAppTy arg res reft
  embed (RRTyF env ref obl ty     ) = RRTy env ref obl ty
  embed (RHoleF r                 ) = RHole r


-- specTypeToLHsType :: SpecType -> LHsType GhcPs
-- specTypeToLHsType = typeToLHsType . toType

-- -- Given types like x:a -> y:a -> _, this function returns x:a -> y:a -> Bool
-- -- Free monad takes care of substitution

-- A one-way function. Kind of like injecting something into Maybe
specTypeToPartial :: forall a . SpecType -> SpecTypeF (Free SpecTypeF a)
specTypeToPartial = hylo (fmap wrap) project

-- probably should return spectype instead..
plugType :: SpecType -> PartialSpecType -> SpecType
plugType t = refix . f
 where
  f = hylo Fix $ \case
    Pure _   -> specTypeToPartial t
    Free res -> res

-- build the expression we send to ghc for elaboration
-- YL: tweak this function to see if ghc accepts explicit dictionary binders
buildHsExpr :: LHsExpr GhcPs -> SpecType -> LHsExpr GhcPs
buildHsExpr res = para $ \case
  RFunF bind (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (symbolToRdrName varName bind)] res
  RImpFF bind (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (symbolToRdrName varName bind)] res
  RAllEF  _ _        (_, res) -> res
  RAllTF  _ (_, res) _        -> res
  RExF    _ _        (_, res) -> res
  RAppTyF _ (_, res) _        -> res
  RRTyF _ _ _ (_, res)        -> res
  _                           -> res

elaborateSpecType
  :: PartialSpecType
  -> (CoreExpr -> F.Expr)
  -> SpecType
  -> Ghc (SpecType, [F.Symbol]) -- binders for dictionaries
                   -- should have returned Maybe [F.Symbol]
elaborateSpecType partialTp coreToLogic t = case F.tracepp "elaborateSpecType" t of
  RVar (RTV tv) (MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
    elaborateReft
      (reft, t)
      (pure (t, []))
      (\bs' ee -> pure (RVar (RTV tv) (MkUReft (F.Reft (vv, ee)) p), bs'))
  RFun bind tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
    -- the reft is never actually used by the child
    -- maybe i should enforce this information at the type level
    let partialFunTp =
          Free (RFunF bind (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
        partialTp' = partialTp >> partialFunTp :: PartialSpecType
    (eTin , bs' ) <- elaborateSpecType partialTp' coreToLogic tin
    (eTout, bs'') <- elaborateSpecType partialTp' coreToLogic tout
    -- eTin and eTout might have different dictionary names
    -- need to do a substitution to make the reference to dictionaries consistent
    -- if isClassType eTin
    elaborateReft
      (reft, t)
      (pure (RFun bind eTin eTout ureft, bs'))
      (\bs' ee -> pure (RFun bind eTin eTout (MkUReft (F.Reft (vv, ee)) p), bs')
      )
  RImpF bind tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
    let partialFunTp =
          Free (RImpFF bind (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
        partialTp' = partialTp >> partialFunTp :: PartialSpecType
    (eTin , bs' ) <- elaborateSpecType partialTp' coreToLogic tin
    (eTout, bs'') <- elaborateSpecType partialTp' coreToLogic tout
    -- eTin and eTout might have different dictionary names
    -- need to do a substitution to make the reference to dictionaries consistent
    -- if isClassType eTin
    elaborateReft
      (reft, t)
      (pure (RImpF bind eTin eTout ureft, bs'))
      (\bs' ee ->
        pure (RImpF bind eTin eTout (MkUReft (F.Reft (vv, ee)) p), bs')
      )
  -- support for RankNTypes/ref
  RAllT (RTVar tv ty) tout ref -> do
    (eTout, bts') <- elaborateSpecType
      (partialTp >> Free (RAllTF (RTVar tv ty) (pure ()) ref))
      coreToLogic
      tout
    pure (RAllT (RTVar tv ty) eTout ref, bts')
  RAllP pvbind tout -> do
    (eTout, bts') <- elaborateSpecType (partialTp >> Free (RAllPF pvbind (pure ())))
                                       coreToLogic
                                       tout
    pure (RAllP pvbind eTout, bts')
  -- pargs not handled for now
  -- RApp tycon args pargs reft
  RApp tycon args pargs ureft@(MkUReft reft@(F.Reft (vv, _)) p)
    | isClass tycon -> pure (t, [])
    | otherwise -> elaborateReft
      (reft, t)
      (pure (RApp tycon args pargs ureft, []))
      (\bs' ee ->
        pure (RApp tycon args pargs (MkUReft (F.Reft (vv, ee)) p), bs')
      )
  RAppTy arg res ureft@(MkUReft reft@(F.Reft (vv, _)) p) -> do
    (eArg, bs' ) <- elaborateSpecType partialTp coreToLogic arg
    (eRes, bs'') <- elaborateSpecType partialTp coreToLogic res
    elaborateReft
      (reft, t)
      (pure (RAppTy eArg eRes ureft, bs''))
      (\bs' ee -> pure (RAppTy eArg eRes (MkUReft (F.Reft (vv, ee)) p), bs''))
  RAllE _ _ _ -> todo Nothing ("Not sure how to elaborate RAllE" ++ F.showpp t)
  REx   _ _ _ -> todo Nothing ("Not sure how to elaborate REx" ++ F.showpp t)
  RExprArg _ ->
    todo Nothing ("Not sure how to elaborate RExprArg" ++ F.showpp t)
  RRTy _ _ _ _ -> todo Nothing ("Not sure how to elaborate RRTy" ++ F.showpp t)
  _            -> todo Nothing ("Not sure how to elaborate " ++ F.showpp t)
 where
  boolType = RApp (RTyCon boolTyCon [] def) [] [] mempty :: SpecType
  elaborateReft
    :: (F.Reft, SpecType) -> Ghc a -> ([F.Symbol] -> F.Expr -> Ghc a) -> Ghc a
  elaborateReft (reft@(F.Reft (vv, e)), vvTy) trivial nonTrivialCont =
    if isTrivial reft
      then trivial
      else do
-- liftIO $ putStrLn query
        let querySpecType =
              plugType (rFun vv vvTy boolType) partialTp :: SpecType
            hsExpr =
              buildHsExpr
                ( 
                 fixExprToHsExpr e
                )
                querySpecType :: LHsExpr GhcPs
            exprWithTySigs =
              GM.tracePpr "exprWithTySigs" $ noLoc $ ExprWithTySig
                (mkLHsSigWcType $ specTypeToLHsType (F.tracepp "querySpecType" querySpecType))
                hsExpr :: LHsExpr GhcPs
        (msgs, mbExpr) <- GM.elaborateHsExprInst exprWithTySigs
        case mbExpr of
          Nothing -> panic
            Nothing
            (  "Ghc is unable to elaborate the expression: "
            ++ GM.showPpr exprWithTySigs
            ++ "\n"
            ++ GM.showPpr (GM.showSDoc <$> pprErrMsgBagWithLoc (snd msgs))
            )
          Just eeWithLamsCore -> do
            let eeWithLams =
                  coreToLogic (GM.tracePpr "eeWithLamsCore" eeWithLamsCore)
                (bs', ee) = F.tracepp "grabLams" $ grabLams ([], eeWithLams)
            nonTrivialCont (GM.dropModuleUnique <$> bs')
                           (dropBinderUnique bs' ee)
  isTrivial :: F.Reft -> Bool
  isTrivial (F.Reft (_, ee)) = (L.null . F.syms) ee
  grabLams :: ([F.Symbol], F.Expr) -> ([F.Symbol], F.Expr)
  grabLams (bs, F.ELam (b, _) e) = grabLams (b : bs, e)
  grabLams bse                   = bse
  dropBinderUnique :: [F.Symbol] -> F.Expr -> F.Expr
  dropBinderUnique binders = F.tracepp "ElaboratedExpr"
    . F.substa (\x -> if L.elem x binders then GM.dropModuleUnique x else x)




-- | Embed fixpoint expressions into parsed haskell expressions.
--   It allows us to bypass the GHC parser and use arbitrary symbols
--   for identifiers (compared to using the string API)
fixExprToHsExpr :: F.Expr -> LHsExpr GhcPs
fixExprToHsExpr (F.ECon c) = constantToHsExpr c
fixExprToHsExpr (F.EVar x) =
  noLoc (HsVar NoExt (noLoc (symbolToRdrName varName x)))
fixExprToHsExpr (F.EApp e0 e1) =
  noLoc (HsApp NoExt (fixExprToHsExpr e0) (fixExprToHsExpr e1))
fixExprToHsExpr (F.ENeg e) = noLoc
  (HsApp NoExt
         (noLoc (HsVar NoExt (noLoc (nameRdrName negateName))))
         (fixExprToHsExpr e)
  )
fixExprToHsExpr (F.EBin bop e0 e1) = noLoc
  (HsApp NoExt
         (noLoc (HsApp NoExt (bopToHsExpr bop) (fixExprToHsExpr e0)))
         (fixExprToHsExpr e1)
  )
fixExprToHsExpr (F.EIte p e0 e1) = noLoc
  (HsIf NoExt
        Nothing
        (fixExprToHsExpr p)
        (fixExprToHsExpr e0)
        (fixExprToHsExpr e1)
  )
-- FIXME: convert sort to HsType
fixExprToHsExpr (F.ECst e0 _) = fixExprToHsExpr e0
fixExprToHsExpr (F.PAnd es  ) = noLoc
  (HsApp
    NoExt
    (noLoc (HsVar NoExt (noLoc (varQual_RDR dATA_FOLDABLE (fsLit "and")))))
    (noLoc (ExplicitList NoExt Nothing (fixExprToHsExpr <$> es)))
  )
fixExprToHsExpr (F.POr es) = noLoc
  (HsApp
    NoExt
    (noLoc (HsVar NoExt (noLoc (varQual_RDR dATA_FOLDABLE (fsLit "or")))))
    (noLoc (ExplicitList NoExt Nothing (fixExprToHsExpr <$> es)))
  )
fixExprToHsExpr (F.PNot e) =
  noLoc (HsApp NoExt (noLoc (HsVar NoExt (noLoc not_RDR))) (fixExprToHsExpr e))
fixExprToHsExpr (F.PAtom brel e0 e1) = noLoc
  (HsApp NoExt
         (noLoc (HsApp NoExt (brelToHsExpr brel) (fixExprToHsExpr e0)))
         (fixExprToHsExpr e1)
  )
fixExprToHsExpr (F.PImp e0 e1) = noLoc
  (HsApp
    NoExt
    (noLoc
      (HsApp NoExt
             (noLoc (HsVar NoExt (noLoc (mkVarUnqual (mkFastString "==>")))))
             (fixExprToHsExpr e0)
      )
    )
    (fixExprToHsExpr e1)
  )
fixExprToHsExpr e =
  todo Nothing ("toGhcExpr: Don't know how to handle " ++ show e)

constantToHsExpr :: F.Constant -> LHsExpr GhcPs
-- constantToHsExpr (F.I c) = noLoc (HsLit NoExt (HsInt NoExt (mkIntegralLit c)))
constantToHsExpr (F.I i) =
  noLoc (HsOverLit NoExt (mkHsIntegral (mkIntegralLit i)))
constantToHsExpr (F.R d) =
  noLoc (HsOverLit NoExt (mkHsFractional (mkFractionalLit d)))
constantToHsExpr _ =
  todo Nothing "constantToHsExpr: Not sure how to handle constructor L"

-- This probably won't work because of the qualifiers
bopToHsExpr :: F.Bop -> LHsExpr GhcPs
bopToHsExpr bop = noLoc (HsVar NoExt (noLoc (f bop)))
 where
  f F.Plus   = plus_RDR
  f F.Minus  = minus_RDR
  f F.Times  = times_RDR
  f F.Div    = mkVarUnqual (fsLit "/")
  f F.Mod    = varQual_RDR gHC_REAL (fsLit "mod")
  f F.RTimes = times_RDR
  f F.RDiv   = varQual_RDR gHC_REAL (fsLit "/")

brelToHsExpr :: F.Brel -> LHsExpr GhcPs
brelToHsExpr brel = noLoc (HsVar NoExt (noLoc (f brel)))
 where
  f F.Eq = mkVarUnqual (mkFastString "==")
  f F.Gt = gt_RDR
  f F.Lt = lt_RDR
  f F.Ge = ge_RDR
  f F.Le = le_RDR
  f F.Ne = mkVarUnqual (mkFastString "/=")
  f _    = impossible Nothing "brelToExpr: Unsupported operation"


symbolToRdrName :: NameSpace -> F.Symbol -> RdrName
symbolToRdrName ns x
  | F.isNonSymbol modName = mkUnqual ns (mkFastString (F.symbolString s))
  | otherwise = mkQual
    ns
    (mkFastString (F.symbolString modName), mkFastString (F.symbolString s))
  where (modName, s) = GM.splitModuleName x


-- SpecType -> LHsType
-- SpecTypeF LHsType -> LHsType
-- SpecType -> SpectypeF
-- distPara :: Corecursive t => Base t (t, a) -> (t, Base t a)
-- SpecTypeF ((t,) SpecType) -> (t,) (SpecTypeF SpecType)
specTypeToLHsType :: SpecType -> LHsType GhcPs
-- surprised that the type annotaiton is necessary
specTypeToLHsType =
  flip (ghylo (distPara @SpecType) distAna) (fmap pure . project) $ \case
    RVarF (RTV tv) _              -> nlHsTyVar (getRdrName tv)
    RFunF  _ (tin, tin') (_, tout) _
      | isClassType tin -> noLoc $ HsQualTy NoExt (noLoc [tin']) tout
      | otherwise -> nlHsFunTy tin' tout
    RImpFF _ (_, tin) (_, tout) _ -> nlHsFunTy tin tout
    RAllTF (ty_var_value -> (RTV tv)) (_, t) _ ->
      noLoc $ HsForAllTy NoExt (userHsTyVarBndrs noSrcSpan [getRdrName tv]) t
    RAllPF _ (_, ty)                    -> ty
    RAppF RTyCon { rtc_tc = tc } ts _ _ -> nlHsTyConApp
      (getRdrName tc)
      [ hst | (t, hst) <- ts, notExprArg t ]
     where
      notExprArg (RExprArg _) = False
      notExprArg _            = True
    RAllEF  _      _                (_, t) -> t
    RExF    _      _                (_, t) -> t
    RAppTyF (_, t) (RExprArg _, _ ) _      -> t
    RAppTyF (_, t) (_         , t') _      -> nlHsAppTy t t'
    RRTyF _ _ _ (_, t) -> t
    RHoleF _ -> noLoc $ HsWildCardTy NoExt
    RExprArgF _ -> todo Nothing "Oops, specTypeToLHsType doesn't know how to handle RExprArg"





-- toType (RApp (RTyCon {rtc_tc = c}) ts _ _)
--   = TyConApp c (toType <$> filter notExprArg ts)
--   where
--     notExprArg (RExprArg _) = False
--     notExprArg _            = True
