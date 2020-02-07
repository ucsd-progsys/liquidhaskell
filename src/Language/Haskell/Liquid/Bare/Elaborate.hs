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
import qualified Data.HashMap.Strict           as M
import qualified Data.HashSet                  as S
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
import           TysWiredIn                     ( boolTyCon
                                                , true_RDR
                                                )
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
import qualified Data.Maybe                    as Mb


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
type PartialSpecType = Free SpecTypeF ()

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
-- returning both expression since ghc adds unique id to the expressions
buildHsExpr :: LHsExpr GhcPs -> SpecType -> (LHsExpr GhcPs, [F.Symbol])
buildHsExpr res = para $ \case
  RFunF bind (tin, _) (_, bres@(res, bs)) _
    | isClassType tin
    -> bres
    | otherwise
    -> (mkHsLam [nlVarPat (symbolToRdrName varName bind)] res, bind : bs)
  RImpFF bind (tin, _) (_, bres@(res, bs)) _
    | isClassType tin
    -> bres
    | otherwise
    -> (mkHsLam [nlVarPat (symbolToRdrName varName bind)] res, bind : bs)
  RAllEF  _ _        (_, res) -> res
  RAllTF  _ (_, res) _        -> res
  RExF    _ _        (_, res) -> res
  RAppTyF _ (_, res) _        -> res
  RRTyF _ _ _ (_, res)        -> res
  _                           -> (res, [])

-- _:Semigroup a -> {x:a | x <> x == x} -> {y:a | y <> x == x <> y} -> {}
-- in gives [dict0]
-- out gives [dict1]

-- I wish there's a way to make this function polymorphic wrt to
-- tuples. microlens's Each seems to do exactly what I want..
-- buildDictBinderSubst :: [[F.Symbol]] -> Maybe _
-- bulidDictBinderSubst dbss =
--   case L.filter (not . null) dbss of
--     [] -> Nothing
--     [_] -> Nothing
--     (dbs:dbss') -> Just $
--       buildSubst $ zip dbs (L.transpose dbss')
--   where buildSubst 

renameDictBinder :: (F.Subable a) => [F.Symbol] -> [F.Symbol] -> a -> a
renameDictBinder []          _  = id
renameDictBinder _           [] = id
renameDictBinder canonicalDs ds = F.substa $ \x -> M.lookupDefault x x tbl
  where tbl = F.tracepp "TBL" $ M.fromList (zip ds canonicalDs)


canonicalizeDictBinder :: F.Subable a => [F.Symbol] -> [F.Symbol] -> a -> (a,[F.Symbol])
canonicalizeDictBinder [] bs' e' = (e',bs')
canonicalizeDictBinder bs [] e' = (e',bs)
canonicalizeDictBinder bs bs' e' = (renameDictBinder bs bs' e', bs)



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
      -- YL : Fix
  RFun bind tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
    -- the reft is never actually used by the child
    -- maybe i should enforce this information at the type level
    let partialFunTp =
          Free (RFunF bind (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
        partialTp' = partialTp >> partialFunTp :: PartialSpecType
    (eTin , bs ) <- elaborateSpecType partialTp coreToLogic tin
    (eTout, bs') <- elaborateSpecType partialTp' coreToLogic tout
    let
      buildRFunContTrivial
        | isClassType tin, dictBinder : bs0' <- bs' = do
          let (eToutRenamed, canonicalBinders) = canonicalizeDictBinder bs bs0' eTout
          pure
            ( F.notracepp "RFunTrivial0" $ RFun dictBinder
                   eTin
                   eToutRenamed
                   ureft
            , canonicalBinders
            )
        | otherwise = do
          let (eToutRenamed, canonicalBinders) = canonicalizeDictBinder bs bs' eTout
          pure
            ( F.notracepp "RFunTrivial1" $ RFun bind eTin eToutRenamed ureft
            , canonicalBinders
            )
      buildRFunCont bs'' ee
        | isClassType tin, dictBinder : bs0' <- bs' = do
          let (eToutRenamed, canonicalBinders) = canonicalizeDictBinder bs bs0' eTout
              eeRenamed = renameDictBinder canonicalBinders bs'' ee
          pure
            ( RFun dictBinder
                   eTin
                   eToutRenamed
                   (MkUReft (F.Reft (vv, eeRenamed)) p)
            , canonicalBinders
            )
        | otherwise = do
          let (eToutRenamed, canonicalBinders) = canonicalizeDictBinder bs bs' eTout
              eeRenamed = renameDictBinder canonicalBinders bs'' ee
          pure
            ( RFun bind eTin eToutRenamed (MkUReft (F.Reft (vv, eeRenamed)) p)
            , canonicalBinders
            )
    elaborateReft (reft, t)
                  buildRFunContTrivial
                  buildRFunCont

      -- (\bs' ee | isClassType tin -> do
      --    let eeRenamed = renameDictBinder canonicalBinders bs' ee
      --    pure (RFun bind eTin eToutRenamed (MkUReft (F.Reft (vv, eeRenamed)) p), bs')
      -- )
  -- YL: implicit dictionary param doesn't seem possible..
  RImpF bind tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
    let partialFunTp =
          Free (RImpFF bind (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
        partialTp' = partialTp >> partialFunTp :: PartialSpecType
    (eTin , bs ) <- elaborateSpecType partialTp' coreToLogic tin
    (eTout, bs') <- elaborateSpecType partialTp' coreToLogic tout
    let (eToutRenamed, canonicalBinders) = canonicalizeDictBinder bs bs' eTout
    
    -- eTin and eTout might have different dictionary names
    -- need to do a substitution to make the reference to dictionaries consistent
    -- if isClassType eTin
    elaborateReft
      (reft, t)
      (pure (RImpF bind eTin eToutRenamed ureft, canonicalBinders))
      (\bs'' ee -> do
        let eeRenamed = renameDictBinder canonicalBinders bs'' ee
        pure (RImpF bind eTin eTout (MkUReft (F.Reft (vv, eeRenamed)) p), bs')
      )
  -- support for RankNTypes/ref
  RAllT (RTVar tv ty) tout ureft@(MkUReft ref@(F.Reft (vv, _oldE)) p) -> do
    (eTout, bs) <- elaborateSpecType
      (partialTp >> Free (RAllTF (RTVar tv ty) (pure ()) ureft))
      coreToLogic
      tout
    elaborateReft
      (ref, RVar tv mempty)
      (pure (RAllT (RTVar tv ty) eTout ureft, bs))
      (\bs' ee ->
        let (eeRenamed, canonicalBinders) = canonicalizeDictBinder bs bs' ee in
        pure (RAllT (RTVar tv ty) eTout (MkUReft (F.Reft (vv, eeRenamed)) p), canonicalBinders)
      )
    -- pure (RAllT (RTVar tv ty) eTout ref, bts')
  -- todo: might as well print an error message?
  RAllP pvbind tout -> do
    (eTout, bts') <- elaborateSpecType
      (partialTp >> Free (RAllPF pvbind (pure ())))
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
    (eArg, bs ) <- elaborateSpecType partialTp coreToLogic arg
    (eRes, bs') <- elaborateSpecType partialTp coreToLogic res
    let (eResRenamed, canonicalBinders) = canonicalizeDictBinder bs bs' eRes
    elaborateReft
      (reft, t)
      (pure (RAppTy eArg eResRenamed ureft, canonicalBinders))
      (\bs'' ee ->
         let eeRenamed = renameDictBinder canonicalBinders bs'' ee in
         pure (RAppTy eArg eResRenamed (MkUReft (F.Reft (vv, eeRenamed)) p), canonicalBinders))
  RAllE bind allarg ty -> do
    (eAllarg, bs ) <- elaborateSpecType partialTp coreToLogic allarg
    (eTy    , bs') <- elaborateSpecType partialTp coreToLogic ty
    pure (RAllE bind eAllarg eTy, bs)
  REx bind allarg ty -> do
    (eAllarg, bs ) <- elaborateSpecType partialTp coreToLogic allarg
    (eTy    , bs') <- elaborateSpecType partialTp coreToLogic ty
    pure (RAllE bind eAllarg eTy, bs)
  -- YL: might need to filter RExprArg out and replace RHole with ghc wildcard
  -- in the future
  RExprArg _   -> impossible Nothing "RExprArg should not appear here"
  RHole    _   -> impossible Nothing "RHole should not appear here"
  RRTy _ _ _ _ -> todo Nothing ("Not sure how to elaborate RRTy" ++ F.showpp t)
 where
  boolType = RApp (RTyCon boolTyCon [] def) [] [] mempty :: SpecType
  elaborateReft
    :: (F.PPrint a) => (F.Reft, SpecType) -> Ghc a -> ([F.Symbol] -> F.Expr -> Ghc a) -> Ghc a
  elaborateReft (reft@(F.Reft (vv, e)), vvTy) trivial nonTrivialCont =
    if isTrivial reft
      then trivial
      else do
-- liftIO $ putStrLn query
        let
          querySpecType =
            plugType (rFun vv vvTy boolType) partialTp :: SpecType
          (hsExpr, origBinders) =
            buildHsExpr (fixExprToHsExpr e) querySpecType :: ( LHsExpr GhcPs
              , [F.Symbol]
              )
          exprWithTySigs =
            GM.notracePpr "exprWithTySigs" $ noLoc $ ExprWithTySig
              ( mkLHsSigWcType
              $ specTypeToLHsType (F.notracepp "querySpecType" querySpecType)
              )
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
            let
              eeWithLams =
                coreToLogic (GM.notracePpr "eeWithLamsCore" eeWithLamsCore)
              (bs', ee) = F.notracepp "grabLams" $ grabLams ([], eeWithLams)
              (dictbs, nondictbs) =
                L.partition (F.isPrefixOfSym (F.symbol "$d")) bs'
          -- invariant: length nondictbs == length origBinders
              subst = if length nondictbs == length origBinders
                then F.notracepp "SUBST" $ zip (L.reverse nondictbs) origBinders
                else panic
                  Nothing
                  "Oops, Ghc gave back more/less binders than I expected"
            ret <- nonTrivialCont
                   dictbs
                   (F.notracepp "nonTrivialContEE" $ F.substa (\x -> Mb.fromMaybe x (L.lookup x subst)) ee)  -- (GM.dropModuleUnique <$> bs')
            pure (F.notracepp "result" ret)
                           -- (F.substa )
  isTrivial :: F.Reft -> Bool
  isTrivial (F.Reft (_, F.PTrue)) = True
  isTrivial _ = False
  
  grabLams :: ([F.Symbol], F.Expr) -> ([F.Symbol], F.Expr)
  grabLams (bs, F.ELam (b, _) e) = grabLams (b : bs, e)
  grabLams bse                   = bse
  -- dropBinderUnique :: [F.Symbol] -> F.Expr -> F.Expr
  -- dropBinderUnique binders = F.notracepp "ElaboratedExpr"
  --   . F.substa (\x -> if L.elem x binders then GM.dropModuleUnique x else x)




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
fixExprToHsExpr (F.ECst e0 _    ) = fixExprToHsExpr e0
fixExprToHsExpr (F.PAnd []      ) = nlHsVar true_RDR
fixExprToHsExpr (F.PAnd (e : es)) = L.foldr f (fixExprToHsExpr e) es
  where f x acc = mkHsApp (mkHsApp (nlHsVar and_RDR) (fixExprToHsExpr x)) acc
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


specTypeToLHsType :: SpecType -> LHsType GhcPs
-- surprised that the type application is necessary
specTypeToLHsType =
  flip (ghylo (distPara @SpecType) distAna) (fmap pure . project) $ \case
    RVarF (RTV tv) _ -> nlHsTyVar (getRdrName tv)
    RFunF _ (tin, tin') (_, tout) _
      | isClassType tin -> noLoc $ HsQualTy NoExt (noLoc [tin']) tout
      | otherwise       -> nlHsFunTy tin' tout
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
    RRTyF _ _ _ (_, t)                     -> t
    RHoleF _                               -> noLoc $ HsWildCardTy NoExt
    RExprArgF _ ->
      todo Nothing "Oops, specTypeToLHsType doesn't know how to handle RExprArg"





-- toType (RApp (RTyCon {rtc_tc = c}) ts _ _)
--   = TyConApp c (toType <$> filter notExprArg ts)
--   where
--     notExprArg (RExprArg _) = False
--     notExprArg _            = True
