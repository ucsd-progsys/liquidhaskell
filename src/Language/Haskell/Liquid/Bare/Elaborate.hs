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
  , buildSimplifier
  )
where

import qualified Language.Fixpoint.Types       as F
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Language.Haskell.Liquid.Types.Visitors
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType
                                                ( )
import qualified Data.List                     as L
import qualified Data.HashMap.Strict           as M
import qualified Data.HashSet                  as S
import           Control.Monad.Free
import           Data.Functor.Foldable
import           Data.Char                      ( isUpper )
import           GHC
import           GhcPlugins                     ( isDFunId )
import           OccName
import           FastString
import           CoreSyn
import           PrelNames
import qualified Outputable                    as O
import           TysWiredIn                     ( boolTyCon
                                                , true_RDR
                                                )
import           ErrUtils
import           RdrName
import           BasicTypes
import           Data.Default                   ( def )
import qualified Data.Maybe                    as Mb
import           CoreSubst               hiding ( substExpr )
import           SimplCore
import           CoreMonad
import           CoreFVs                        ( exprFreeVarsList )
import           VarEnv                         ( lookupVarEnv
                                                , lookupInScope
                                                )
import           CoreUtils                      ( mkTick )

lookupIdSubstAll :: O.SDoc -> Subst -> Id -> CoreExpr
lookupIdSubstAll doc (Subst in_scope ids _ _) v
  | Just e <- lookupVarEnv ids v        = e
  | Just v' <- lookupInScope in_scope v = Var v'
  | otherwise                           = Var v
        -- Vital! See Note [Extending the Subst]
  -- | otherwise = WARN( True, text "CoreSubst.lookupIdSubst" <+> doc <+> ppr v
  --                           $$ ppr in_scope)

substExprAll :: O.SDoc -> Subst -> CoreExpr -> CoreExpr
substExprAll doc subst orig_expr = subst_expr_all doc subst orig_expr


subst_expr_all :: O.SDoc -> Subst -> CoreExpr -> CoreExpr
subst_expr_all doc subst expr = go expr
 where
  go (Var v) = lookupIdSubstAll (doc O.$$ O.text "subst_expr_all") subst v
  go (Type     ty      ) = Type (substTy subst ty)
  go (Coercion co      ) = Coercion (substCo subst co)
  go (Lit      lit     ) = Lit lit
  go (App  fun     arg ) = App (go fun) (go arg)
  go (Tick tickish e   ) = mkTick (substTickish subst tickish) (go e)
  go (Cast e       co  ) = Cast (go e) (substCo subst co)
     -- Do not optimise even identity coercions
     -- Reason: substitution applies to the LHS of RULES, and
     --         if you "optimise" an identity coercion, you may
     --         lose a binder. We optimise the LHS of rules at
     --         construction time

  go (Lam  bndr    body) = Lam bndr' (subst_expr_all doc subst' body)
    where (subst', bndr') = substBndr subst bndr

  go (Let bind body) = Let bind' (subst_expr_all doc subst' body)
    where (subst', bind') = substBind subst bind

  go (Case scrut bndr ty alts) = Case (go scrut)
                                      bndr'
                                      (substTy subst ty)
                                      (map (go_alt subst') alts)
    where (subst', bndr') = substBndr subst bndr

  go_alt subst (con, bndrs, rhs) = (con, bndrs', subst_expr_all doc subst' rhs)
    where (subst', bndrs') = substBndrs subst bndrs


substLet :: CoreExpr -> CoreExpr
substLet (Lam b body) = Lam b (substLet body)
substLet (Let b body)
  | NonRec x e <- b = substLet
    (substExprAll O.empty (extendIdSubst emptySubst x e) body)
  | otherwise = Let b (substLet body)
substLet e = e


buildDictSubst :: CoreProgram -> Subst
buildDictSubst = cata f
 where
  f Nil = emptySubst
  f (Cons b s)
    | NonRec x e <- b, isDFunId x || isDictonaryId x = extendIdSubst s x e
    | otherwise = s

buildSimplifier :: CoreProgram -> CoreExpr -> Ghc CoreExpr
buildSimplifier cbs e = do
  df <- getDynFlags
  liftIO $ simplifyExpr df e'
 where
  -- fvs = fmap (\x -> (x, getUnique x, isLocalId x))  (freeVars mempty e)
  dictSubst = buildDictSubst cbs
  e'        = substExprAll O.empty dictSubst e


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
-- returning both expressions and binders since ghc adds unique id to the expressions

collectSpecTypeBinders :: SpecType -> [F.Symbol]
collectSpecTypeBinders = para $ \case
  RFunF bind (tin, _) (_, bs) _ | isClassType tin -> bs
                                | otherwise       -> bind : bs
  RImpFF bind (tin, _) (_, bs) _ | isClassType tin -> bs
                                 | otherwise       -> bind : bs
  RAllEF  b _        (_, res) -> b : res
  RAllTF  _ (_, res) _        -> res
  RExF    b _        (_, res) -> b : res
  RAppTyF _ (_, res) _        -> res
  RRTyF _ _ _ (_, res)        -> res
  _                           -> []

-- really should be fused with collectBinders. However, we need the binders
-- to correctly convert fixpoint expressions to ghc expressions because of
-- namespace related issues (whether the symbol denotes a varName or a datacon)
buildHsExpr :: LHsExpr GhcPs -> SpecType -> LHsExpr GhcPs
buildHsExpr res = para $ \case
  RFunF bind (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (varSymbolToRdrName bind)] res
  RImpFF bind (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (varSymbolToRdrName bind)] res
  RAllEF  _ _        (_, res) -> res
  RAllTF  _ (_, res) _        -> res
  RExF    _ _        (_, res) -> res
  RAppTyF _ (_, res) _        -> res
  RRTyF _ _ _ (_, res)        -> res
  _                           -> res



canonicalizeDictBinder
  :: F.Subable a => [F.Symbol] -> (a, [F.Symbol]) -> (a, [F.Symbol])
canonicalizeDictBinder [] (e', bs') = (e', bs')
canonicalizeDictBinder bs (e', [] ) = (e', bs)
canonicalizeDictBinder bs (e', bs') = (renameDictBinder bs bs' e', bs)
 where
  renameDictBinder :: (F.Subable a) => [F.Symbol] -> [F.Symbol] -> a -> a
  renameDictBinder []          _  = id
  renameDictBinder _           [] = id
  renameDictBinder canonicalDs ds = F.substa $ \x -> M.lookupDefault x x tbl
    where tbl = F.notracepp "TBL" $ M.fromList (zip ds canonicalDs)

elaborateSpecType
  :: (CoreExpr -> F.Expr)
  -> (CoreExpr -> Ghc CoreExpr)
  -> SpecType
  -> Ghc SpecType
elaborateSpecType coreToLogic simplifier t = do
  (t', xs) <- elaborateSpecType' (pure ()) coreToLogic simplifier t
  case xs of
    _ : _ -> panic
      Nothing
      "elaborateSpecType: invariant broken. substitution list for dictionary is not completely consumed"
    _ -> pure t'

elaborateSpecType'
  :: PartialSpecType
  -> (CoreExpr -> F.Expr) -- core to logic
  -> (CoreExpr -> Ghc CoreExpr)
  -> SpecType
  -> Ghc (SpecType, [F.Symbol]) -- binders for dictionaries
                   -- should have returned Maybe [F.Symbol]
elaborateSpecType' partialTp coreToLogic simplify t =
  case F.notracepp "elaborateSpecType'" t of
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
      (eTin , bs ) <- elaborateSpecType' partialTp coreToLogic simplify tin
      (eTout, bs') <- elaborateSpecType' partialTp' coreToLogic simplify tout
      let buildRFunContTrivial
            | isClassType tin, dictBinder : bs0' <- bs' = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs0')
              pure
                ( F.notracepp "RFunTrivial0"
                  $ RFun dictBinder eTin eToutRenamed ureft
                , canonicalBinders
                )
            | otherwise = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs')
              pure
                ( F.notracepp "RFunTrivial1" $ RFun bind eTin eToutRenamed ureft
                , canonicalBinders
                )
          buildRFunCont bs'' ee
            | isClassType tin, dictBinder : bs0' <- bs' = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs0')
                  (eeRenamed, canonicalBinders') =
                    canonicalizeDictBinder canonicalBinders (ee, bs'')
              pure
                ( RFun dictBinder
                       eTin
                       eToutRenamed
                       (MkUReft (F.Reft (vv, eeRenamed)) p)
                , canonicalBinders'
                )
            | otherwise = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs')
                  (eeRenamed, canonicalBinders') =
                    canonicalizeDictBinder canonicalBinders (ee, bs'')
              pure
                ( RFun bind
                       eTin
                       eToutRenamed
                       (MkUReft (F.Reft (vv, eeRenamed)) p)
                , canonicalBinders'
                )
      elaborateReft (reft, t) buildRFunContTrivial buildRFunCont

        -- (\bs' ee | isClassType tin -> do
        --    let eeRenamed = renameDictBinder canonicalBinders bs' ee
        --    pure (RFun bind eTin eToutRenamed (MkUReft (F.Reft (vv, eeRenamed)) p), bs')
        -- )
    -- YL: implicit dictionary param doesn't seem possible..
    RImpF bind tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
      let partialFunTp =
            Free (RImpFF bind (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
          partialTp' = partialTp >> partialFunTp :: PartialSpecType
      (eTin , bs ) <- elaborateSpecType' partialTp' coreToLogic simplify tin
      (eTout, bs') <- elaborateSpecType' partialTp' coreToLogic simplify tout
      let (eToutRenamed, canonicalBinders) =
            canonicalizeDictBinder bs (eTout, bs')

      -- eTin and eTout might have different dictionary names
      -- need to do a substitution to make the reference to dictionaries consistent
      -- if isClassType eTin
      elaborateReft
        (reft, t)
        (pure (RImpF bind eTin eToutRenamed ureft, canonicalBinders))
        (\bs'' ee -> do
          let (eeRenamed, canonicalBinders') =
                canonicalizeDictBinder canonicalBinders (ee, bs'')
          pure
            ( RImpF bind eTin eTout (MkUReft (F.Reft (vv, eeRenamed)) p)
            , canonicalBinders'
            )
        )
    -- support for RankNTypes/ref
    RAllT (RTVar tv ty) tout ureft@(MkUReft ref@(F.Reft (vv, _oldE)) p) -> do
      (eTout, bs) <- elaborateSpecType'
        (partialTp >> Free (RAllTF (RTVar tv ty) (pure ()) ureft))
        coreToLogic
        simplify
        tout
      elaborateReft
        (ref, RVar tv mempty)
        (pure (RAllT (RTVar tv ty) eTout ureft, bs))
        (\bs' ee ->
          let (eeRenamed, canonicalBinders) =
                  canonicalizeDictBinder bs (ee, bs')
          in  pure
                ( RAllT (RTVar tv ty) eTout (MkUReft (F.Reft (vv, eeRenamed)) p)
                , canonicalBinders
                )
        )
      -- pure (RAllT (RTVar tv ty) eTout ref, bts')
    -- todo: might as well print an error message?
    RAllP pvbind tout -> do
      (eTout, bts') <- elaborateSpecType'
        (partialTp >> Free (RAllPF pvbind (pure ())))
        coreToLogic
        simplify
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
      (eArg, bs ) <- elaborateSpecType' partialTp coreToLogic simplify arg
      (eRes, bs') <- elaborateSpecType' partialTp coreToLogic simplify res
      let (eResRenamed, canonicalBinders) =
            canonicalizeDictBinder bs (eRes, bs')
      elaborateReft
        (reft, t)
        (pure (RAppTy eArg eResRenamed ureft, canonicalBinders))
        (\bs'' ee ->
          let (eeRenamed, canonicalBinders') =
                  canonicalizeDictBinder canonicalBinders (ee, bs'')
          in  pure
                ( RAppTy eArg eResRenamed (MkUReft (F.Reft (vv, eeRenamed)) p)
                , canonicalBinders'
                )
        )
    -- todo: Existential support
    RAllE bind allarg ty -> do
      (eAllarg, bs ) <- elaborateSpecType' partialTp coreToLogic simplify allarg
      (eTy    , bs') <- elaborateSpecType' partialTp coreToLogic simplify ty
      let (eTyRenamed, canonicalBinders) = canonicalizeDictBinder bs (eTy, bs')
      pure (RAllE bind eAllarg eTyRenamed, canonicalBinders)
    REx bind allarg ty -> do
      (eAllarg, bs ) <- elaborateSpecType' partialTp coreToLogic simplify allarg
      (eTy    , bs') <- elaborateSpecType' partialTp coreToLogic simplify ty
      let (eTyRenamed, canonicalBinders) = canonicalizeDictBinder bs (eTy, bs')
      pure (REx bind eAllarg eTyRenamed, canonicalBinders)
    -- YL: might need to filter RExprArg out and replace RHole with ghc wildcard
    -- in the future
    RExprArg _ -> impossible Nothing "RExprArg should not appear here"
    RHole    _ -> impossible Nothing "RHole should not appear here"
    RRTy _ _ _ _ ->
      todo Nothing ("Not sure how to elaborate RRTy" ++ F.showpp t)
 where
  boolType = RApp (RTyCon boolTyCon [] def) [] [] mempty :: SpecType
  elaborateReft
    :: (F.PPrint a)
    => (F.Reft, SpecType)
    -> Ghc a
    -> ([F.Symbol] -> F.Expr -> Ghc a)
    -> Ghc a
  elaborateReft (reft@(F.Reft (vv, e)), vvTy) trivial nonTrivialCont =
    if isTrivial reft
      then trivial
      else do
-- liftIO $ putStrLn query
        let
          querySpecType =
            plugType (rFun vv vvTy boolType) partialTp :: SpecType
          origBinders = collectSpecTypeBinders querySpecType
          hsExpr =
            buildHsExpr (fixExprToHsExpr (S.fromList origBinders) e)
                        querySpecType :: LHsExpr GhcPs
          exprWithTySigs =
            GM.notracePpr "exprWithTySigs" $ noLoc $ ExprWithTySig
              (mkLHsSigWcType $ specTypeToLHsType
                (F.notracepp "querySpecType" querySpecType)
              )
              hsExpr :: LHsExpr GhcPs
        (msgs, mbExpr) <- GM.elaborateHsExprInst exprWithTySigs
        case mbExpr of
          Nothing -> panic
            Nothing
            (  "Ghc is unable to elaborate the expression: "
            ++ GM.showPpr exprWithTySigs
            ++ "\n"
            ++ GM.showPpr
                 (GM.showSDoc $ O.hcat (pprErrMsgBagWithLoc (snd msgs)))
            )
          Just eeWithLamsCore -> do
            let (_, bs, ee) = GM.notracePpr "collectTyAndValBinders"
                  $ collectTyAndValBinders (substLet eeWithLamsCore)
            ee' <- simplify ee
            let
              eeFix = coreToLogic (GM.notracePpr "eeWithLamsCore" ee')
              -- (bs', ee) = F.notracepp "grabLams" $ grabLams ([], eeWithLams)
              (dictbs, nondictbs) =
                L.partition (F.isPrefixOfSym (F.symbol "$d")) (fmap F.symbol bs)
          -- invariant: length nondictbs == length origBinders
              subst = if length nondictbs == length origBinders
                then F.notracepp "SUBST" $ zip nondictbs origBinders
                else panic
                  Nothing
                  (  "Oops, Ghc gave back more/less binders than I expected:"
                  ++ F.showpp nondictbs
                  ++ "  "
                  ++ F.showpp dictbs
                  )
            ret <- nonTrivialCont
              (L.reverse dictbs)
              (F.notracepp "nonTrivialContEE" . eliminateEta $ F.substa
                (\x -> Mb.fromMaybe x (L.lookup x subst))
                eeFix
              )  -- (GM.dropModuleUnique <$> bs')
            pure (F.notracepp "result" ret)
                           -- (F.substa )
  isTrivial :: F.Reft -> Bool
  isTrivial (F.Reft (_, F.PTrue)) = True
  isTrivial _                     = False

  grabLams :: ([F.Symbol], F.Expr) -> ([F.Symbol], F.Expr)
  grabLams (bs, F.ELam (b, _) e) = grabLams (b : bs, e)
  grabLams bse                   = bse
  -- dropBinderUnique :: [F.Symbol] -> F.Expr -> F.Expr
  -- dropBinderUnique binders = F.notracepp "ElaboratedExpr"
  --   . F.substa (\x -> if L.elem x binders then GM.dropModuleUnique x else x)




-- | Embed fixpoint expressions into parsed haskell expressions.
--   It allows us to bypass the GHC parser and use arbitrary symbols
--   for identifiers (compared to using the string API)
fixExprToHsExpr :: S.HashSet F.Symbol -> F.Expr -> LHsExpr GhcPs
fixExprToHsExpr env (F.ECon c) = constantToHsExpr c
fixExprToHsExpr env (F.EVar x) = nlHsVar (symbolToRdrName env x)
fixExprToHsExpr env (F.EApp e0 e1) =
  mkHsApp (fixExprToHsExpr env e0) (fixExprToHsExpr env e1)
fixExprToHsExpr env (F.ENeg e) =
  mkHsApp (nlHsVar (nameRdrName negateName)) (fixExprToHsExpr env e)

fixExprToHsExpr env (F.EBin bop e0 e1) = mkHsApp
  (mkHsApp (bopToHsExpr bop) (fixExprToHsExpr env e0))
  (fixExprToHsExpr env e1)
fixExprToHsExpr env (F.EIte p e0 e1) = nlHsIf (fixExprToHsExpr env p)
                                              (fixExprToHsExpr env e0)
                                              (fixExprToHsExpr env e1)

-- FIXME: convert sort to HsType
fixExprToHsExpr env (F.ECst e0 _    ) = fixExprToHsExpr env e0
-- fixExprToHsExpr env (F.PAnd []      ) = nlHsVar true_RDR
fixExprToHsExpr env (F.PAnd []      ) = nlHsVar true_RDR
fixExprToHsExpr env (F.PAnd (e : es)) = L.foldr f (fixExprToHsExpr env e) es
 where
  f x acc = mkHsApp (mkHsApp (nlHsVar and_RDR) (fixExprToHsExpr env x)) acc

-- This would work in the latest commit
-- fixExprToHsExpr env (F.PAnd es  ) = mkHsApp
--   (nlHsVar (varQual_RDR dATA_FOLDABLE (fsLit "and")))
--   (nlList $ fixExprToHsExpr env <$> es)
fixExprToHsExpr env (F.POr es) = mkHsApp
  (nlHsVar (varQual_RDR dATA_FOLDABLE (fsLit "or")))
  (nlList $ fixExprToHsExpr env <$> es)
fixExprToHsExpr env (F.PIff e0 e1) = mkHsApp
  (mkHsApp (nlHsVar (mkVarUnqual (mkFastString "<=>"))) (fixExprToHsExpr env e0)
  )
  (fixExprToHsExpr env e1)
fixExprToHsExpr env (F.PNot e) =
  mkHsApp (nlHsVar not_RDR) (fixExprToHsExpr env e)
fixExprToHsExpr env (F.PAtom brel e0 e1) = mkHsApp
  (mkHsApp (brelToHsExpr brel) (fixExprToHsExpr env e0))
  (fixExprToHsExpr env e1)
fixExprToHsExpr env (F.PImp e0 e1) = mkHsApp
  (mkHsApp (nlHsVar (mkVarUnqual (mkFastString "==>"))) (fixExprToHsExpr env e0)
  )
  (fixExprToHsExpr env e1)

fixExprToHsExpr env e =
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

symbolToRdrNameNs :: NameSpace -> F.Symbol -> RdrName
symbolToRdrNameNs ns x
  | F.isNonSymbol modName = mkUnqual ns (mkFastString (F.symbolString s))
  | otherwise = mkQual
    ns
    (mkFastString (F.symbolString modName), mkFastString (F.symbolString s))
  where (modName, s) = GM.splitModuleName x


varSymbolToRdrName :: F.Symbol -> RdrName
varSymbolToRdrName = symbolToRdrNameNs varName


-- don't use this function...
symbolToRdrName :: S.HashSet F.Symbol -> F.Symbol -> RdrName
symbolToRdrName env x
  | F.isNonSymbol modName = mkUnqual ns (mkFastString (F.symbolString s))
  | otherwise = mkQual
    ns
    (mkFastString (F.symbolString modName), mkFastString (F.symbolString s))
 where
  (modName, s) = GM.splitModuleName x
  ns | not (S.member x env), Just (c, _) <- F.unconsSym s, isUpper c = dataName
     | otherwise = varName


specTypeToLHsType :: SpecType -> LHsType GhcPs
-- surprised that the type application is necessary
specTypeToLHsType =
  flip (ghylo (distPara @SpecType) distAna) (fmap pure . project) $ \case
    RVarF (RTV tv) _ -> nlHsTyVar (symbolToRdrNameNs tvName (F.symbol tv)) -- (getRdrName tv)
    RFunF _ (tin, tin') (_, tout) _
      | isClassType tin -> noLoc $ HsQualTy NoExt (noLoc [tin']) tout
      | otherwise       -> nlHsFunTy tin' tout
    RImpFF _ (_, tin) (_, tout) _              -> nlHsFunTy tin tout
    RAllTF (ty_var_value -> (RTV tv)) (_, t) _ -> noLoc $ HsForAllTy
      NoExt
      (userHsTyVarBndrs noSrcSpan
                        [-- getRdrName tv
                         (symbolToRdrNameNs tvName (F.symbol tv))]
      )
      t
    RAllPF _ (_, ty)                    -> ty
    RAppF RTyCon { rtc_tc = tc } ts _ _ -> nlHsTyConApp
      (getRdrName tc)
      [ hst | (t, hst) <- ts, notExprArg t ]
     where
      notExprArg (RExprArg _) = False
      notExprArg _            = True
    RAllEF _ (_, tin) (_, tout) -> nlHsFunTy tin tout
    RExF   _ (_, tin) (_, tout) -> nlHsFunTy tin tout
    -- impossible
    RAppTyF _ (RExprArg _, _) _ ->
      impossible Nothing "RExprArg should not appear here"
    RAppTyF (_, t) (_, t') _ -> nlHsAppTy t t'
    -- YL: todo..
    RRTyF _ _ _ (_, t)       -> t
    RHoleF _                 -> noLoc $ HsWildCardTy NoExt
    RExprArgF _ ->
      todo Nothing "Oops, specTypeToLHsType doesn't know how to handle RExprArg"

-- the core expression returned by ghc might be eta-expanded
-- we need to do elimination so Pred doesn't contain lambda terms
eliminateEta :: F.Expr -> F.Expr
eliminateEta (F.EApp e0 e1) = F.EApp (eliminateEta e0) (eliminateEta e1)
eliminateEta (F.ENeg e    ) = F.ENeg (eliminateEta e)
eliminateEta (F.EBin bop e0 e1) =
  F.EBin bop (eliminateEta e0) (eliminateEta e1)
eliminateEta (F.EIte e0 e1 e2) =
  F.EIte (eliminateEta e0) (eliminateEta e1) (eliminateEta e2)
eliminateEta (F.ECst e0 s) = F.ECst (eliminateEta e0) s
eliminateEta (F.ELam (x, t) body)
  | F.EApp e0 (F.EVar x') <- ebody, x == x' && notElem x (F.syms e0) = e0
  | otherwise = F.ELam (x, t) ebody
  where ebody = eliminateEta body
eliminateEta (F.PAnd es   ) = F.PAnd (eliminateEta <$> es)
eliminateEta (F.POr  es   ) = F.POr (eliminateEta <$> es)
eliminateEta (F.PNot e    ) = F.PNot (eliminateEta e)
eliminateEta (F.PImp e0 e1) = F.PImp (eliminateEta e0) (eliminateEta e1)
eliminateEta (F.PAtom brel e0 e1) =
  F.PAtom brel (eliminateEta e0) (eliminateEta e1)
eliminateEta e = e
