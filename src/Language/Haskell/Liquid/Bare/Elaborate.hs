{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE ExplicitForAll            #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE CPP                       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

{-# OPTIONS_GHC -Wno-dodgy-imports #-} -- TODO(#1913): Fix import of Data.Functor.Foldable.Fix
{-# OPTIONS_GHC -Wno-unused-top-binds #-} -- TODO(#1914): Is RTypeF even used?

-- | This module uses GHC API to elaborate the resolves expressions

-- TODO: Genearlize to BareType and replace the existing resolution mechanisms

module Language.Haskell.Liquid.Bare.Elaborate
  ( fixExprToHsExpr
  , elaborateSpecType
  -- , buildSimplifier
  )
where

import qualified Language.Fixpoint.Types       as F
-- import           Control.Arrow
import           Language.Haskell.Liquid.GHC.API hiding (panic, varName)
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType
                                                ( ofType )
import qualified Data.List                     as L
import qualified Data.HashMap.Strict           as M
import qualified Data.HashSet                  as S
import           Control.Monad.Free
#if MIN_VERSION_recursion_schemes(5,2,0)
import           Data.Fix                      hiding (hylo)
import           Data.Functor.Foldable         hiding (Fix)
#else
import           Data.Functor.Foldable
#endif

-- import           TcRnMonad (TcRn)
import           Data.Char                      ( isUpper )
#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
import           GHC.Types.Name.Occurrence
#else
import           OccName
#endif
-- import           GHC
-- import           GhcPlugins                     ( isDFunId
--                                                 )

-- import           FastString
-- import           CoreSyn
-- import           PrelNames
import qualified Language.Haskell.Liquid.GHC.API as Ghc
                                                (noExtField)

-- import qualified Outputable                    as O
-- import           TysWiredIn                     ( boolTyCon
--                                                 , true_RDR
--                                                 )
-- import           RdrName
-- import           BasicTypes
import           Data.Default                   ( def )
import qualified Data.Maybe                    as Mb
-- import qualified CoreUtils                     as Utils


-- TODO: make elaboration monadic so typeclass names are unified to something
-- that is generated in advance. This can greatly simplify the implementation
-- of elaboration

-- the substitution code is meant to inline dictionary functions
-- but does not seem to work
-- lookupIdSubstAll :: O.SDoc -> M.HashMap Id CoreExpr -> Id -> CoreExpr
-- lookupIdSubstAll doc env v | Just e <- M.lookup v env = e
--                            | otherwise                = Var v
--         -- Vital! See Note [Extending the Subst]
--   -- | otherwise = WARN( True, text "CoreSubst.lookupIdSubst" <+> doc <+> ppr v
--   --                           $$ ppr in_scope)

-- substExprAll :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
-- substExprAll doc subst orig_expr = subst_expr_all doc subst orig_expr


-- subst_expr_all :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
-- subst_expr_all doc subst expr = go expr
--  where
--   go (Var v) = lookupIdSubstAll (doc O.$$ O.text "subst_expr_all") subst v
--   go (Type     ty      ) = Type ty
--   go (Coercion co      ) = Coercion co
--   go (Lit      lit     ) = Lit lit
--   go (App  fun     arg ) = App (go fun) (go arg)
--   go (Tick tickish e   ) = Tick tickish (go e)
--   go (Cast e       co  ) = Cast (go e) co
--      -- Do not optimise even identity coercions
--      -- Reason: substitution applies to the LHS of RULES, and
--      --         if you "optimise" an identity coercion, you may
--      --         lose a binder. We optimise the LHS of rules at
--      --         construction time

--   go (Lam  bndr    body) = Lam bndr (subst_expr_all doc subst body)

--   go (Let  bind    body) = Let (mapBnd go bind) (subst_expr_all doc subst body)

--   go (Case scrut bndr ty alts) =
--     Case (go scrut) bndr ty (map (go_alt subst) alts)

--   go_alt subst (con, bndrs, rhs) = (con, bndrs, subst_expr_all doc subst rhs)


-- mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
-- mapBnd f (NonRec b e) = NonRec b (f e)
-- mapBnd f (Rec bs    ) = Rec (map (second f) bs)

-- -- substLet :: CoreExpr -> CoreExpr
-- -- substLet (Lam b body) = Lam b (substLet body)
-- -- substLet (Let b body)
-- --   | NonRec x e <- b = substLet
-- --     (substExprAll O.empty (extendIdSubst emptySubst x e) body)
-- --   | otherwise = Let b (substLet body)
-- -- substLet e = e


-- buildDictSubst :: CoreProgram -> M.HashMap Id CoreExpr
-- buildDictSubst = cata f
--  where
--   f Nil = M.empty
--   f (Cons b s) | NonRec x e <- b, isDFunId x -- || isDictonaryId x
--                                              = M.insert x e s
--                | otherwise                   = s

-- buildSimplifier :: CoreProgram -> CoreExpr -> TcRn CoreExpr
-- buildSimplifier cbs e = pure e-- do
 --  df <- getDynFlags
 --  liftIO $ simplifyExpr (df `gopt_set` Opt_SuppressUnfoldings) e'
 -- where
 --  -- fvs = fmap (\x -> (x, getUnique x, isLocalId x))  (freeVars mempty e)
 --  dictSubst = buildDictSubst cbs
 --  e'        = substExprAll O.empty dictSubst e


-- | Base functor of RType
data RTypeF c tv r f
  = RVarF {
      rtf_var    :: !tv
    , rtf_reft   :: !r
    }

  | RFunF  {
      rtf_bind   :: !F.Symbol
    , rtf_rinfo  :: !RFInfo
    , rtf_in     :: !f
    , rtf_out    :: !f
    , rtf_reft   :: !r
    }

  | RImpFF  {
      rtf_bind   :: !F.Symbol
    , rtd_rinfo  :: !RFInfo
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
  project (RFun  bind i tin tout reft) = RFunF bind i tin tout reft
  project (RImpF bind i tin tout reft) = RImpFF bind i tin tout reft
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
  embed (RFunF  bind i tin tout reft) = RFun bind  i tin tout reft
  embed (RImpFF bind i tin tout reft) = RImpF bind i tin tout reft
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

-- | returns (lambda binders, forall binders)
collectSpecTypeBinders :: SpecType -> ([F.Symbol], [F.Symbol])
collectSpecTypeBinders = para $ \case
  RFunF bind _ (tin, _) (_, (bs, abs')) _ | isClassType tin -> (bs, abs')
                                       | otherwise       -> (bind : bs, abs')
  RImpFF bind _ (tin, _) (_, (bs, abs')) _ | isClassType tin -> (bs, abs')
                                        | otherwise       -> (bind : bs, abs')
  RAllEF b _ (_, (bs, abs'))  -> (b : bs, abs')
  RAllTF (RTVar (RTV ab) _) (_, (bs, abs')) _ -> (bs, F.symbol ab : abs')
  RExF b _ (_, (bs, abs'))    -> (b : bs, abs')
  RAppTyF _ (_, (bs, abs')) _ -> (bs, abs')
  RRTyF _ _ _ (_, (bs, abs')) -> (bs, abs')
  _                           -> ([], [])

-- really should be fused with collectBinders. However, we need the binders
-- to correctly convert fixpoint expressions to ghc expressions because of
-- namespace related issues (whether the symbol denotes a varName or a datacon)
buildHsExpr :: LHsExpr GhcPs -> SpecType -> LHsExpr GhcPs
buildHsExpr expr = para $ \case
  RFunF bind _ (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (varSymbolToRdrName bind)] res
  RImpFF bind _ (tin, _) (_, res) _
    | isClassType tin -> res
    | otherwise       -> mkHsLam [nlVarPat (varSymbolToRdrName bind)] res
  RAllEF  _ _        (_, res) -> res
  RAllTF  _ (_, res) _        -> res
  RExF    _ _        (_, res) -> res
  RAppTyF _ (_, res) _        -> res
  RRTyF _ _ _ (_, res)        -> res
  _                           -> expr



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
  -> (CoreExpr -> TcRn CoreExpr)
  -> SpecType
  -> TcRn SpecType
elaborateSpecType coreToLogic simplifier t = GM.withWiredIn $ do
  (t', xs) <- elaborateSpecType' (pure ()) coreToLogic simplifier t
  case xs of
    _ : _ -> panic
      Nothing
      "elaborateSpecType: invariant broken. substitution list for dictionary is not completely consumed"
    _ -> pure t'

elaborateSpecType'
  :: PartialSpecType
  -> (CoreExpr -> F.Expr) -- core to logic
  -> (CoreExpr -> TcRn CoreExpr)
  -> SpecType
  -> TcRn (SpecType, [F.Symbol]) -- binders for dictionaries
                   -- should have returned Maybe [F.Symbol]
elaborateSpecType' partialTp coreToLogic simplify t =
  case F.notracepp "elaborateSpecType'" t of
    RVar (RTV tv) (MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
      elaborateReft
        (reft, t)
        (pure (t, []))
        (\bs' ee -> pure (RVar (RTV tv) (MkUReft (F.Reft (vv, ee)) p), bs'))
        -- YL : Fix
    RFun bind i tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
      -- the reft is never actually used by the child
      -- maybe i should enforce this information at the type level
      let partialFunTp =
            Free (RFunF bind i (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
          partialTp' = partialTp >> partialFunTp :: PartialSpecType
      (eTin , bs ) <- elaborateSpecType' partialTp coreToLogic simplify tin
      (eTout, bs') <- elaborateSpecType' partialTp' coreToLogic simplify tout
      let buildRFunContTrivial
            | isClassType tin, dictBinder : bs0' <- bs' = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs0')
              pure
                ( F.notracepp "RFunTrivial0"
                  $ RFun dictBinder i eTin eToutRenamed ureft
                , canonicalBinders
                )
            | otherwise = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs')
              pure
                ( F.notracepp "RFunTrivial1" $ RFun bind i eTin eToutRenamed ureft
                , canonicalBinders
                )
          buildRFunCont bs'' ee
            | isClassType tin, dictBinder : bs0' <- bs' = do
              let (eToutRenamed, canonicalBinders) =
                    canonicalizeDictBinder bs (eTout, bs0')
                  (eeRenamed, canonicalBinders') =
                    canonicalizeDictBinder canonicalBinders (ee, bs'')
              pure
                ( RFun dictBinder i
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
                ( RFun bind i
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
    RImpF bind i tin tout ureft@(MkUReft reft@(F.Reft (vv, _oldE)) p) -> do
      let partialFunTp =
            Free (RImpFF bind i (wrap $ specTypeToPartial tin) (pure ()) ureft) :: PartialSpecType
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
        (pure (RImpF bind i eTin eToutRenamed ureft, canonicalBinders))
        (\bs'' ee -> do
          let (eeRenamed, canonicalBinders') =
                canonicalizeDictBinder canonicalBinders (ee, bs'')
          pure
            ( RImpF bind i eTin eTout (MkUReft (F.Reft (vv, eeRenamed)) p)
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
      | otherwise -> do
        args' <- mapM
          (fmap fst . elaborateSpecType' partialTp coreToLogic simplify)
          args
        elaborateReft
          (reft, t)
          (pure (RApp tycon args' pargs ureft, []))
          (\bs' ee ->
            pure (RApp tycon args' pargs (MkUReft (F.Reft (vv, ee)) p), bs')
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
    -> TcRn a
    -> ([F.Symbol] -> F.Expr -> TcRn a)
    -> TcRn a
  elaborateReft (reft@(F.Reft (vv, e)), vvTy) trivial nonTrivialCont =
    if isTrivial' reft
      then trivial
      else do
        let
          querySpecType =
            plugType (rFun' (classRFInfo True) vv vvTy boolType) partialTp :: SpecType

          (origBinders, origTyBinders) = F.notracepp "collectSpecTypeBinders"
            $ collectSpecTypeBinders querySpecType



          hsExpr =
            buildHsExpr (fixExprToHsExpr (S.fromList origBinders) e)
                        querySpecType :: LHsExpr GhcPs
          exprWithTySigs = noLoc $ ExprWithTySig
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,5,0) && !MIN_VERSION_GLASGOW_HASKELL(8,8,1,0)        
            (mkLHsSigWcType (specTypeToLHsType querySpecType))
            hsExpr
#else
            Ghc.noExtField
            hsExpr
            (mkLHsSigWcType (specTypeToLHsType querySpecType))
#endif
#endif
        eeWithLamsCore <- GM.elabRnExpr TM_Inst exprWithTySigs
        eeWithLamsCore' <- simplify eeWithLamsCore
        let
          (_, tyBinders) =
            collectSpecTypeBinders
              . ofType
              . exprType
              $ eeWithLamsCore'
          substTy' = zip tyBinders origTyBinders
          eeWithLams =
            coreToLogic (GM.notracePpr "eeWithLamsCore" eeWithLamsCore')
          (bs', ee) = F.notracepp "grabLams" $ grabLams ([], eeWithLams)
          (dictbs, nondictbs) =
            L.partition (F.isPrefixOfSym "$d") bs'
      -- invariant: length nondictbs == length origBinders
          subst = if length nondictbs == length origBinders
            then F.notracepp "SUBST" $ zip (L.reverse nondictbs) origBinders
            else panic
              Nothing
              "Oops, Ghc gave back more/less binders than I expected"
        ret <- nonTrivialCont
          dictbs
          ( renameBinderCoerc (\x -> Mb.fromMaybe x (L.lookup x substTy'))
          . F.substa (\x -> Mb.fromMaybe x (L.lookup x subst))
          $ F.notracepp
              (  "elaborated: subst "
              ++ F.showpp substTy'
              ++ "  "
              ++ F.showpp
                   (ofType $ exprType eeWithLamsCore' :: SpecType)
              )
              ee
          )  -- (GM.dropModuleUnique <$> bs')
        pure (F.notracepp "result" ret)
                           -- (F.substa )
  isTrivial' :: F.Reft -> Bool
  isTrivial' (F.Reft (_, F.PTrue)) = True
  isTrivial' _                     = False

  grabLams :: ([F.Symbol], F.Expr) -> ([F.Symbol], F.Expr)
  grabLams (bs, F.ELam (b, _) e) = grabLams (b : bs, e)
  grabLams bse                   = bse
  -- dropBinderUnique :: [F.Symbol] -> F.Expr -> F.Expr
  -- dropBinderUnique binders = F.notracepp "ElaboratedExpr"
  --   . F.substa (\x -> if L.elem x binders then GM.dropModuleUnique x else x)

renameBinderCoerc :: (F.Symbol -> F.Symbol) -> F.Expr -> F.Expr
renameBinderCoerc f = rename
 where
  renameSort = renameBinderSort f
  rename e'@(F.ESym _          ) = e'
  rename e'@(F.ECon _          ) = e'
  rename e'@(F.EVar _          ) = e'
  rename (   F.EApp e0 e1      ) = F.EApp (rename e0) (rename e1)
  rename (   F.ENeg e0         ) = F.ENeg (rename e0)
  rename (   F.EBin bop e0 e1  ) = F.EBin bop (rename e0) (rename e1)
  rename (   F.EIte e0  e1 e2  ) = F.EIte (rename e0) (rename e1) (rename e2)
  rename (   F.ECst e' t       ) = F.ECst (rename e') (renameSort t)
  -- rename (F.ELam (x, t) e') = F.ELam (x, renameSort t) (rename e')
  rename (   F.PAnd es         ) = F.PAnd (rename <$> es)
  rename (   F.POr  es         ) = F.POr (rename <$> es)
  rename (   F.PNot e'         ) = F.PNot (rename e')
  rename (   F.PImp e0 e1      ) = F.PImp (rename e0) (rename e1)
  rename (   F.PIff e0 e1      ) = F.PIff (rename e0) (rename e1)
  rename (   F.PAtom brel e0 e1) = F.PAtom brel (rename e0) (rename e1)
  rename (F.ECoerc _ _ e') = rename e'
    
  rename e = panic
    Nothing
    ("renameBinderCoerc: Not sure how to handle the expression " ++ F.showpp e)



renameBinderSort :: (F.Symbol -> F.Symbol) -> F.Sort -> F.Sort
renameBinderSort f = rename
 where
  rename F.FInt             = F.FInt
  rename F.FReal            = F.FReal
  rename F.FNum             = F.FNum
  rename F.FFrac            = F.FFrac
  rename (   F.FObj s     ) = F.FObj (f s)
  rename t'@(F.FVar _     ) = t'
  rename (   F.FFunc t0 t1) = F.FFunc (rename t0) (rename t1)
  rename (   F.FAbs  x  t') = F.FAbs x (rename t')
  rename t'@(F.FTC _      ) = t'
  rename (   F.FApp t0 t1 ) = F.FApp (rename t0) (rename t1)


mkHsTyConApp ::  IdP (GhcPass p) -> [LHsType (GhcPass p)] -> LHsType (GhcPass p)
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
mkHsTyConApp = nlHsTyConApp 
#else
mkHsTyConApp tyconId tyargs = nlHsTyConApp Prefix tyconId (map HsValArg tyargs)
#endif

-- | Embed fixpoint expressions into parsed haskell expressions.
--   It allows us to bypass the GHC parser and use arbitrary symbols
--   for identifiers (compared to using the string API)
fixExprToHsExpr :: S.HashSet F.Symbol -> F.Expr -> LHsExpr GhcPs
fixExprToHsExpr _ (F.ECon c) = constantToHsExpr c
fixExprToHsExpr env (F.EVar x)
  | x == "GHC.Types.[]" =  GM.notracePpr "Empty" $ nlHsVar (mkVarUnqual (mkFastString "[]"))
  | x == "GHC.Types.:" = GM.notracePpr "Cons" $ nlHsVar (mkVarUnqual (mkFastString ":"))
  | otherwise = GM.notracePpr "Var" $ nlHsVar (symbolToRdrName env x)
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
-- This is currently not doable because how do we know if FInt corresponds to
-- Int or Integer?
fixExprToHsExpr env (F.ECst e0 _    ) = fixExprToHsExpr env e0
-- fixExprToHsExpr env (F.PAnd []      ) = nlHsVar true_RDR
fixExprToHsExpr _ (F.PAnd []      ) = nlHsVar true_RDR
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

fixExprToHsExpr _ e =
  todo Nothing ("toGhcExpr: Don't know how to handle " ++ show e)

constantToHsExpr :: F.Constant -> LHsExpr GhcPs
-- constantToHsExpr (F.I c) = noLoc (HsLit NoExt (HsInt NoExt (mkIntegralLit c)))
constantToHsExpr (F.I i) =
  noLoc (HsOverLit Ghc.noExtField (mkHsIntegral (mkIntegralLit i)))
constantToHsExpr (F.R d) =
  noLoc (HsOverLit Ghc.noExtField (mkHsFractional (mkFractionalLit d)))
constantToHsExpr _ =
  todo Nothing "constantToHsExpr: Not sure how to handle constructor L"

-- This probably won't work because of the qualifiers
bopToHsExpr :: F.Bop -> LHsExpr GhcPs
bopToHsExpr bop = noLoc (HsVar Ghc.noExtField (noLoc (f bop)))
 where
  f F.Plus   = plus_RDR
  f F.Minus  = minus_RDR
  f F.Times  = times_RDR
  f F.Div    = mkVarUnqual (fsLit "/")
  f F.Mod    = GM.prependGHCRealQual (fsLit "mod")
  f F.RTimes = times_RDR
  f F.RDiv   = GM.prependGHCRealQual (fsLit "/")

brelToHsExpr :: F.Brel -> LHsExpr GhcPs
brelToHsExpr brel = noLoc (HsVar Ghc.noExtField (noLoc (f brel)))
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
    RVarF (RTV tv) _ -> nlHsTyVar
      -- (GM.notracePpr ("varRdr" ++ F.showpp (F.symbol tv)) $ getRdrName tv)
      (symbolToRdrNameNs tvName (F.symbol tv)) 
    RFunF _ _ (tin, tin') (_, tout) _
      | isClassType tin -> noLoc $ HsQualTy Ghc.noExtField (noLoc [tin']) tout
      | otherwise       -> nlHsFunTy tin' tout
    RImpFF _ _ (_, tin) (_, tout) _              -> nlHsFunTy tin tout
    RAllTF (ty_var_value -> (RTV tv)) (_, t) _ -> noLoc $ HsForAllTy
      Ghc.noExtField
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
      ForallInvis
#endif
      [noLoc $ UserTyVar Ghc.noExtField (noLoc $ symbolToRdrNameNs tvName (F.symbol tv))]
#else
      (mkHsForAllInvisTele [noLoc $ UserTyVar Ghc.noExtField SpecifiedSpec (noLoc $ symbolToRdrNameNs tvName (F.symbol tv))])
#endif
      t
    RAllPF _ (_, ty)                    -> ty
    RAppF RTyCon { rtc_tc = tc } ts _ _ -> mkHsTyConApp
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
    RHoleF _                 -> noLoc $ HsWildCardTy Ghc.noExtField
    RExprArgF _ ->
      todo Nothing "Oops, specTypeToLHsType doesn't know how to handle RExprArg"
