{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Transforms.InlineAux
  ( inlineAux
  , inlineDFun
  )
where

import           CoreSyn
import           DynFlags
import qualified Outputable                    as O
import           MkCore
import           Control.Arrow                  ( second )
import           OccurAnal                      ( occurAnalysePgm )
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Class                          ( classAllSelIds )
import           Id
import           CoreFVs                        ( exprFreeVarsList )
import           InstEnv
import           TcType                         ( tcSplitDFunTy )
import           GhcPlugins                     ( isDFunId
                                                , exprType
                                                , OccName
                                                , Module
                                                , occNameString
                                                , getOccName
                                                , mkCoreApps
                                                )
import           Predicate                      ( isDictId )
import qualified Data.HashMap.Strict           as M
import           CoreSubst
import           GHC                            ( isDictonaryId )
import           SimplMonad
import           SimplCore
import           Control.Monad.State
import           Data.Functor.Foldable

buildDictSubst :: CoreProgram -> M.HashMap Id CoreExpr
buildDictSubst = cata f
 where
  f Nil = M.empty
  f (Cons b s) | NonRec x e <- b, isDFunId x || isDictonaryId x = M.insert x e s
               | otherwise = s


inlineAux :: Module -> CoreProgram -> CoreProgram
inlineAux m cbs = occurAnalysePgm m (const False) (const False) [] (map f cbs)
 where
  f :: CoreBind -> CoreBind
  f all@(NonRec x e)
    | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux = NonRec
      x
      (inlineAuxExpr dfunId methodToAux e)
    | otherwise = all
  f (Rec bs) = Rec (fmap g bs)
   where
    g all@(x, e)
      | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux
      = (x, inlineAuxExpr dfunId methodToAux e)
      | otherwise
      = all
  auxToMethodToAux = mconcat $ fmap (uncurry dfunIdSubst) (grepDFunIds cbs)


inlineDFun :: DynFlags -> CoreProgram -> IO CoreProgram
inlineDFun df cbs = pure cbs-- mapM go cbs
 -- where
 --  go orig@(NonRec x e) | isDFunId x = do
 --                           -- e''' <- simplifyExpr df e''
 --                           let newBody = mkCoreApps (GM.tracePpr ("substituted type:" ++ GM.showPpr (exprType (mkCoreApps e' binders))) e') (fmap Var binders)
 --                               bind = NonRec (mkWildValBinder (exprType newBody)) newBody
 --                           pure $ NonRec x (mkLet bind e)
 --                       | otherwise  = pure orig
 --   where
 --    -- wcBinder = mkWildValBinder t
 --    (binders, _) = GM.tracePpr "collectBinders"$ collectBinders e
 --    e' = substExprAll O.empty subst e
 --  go recs = pure recs
 --  subst = buildDictSubst cbs



lookupIdSubstAll :: O.SDoc -> M.HashMap Id CoreExpr -> Id -> CoreExpr
lookupIdSubstAll doc env v | Just e <- M.lookup v env = e
                           | otherwise                = Var v
        -- Vital! See Note [Extending the Subst]
  -- | otherwise = WARN( True, text "CoreSubst.lookupIdSubst" <+> doc <+> ppr v
  --                           $$ ppr in_scope)

substExprAll :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
substExprAll doc subst orig_expr = subst_expr_all doc subst orig_expr


subst_expr_all :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
subst_expr_all doc subst expr = go expr
 where
  go (Var v) = lookupIdSubstAll (doc O.$$ O.text "subst_expr_all") subst v
  go (Type     ty      ) = Type ty
  go (Coercion co      ) = Coercion co
  go (Lit      lit     ) = Lit lit
  go (App  fun     arg ) = App (go fun) (go arg)
  go (Tick tickish e   ) = Tick tickish (go e)
  go (Cast e       co  ) = Cast (go e) co
     -- Do not optimise even identity coercions
     -- Reason: substitution applies to the LHS of RULES, and
     --         if you "optimise" an identity coercion, you may
     --         lose a binder. We optimise the LHS of rules at
     --         construction time

  go (Lam  bndr    body) = Lam bndr (subst_expr_all doc subst body)

  go (Let  bind    body) = Let (mapBnd go bind) (subst_expr_all doc subst body)

  go (Case scrut bndr ty alts) =
    Case (go scrut) bndr ty (map (go_alt subst) alts)

  go_alt subst (con, bndrs, rhs) = (con, bndrs, subst_expr_all doc subst rhs)



-- grab the dictionaries
grepDFunIds :: CoreProgram -> [(DFunId, CoreExpr)]
grepDFunIds = filter (isDFunId . fst) . flattenBinds

isClassOpAuxOccName :: OccName -> Bool
isClassOpAuxOccName occ = case occNameString occ of
  '$' : 'c' : _ -> True
  _             -> False

isClassOpAuxOf :: Id -> Id -> Bool
isClassOpAuxOf aux method = case occNameString $ getOccName aux of
  '$' : 'c' : rest -> rest == occNameString (getOccName method)
  _                -> False

dfunIdSubst :: DFunId -> CoreExpr -> M.HashMap Id (Id, M.HashMap Id Id)
dfunIdSubst dfunId e = M.fromList $ zip auxIds (repeat (dfunId, methodToAux))
 where
  methodToAux = M.fromList
    [ (m, aux) | m <- methods, aux <- auxIds, aux `isClassOpAuxOf` m ]
  (_, _, cls, _) = tcSplitDFunTy (idType dfunId)
  auxIds = filter (isClassOpAuxOccName . getOccName) (exprFreeVarsList e)
  methods = classAllSelIds cls

inlineAuxExpr :: DFunId -> M.HashMap Id Id -> CoreExpr -> CoreExpr
inlineAuxExpr dfunId methodToAux e = go e
 where
  go :: CoreExpr -> CoreExpr
  go (Lam b body) = Lam b (go body)
  go (Let b body)
    | NonRec x e <- b, isDictId x = go
    $ substExpr O.empty (extendIdSubst emptySubst x e) body
    | otherwise = Let (mapBnd go b) (go body)
  go (Case e x t alts) = Case (go e) x t (fmap (mapAlt go) alts)
  go (Cast e c       ) = Cast (go e) c
  go (Tick t e       ) = Tick t (go e)
  go e
    | (Var m, args) <- collectArgs e
    , Just aux <- M.lookup m methodToAux
    , arg : argsNoTy <- dropWhile isTypeArg args
    , (Var x, argargs) <- collectArgs arg
    , x == dfunId
    = GM.notracePpr ("inlining in" ++ GM.showPpr e)
      $ mkCoreApps (Var aux) (argargs ++ (go <$> argsNoTy))
  go (App e0 e1) = App (go e0) (go e1)
  go e           = e


-- modified from Rec.hs
mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
mapBnd f (NonRec b e) = NonRec b (f e)
mapBnd f (Rec bs    ) = Rec (map (second f) bs)

mapAlt :: (Expr b -> Expr b) -> (t, t1, Expr b) -> (t, t1, Expr b)
mapAlt f (d, bs, e) = (d, bs, f e)
