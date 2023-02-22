{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Transforms.InlineAux
  ( inlineAux
  )
where
import qualified Language.Haskell.Liquid.UX.Config  as UX
import           Liquid.GHC.API
import           Control.Arrow                  (second)
import qualified Liquid.GHC.Misc
                                               as GM
import qualified Data.HashMap.Strict           as M

inlineAux :: UX.Config -> Module -> CoreProgram -> CoreProgram
inlineAux cfg m cbs =  if UX.auxInline cfg then occurAnalysePgm m (const False) (const False) [] (map f cbs) else cbs
 where
  f :: CoreBind -> CoreBind
  f all'@(NonRec x e)
    | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux = NonRec
      x
      (inlineAuxExpr dfunId methodToAux e)
    | otherwise = all'
  f (Rec bs) = Rec (fmap g bs)
   where
    g all'@(x, e)
      | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux
      = (x, inlineAuxExpr dfunId methodToAux e)
      | otherwise
      = all'
  auxToMethodToAux = mconcat $ fmap (uncurry dfunIdSubst) (grepDFunIds cbs)


-- inlineDFun :: DynFlags -> CoreProgram -> IO CoreProgram
-- inlineDFun df cbs = mapM go cbs
--  where
--   go orig@(NonRec x e) | isDFunId x = do
--                            -- e''' <- simplifyExpr df e''
--                            let newBody = mkCoreApps (GM.tracePpr ("substituted type:" ++ GM.showPpr (exprType (mkCoreApps e' (Var <$> binders)))) e') (fmap Var binders)
--                                bind = NonRec (mkWildValBinder (exprType newBody)) newBody
--                            pure $ NonRec x (mkLet bind e)
--                        | otherwise  = pure orig
--    where
--     -- wcBinder = mkWildValBinder t
--     (binders, _) = GM.tracePpr "collectBinders"$ collectBinders e
--     e' = substExprAll empty subst e
--   go recs = pure recs
--   subst = buildDictSubst cbs

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
inlineAuxExpr dfunId methodToAux = go
 where
  go :: CoreExpr -> CoreExpr
  go (Lam b body) = Lam b (go body)
  go (Let b body)
    | NonRec x e <- b, isDictId x =
        go $ substExpr (extendIdSubst emptySubst x e) body
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

mapAlt :: (Expr b -> Expr b) -> Alt b -> Alt b
mapAlt f (Alt d bs e) = Alt d bs (f e)
