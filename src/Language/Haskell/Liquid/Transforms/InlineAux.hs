{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Transforms.InlineAux
  ( inlineAux
  )
where
import qualified Language.Haskell.Liquid.UX.Config  as UX
import           Language.Haskell.Liquid.GHC.API
import           Control.Arrow                  (second)
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import qualified Data.HashMap.Strict           as M

inlineAux :: UX.Config -> Module -> CoreProgram -> CoreProgram
inlineAux cfg m cbs =  if UX.auxInline cfg then occurAnalysePgm m (const False) (const False) [] (map f cbs) else cbs
 where
  f :: CoreBind -> CoreBind
  f cb@(NonRec x e)
    | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux = NonRec
      x
      (inlineAuxExpr dfunId methodToAux e)
    | otherwise = cb
  f (Rec bs) = Rec (fmap g bs)
   where
    g cb@(x, e)
      | Just (dfunId, methodToAux) <- M.lookup x auxToMethodToAux
      = (x, inlineAuxExpr dfunId methodToAux e)
      | otherwise
      = cb
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
inlineAuxExpr dfunId methodToAux e = go e
 where
  go :: CoreExpr -> CoreExpr
  go (Lam b body) = Lam b (go body)
  go (Let b body)
    | NonRec x ecb <- b, isDictId x = go
     $ substExpr
#if !MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)     
        empty
#endif
        (extendIdSubst emptySubst x ecb) body
    | otherwise = Let (mapBnd go b) (go body)
  go (Case ecb x t alts) = Case (go ecb) x t (fmap (mapAlt go) alts)
  go (Cast ecb c       ) = Cast (go ecb) c
  go (Tick t ecb       ) = Tick t (go ecb)
  go ecb
    | (Var m, args) <- collectArgs ecb
    , Just aux <- M.lookup m methodToAux
    , arg : argsNoTy <- dropWhile isTypeArg args
    , (Var x, argargs) <- collectArgs arg
    , x == dfunId
    = GM.notracePpr ("inlining in" ++ GM.showPpr ecb)
      $ mkCoreApps (Var aux) (argargs ++ (go <$> argsNoTy))
  go (App e0 e1) = App (go e0) (go e1)
  go ecb           = ecb


-- modified from Rec.hs
mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
mapBnd f (NonRec b e) = NonRec b (f e)
mapBnd f (Rec bs    ) = Rec (map (second f) bs)

mapAlt :: (Expr b -> Expr b) -> (t, t1, Expr b) -> (t, t1, Expr b)
mapAlt f (d, bs, e) = (d, bs, f e)
