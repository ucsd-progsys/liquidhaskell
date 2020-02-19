module Language.Haskell.Liquid.Transforms.InlineAux
  ( inlineAux
  )
where

import           CoreSyn
import           Control.Arrow                  ( second )
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Class                          ( classAllSelIds )
import           Id
import           CoreFVs                        ( exprFreeVarsList )
import           InstEnv
import           TcType                         ( tcSplitDFunTy )
import           GhcPlugins                     ( isDFunId
                                                , OccName
                                                , occNameString
                                                , getOccName
                                                , mkCoreApps
                                                )
import qualified Data.HashMap.Strict           as M

-- Issue: mappend (S n) m = S (mappend n m)
-- in core:
--  $cmappend_Nat (S n) m = S (mappend $fMonoid_Nat n m)
--  $fMonoid_nat = C:Monoid $cmappend_nat $cmempty
--  note that now there's mutual dependence between $cmappend_Nat and $fMonoid_nat
--  to address this problem, we do the substitution: mappend $Monoid_Nat -> $cmappend_Nat


inlineAux :: CoreProgram -> CoreProgram
inlineAux cbs = map f cbs
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
  -- go (App e arg)
  --   | Var m <- e
  --   , Just aux <- M.lookup m methodToAux
  --   , (Var x, args, _) <- GM.tracePpr "collecting" $ collectArgs arg
  --   , x == dfunId
  --   = mkCoreApps (Var aux) args
  --   | otherwise
  --   = App (go e) (go arg)
  go (Lam b body     ) = Lam b (go body)
  go (Let b e        ) = Let (mapBnd go b) (go e)
  go (Case e x t alts) = Case (go e) x t (fmap (mapAlt go) alts)
  go (Cast e c       ) = Cast (go e) c
  go (Tick t e       ) = Tick t (go e)
  go e
    | (Var m, args) <- collectArgs e
    , Just aux <- M.lookup m methodToAux
    , arg : argsNoTy <- dropWhile isTypeArg args
    , (Var x, argargs) <- collectArgs arg
    , x == dfunId
    = mkCoreApps (Var aux) (argargs ++ argsNoTy)
  go (App e0 e1) = App (go e0) (go e1)
  go e           = e


-- modified from Rec.hs
mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
mapBnd f (NonRec b e) = NonRec b (f e)
mapBnd f (Rec bs    ) = Rec (map (second f) bs)

mapAlt :: (Expr b -> Expr b) -> (t, t1, Expr b) -> (t, t1, Expr b)
mapAlt f (d, bs, e) = (d, bs, f e)
