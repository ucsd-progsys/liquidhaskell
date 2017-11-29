{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}

module Language.Haskell.Liquid.Constraint.Fresh
  ( module Language.Haskell.Liquid.Types.Fresh
  , refreshArgsTop
  , freshTy_type
  , freshTy_expr
  , trueTy
  , addKuts
  )
  where

-- import           Data.Maybe                    (catMaybes) -- , fromJust, isJust)
-- import           Data.Bifunctor
-- import qualified Data.List                      as L
import qualified Data.HashMap.Strict            as M
import qualified Data.HashSet                   as S
import           Data.Hashable
import           Control.Monad.State            (gets, get, put, modify)
import           Control.Monad                  (when, (>=>))
import           Prelude                        hiding (error)

import           CoreUtils  (exprType)
import           Type       (Type)
import           CoreSyn
import           Var        (varType, isTyVar, Var)

import           Language.Fixpoint.Misc  ((=>>))
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types.Visitor (kvars)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Constraint.Types

--------------------------------------------------------------------------------
-- | This is all hardwiring stuff to CG ----------------------------------------
--------------------------------------------------------------------------------
instance Freshable CG Integer where
  fresh = do s <- get
             let n = freshIndex s
             put $ s { freshIndex = n + 1 }
             return n

--------------------------------------------------------------------------------
refreshArgsTop :: (Var, SpecType) -> CG SpecType
--------------------------------------------------------------------------------
refreshArgsTop (x, t)
  = do (t', su) <- refreshArgsSub t
       modify $ \s -> s {termExprs = M.adjust (F.subst su <$>) x $ termExprs s}
       return t'

--------------------------------------------------------------------------------
-- | Generation: Freshness -----------------------------------------------------
--------------------------------------------------------------------------------

-- | Right now, we generate NO new pvars. Rather than clutter code
--   with `uRType` calls, put it in one place where the above
--   invariant is /obviously/ enforced.
--   Constraint generation should ONLY use @freshTy_type@ and @freshTy_expr@

freshTy_type        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_type k _ τ  = freshTy_reftype k $ ofType τ

freshTy_expr        :: KVKind -> CoreExpr -> Type -> CG SpecType
freshTy_expr k e _  = freshTy_reftype k $ exprRefType e

freshTy_reftype     :: KVKind -> SpecType -> CG SpecType
freshTy_reftype k _t = (fixTy t >>= refresh) =>> addKVars k
  where
    t                = {- F.tracepp ("freshTy_reftype:" ++ show k) -} _t

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.
addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do
    cfg <- getConfig  <$> gets ghcI
    when (True)        $ modify $ \s -> s { kvProf = updKVProf k ks (kvProf s) }
    when (isKut cfg k) $ addKuts k t
  where
    ks         = F.KS $ S.fromList $ specTypeKVars t

isKut :: Config -> KVKind -> Bool
isKut _  (RecBindE _) = True
isKut cfg ProjectE    = not (higherOrderFlag cfg) -- see ISSUE 1034, tests/pos/T1034.hs
isKut _    _          = False

addKuts :: (PPrint a) => a -> SpecType -> CG ()
addKuts _x t = modify $ \s -> s { kuts = mappend (F.KS ks) (kuts s)   }
  where
     ks'     = S.fromList $ specTypeKVars t
     ks
       | S.null ks' = ks'
       | otherwise  = {- F.tracepp ("addKuts: " ++ showpp _x) -} ks'

specTypeKVars :: SpecType -> [F.KVar]
specTypeKVars = foldReft (\ _ r ks -> (kvars $ ur_reft r) ++ ks) []

--------------------------------------------------------------------------------
trueTy  :: Type -> CG SpecType
--------------------------------------------------------------------------------
trueTy = ofType' >=> true

ofType' :: Type -> CG SpecType
ofType' = fixTy . ofType

fixTy :: SpecType -> CG SpecType
fixTy t = do tyi   <- tyConInfo  <$> get
             tce   <- tyConEmbed <$> get
             return $ addTyConInfo tce tyi t

exprRefType :: CoreExpr -> SpecType
exprRefType = exprRefType_ M.empty

exprRefType_ :: M.HashMap Var SpecType -> CoreExpr -> SpecType
exprRefType_ γ (Let b e)
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (makeRTVar $ rTyVar α) (exprRefType_ γ e)

exprRefType_ γ (Lam x e)
  = rFun (F.symbol x) (ofType $ varType x) (exprRefType_ γ e)

exprRefType_ γ (Tick _ e)
  = exprRefType_ γ e

exprRefType_ γ (Var x)
  = M.lookupDefault (ofType $ varType x) x γ

exprRefType_ _ e
  = ofType $ exprType e

bindRefType_ :: M.HashMap Var SpecType -> Bind Var -> M.HashMap Var SpecType
bindRefType_ γ (Rec xes)
  = extendγ γ [(x, exprRefType_ γ e) | (x,e) <- xes]

bindRefType_ γ (NonRec x e)
  = extendγ γ [(x, exprRefType_ γ e)]

extendγ :: (Eq k, Foldable t, Hashable k)
        => M.HashMap k v
        -> t (k, v)
        -> M.HashMap k v
extendγ γ xts
  = foldr (\(x,t) m -> M.insert x t m) γ xts
