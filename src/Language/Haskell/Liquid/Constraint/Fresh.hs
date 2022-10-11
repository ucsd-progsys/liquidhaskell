{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Constraint.Fresh
  ( -- module Language.Haskell.Liquid.Types.Fresh
    -- , 
    refreshArgsTop
  , freshTyType
  , freshTyExpr
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

import           Language.Fixpoint.Misc  ((=>>))
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types.Visitor (kvarsExpr)
import           Language.Haskell.Liquid.Types
-- import           Language.Haskell.Liquid.Types.RefType
-- import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Constraint.Types
import qualified Liquid.GHC.Misc as GM
import           Liquid.GHC.API as Ghc

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
--   Constraint generation should ONLY use @freshTyType@ and @freshTyExpr@

freshTyType        :: Bool -> KVKind -> CoreExpr -> Type -> CG SpecType
freshTyType allowTC k e τ  =  F.notracepp ("freshTyType: " ++ F.showpp k ++ GM.showPpr e)
                   <$> freshTyReftype allowTC k (ofType τ)

freshTyExpr        :: Bool -> KVKind -> CoreExpr -> Type -> CG SpecType
freshTyExpr allowTC k e _  = freshTyReftype allowTC k $ exprRefType e

freshTyReftype     :: Bool -> KVKind -> SpecType -> CG SpecType
freshTyReftype allowTC k _t = (fixTy t >>= refresh allowTC) =>> addKVars k
  where
    t                = {- F.tracepp ("freshTyReftype:" ++ show k) -} _t

-- | Used to generate "cut" kvars for fixpoint. Typically, KVars for recursive
--   definitions, and also to update the KVar profile.
addKVars        :: KVKind -> SpecType -> CG ()
addKVars !k !t  = do
    cfg <- gets (getConfig . ghcI)
    when True          $ modify $ \s -> s { kvProf = updKVProf k ks (kvProf s) }
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
specTypeKVars = foldReft False (\ _ r ks -> kvarsExpr (F.reftPred $ ur_reft r) ++ ks) []

--------------------------------------------------------------------------------
trueTy  :: Bool -> Type -> CG SpecType
--------------------------------------------------------------------------------
trueTy allowTC = ofType' >=> true allowTC

ofType' :: Type -> CG SpecType
ofType' = fixTy . ofType

fixTy :: SpecType -> CG SpecType
fixTy t = do tyi   <- gets tyConInfo
             tce   <- gets tyConEmbed
             return $ addTyConInfo tce tyi t

exprRefType :: CoreExpr -> SpecType
exprRefType = exprRefType_ M.empty

exprRefType_ :: M.HashMap Var SpecType -> CoreExpr -> SpecType
exprRefType_ γ (Let b e)
  = exprRefType_ (bindRefType_ γ b) e

exprRefType_ γ (Lam α e) | isTyVar α
  = RAllT (makeRTVar $ rTyVar α) (exprRefType_ γ e) mempty

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
