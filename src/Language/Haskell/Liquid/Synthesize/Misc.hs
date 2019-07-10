{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Misc where


import TyCoRep 
import           Control.Monad.State.Lazy

-- can we replace it with Language.Haskell.Liquid.GHC.Misc.isBaseType ? 
isBasic :: Type -> Bool
isBasic TyConApp{}     = True
isBasic TyVarTy {}     = True
isBasic (ForAllTy _ t) = isBasic t
isBasic AppTy {}       = False 
isBasic LitTy {}       = False
isBasic _              = False


(<$$>) :: (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) = fmap . fmap

filterElseM :: Monad m => (a -> m Bool) -> [a] -> m [a] -> m [a]
filterElseM f as ms = do
    rs <- filterM f as
    if null rs then
        ms
    else
        return rs