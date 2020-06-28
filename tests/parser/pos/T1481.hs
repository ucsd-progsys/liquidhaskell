{-# LANGUAGE MultiParamTypeClasses #-}
module T1481 where

{-@
class Monad m => Filter filter m where
  q :: forall a . Int -> Int -> Int -> m (filter a)
  qq :: forall a . filter a -> m Int
@-}
class Monad m => Filter filter m where
  q :: Int -> Int -> Int -> m (filter a)
  qq :: filter a -> m Int
