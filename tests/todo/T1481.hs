{-# LANGUAGE MultiParamTypeClasses #-}

module Foo where 

{-@ class Monad m => Filter filter m where
      q  :: forall m. Int -> Int -> Int -> _
      qq :: _ -> _ 
  @-}
class Monad m => Filter filter m where
  q :: Int -> Int -> Int -> m (filter a)
  qq :: filter a -> m Int
