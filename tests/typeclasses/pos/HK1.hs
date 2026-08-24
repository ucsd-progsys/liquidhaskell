{-@ LIQUID "--typeclass" @-}
module HK1 where

class M m where
  {-@ ret :: a -> m a @-}
  ret :: a -> m a

class M m => VM m where
  {-@ lawRet :: x:a -> y:m a ->
        { ((y == ret x) ==> (y == ret x)) && ((y == ret x) ==> (y == ret x)) } @-}
  lawRet :: a -> m a -> ()
