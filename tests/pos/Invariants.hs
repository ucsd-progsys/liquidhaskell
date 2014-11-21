{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Foo () where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Data.IORef


data Foo a b c d

{-@ data variance IO bivariant @-}

foo :: IO ()
foo = do a <- return 0 
         liquidAssert (a == 0) (return ())

foo' :: IO ()
foo' = bind (return 0) (\a -> liquidAssert (a == 0) (return ()))

{-@ data variance IORef bivariant @-}

{-@ data variance Foo invariant bivariant covariant contravariant @-}

{-@ job' :: IORef {v:Int |  v = 4} -> IO () @-}
job' :: IORef Int -> IO ()
job' p = 
	bind (readIORef p) (\v -> liquidAssert (v == 4) (return ()))


{-@ bind :: Monad m => m a -> (a -> m b) -> m b @-}
bind :: Monad m => m a -> (a -> m b) -> m b
bind = (>>=)























