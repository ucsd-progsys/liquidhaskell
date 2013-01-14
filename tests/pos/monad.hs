module Monad where

foo x = return x

zoo x = return ()

bar x
  = do f <- foo x
       zoo x
       return ()
