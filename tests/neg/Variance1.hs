{-@ LIQUID "--ghost-variance=Invariant" @-}
module Variance1 where

import Data.Binary


{-@ assume error :: { x : String | false } -> a @-}

example :: Get ()
example = do
    _ <- return ()
    error "URK"
