module Maybe0 () where

import Language.Haskell.Liquid.Prelude
import Data.Maybe() -- to get isJust and fromJust

{-@ foo :: x:Maybe a -> {v:a | ((isJust(x)) => (fromJust(x) = v)) } @-}
foo :: Maybe a -> a 
foo (Just x)  = x 
foo (Nothing) = unsafeError "foo"

{-@ bar :: x:Maybe a -> {v:Bool | v <=> isJust x } @-}
bar (Just x)  = True 
bar (Nothing) = False

