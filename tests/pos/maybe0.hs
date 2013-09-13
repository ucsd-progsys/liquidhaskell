module Test where

import Language.Haskell.Liquid.Prelude

{-@ foo :: x:Maybe a -> {v:a | ((isJust(x)) => (fromJust(x) = v)) } @-}
foo :: Maybe a -> a 
foo (Just x)  = x 
foo (Nothing) = error "foo"

{-@ bar :: x:Maybe a -> {v:Bool | ((isJust(x)) <=> Prop(v)) } @-}
bar (Just x)  = True 
bar (Nothing) = False

