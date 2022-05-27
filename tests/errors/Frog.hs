
module Frog where

{-@ LIQUID "--reflection" @-}

{-@ reflect frog @-}
frog :: () -> Bool
frog () = undefined
