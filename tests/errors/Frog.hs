{-@ LIQUID "--expect-error-containing=Unbound symbol GHC.Err.undefined" @-}

module Frog where

{-@ LIQUID "--reflection" @-}

{-@ reflect frog @-}
frog :: () -> Bool
frog () = undefined
