module UnboundVarInReflect where

-- see GH #1708

{-@ LIQUID "--reflection" @-}
{-@ reflect frog @-}
frog :: () -> Bool
frog () = undefined
