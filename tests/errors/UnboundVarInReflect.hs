{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundVarInReflect.frog`" @-}
module UnboundVarInReflect where

-- see GH #1708

{-@ LIQUID "--reflection" @-}
{-@ reflect frog @-}
frog :: () -> Bool
frog () = undefined
