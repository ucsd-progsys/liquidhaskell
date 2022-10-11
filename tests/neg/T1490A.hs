{-@ LIQUID "--expect-any-error" @-}
module T1490A () where

newtype Embed a = Embed a

{-@ autosize LTT @-}
{-@ data LTT = Pi { piTyA :: Embed LTT, piTyB :: LTT }
             | Universe
             | Var @-}
data LTT = Pi (Embed LTT) LTT
         | Universe
         | Var

{-@ measure isLttDev @-}
isLttDev :: LTT -> Bool
isLttDev (Pi (Embed t1) t2) = isLttDev t2 || isLttDev t1
isLttDev Universe = True
isLttDev Var = False


newtype B = B Bool

{-@ fb :: Bool -> Nat @-}
fb :: Bool -> Int
fb b  = 1

{-@ foo :: B -> Nat @-}
foo :: B -> Int
foo (B b) = fb b
