{-@ LIQUID "--expect-any-error" @-}
module T1490 where

newtype MyId a = MyId a


{-@ data U a = U {unU :: a -> ()} @-}
data U a = U {unU :: a -> ()}

newtype Id a = Id a


-- crash: SMTLIB2 respSat = Error "line 316 column 73: Sorts Int and (Main.Id Int) are incompatible"
{-@ bad :: x:U a -> y:Id a -> {x /= x} @-}
bad :: U a -> Id a -> ()
bad (U unU) (Id y) = unU y

-- succeed and no smtlib crash
{-@ ok0 :: x:U a -> y:Id a -> () @-}
ok0 :: U a -> Id a -> ()
ok0 (U unU) (Id y) = unU y

-- fail but no smtlib crash
{-@ ok1 :: x:U a -> y:a -> {x /= x} @-}
ok1 :: U a -> a -> ()
ok1 (U unU) y = unU y
