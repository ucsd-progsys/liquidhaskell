module AppSucc0 (main) where

{-@ suc :: d:Int ~> ( {v:_ | v = d} -> _ ) -> {v:_ | v = d - 1  } -> () @-}
suc :: (Int -> ()) -> Int -> ()
suc f x = f (x + 1)

app f x = if chaos then app (suc f) (x - 1) else f x
main n = app (check 0) 0

{-@ check :: a:Int -> {v:_|v=a} -> () @-}
check :: Int -> Int -> ()
check x y = assert (x == y)

------------------------------------------------------
{-@ assume liquidAssert :: {v:Bool | v} -> a -> a  @-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

{-@ assert :: {v:Bool | v} -> () @-}
assert x = liquidAssert x ()

{-@ chaos :: { True } @-}
chaos = True
