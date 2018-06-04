module AppSucc0 (main) where

{-@ chaos :: { True } @-}
chaos = undefined

suc f x = f (x+1)

app f x = if chaos then app (suc f) (x - 1) else f x

{-@ check :: a:Int -> {v:_|v=a} -> () @-}
check :: Int -> Int -> ()
check x y = ()

main n = app (check 0) 0
