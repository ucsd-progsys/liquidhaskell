module Local02 where

{-@ foo :: x:_ -> y:_ -> {v:Int | v = x + y} @-} 
foo :: Int -> Int -> Int 
foo arg0 = bar 
  where 
    {-@ bar :: x:_ -> {v:Int | v = x + arg0} @-} 
    bar arg1 = arg0 + arg1 
