{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--maxparams=5"     @-}


{-@ measure ack :: Int -> Int -> Int  @-}

{-@ assume ack :: n:Int -> {v: (x:Int -> {v:Int | v == ack n x}) | v == ack n } @-}
ack :: Int -> Int -> Int
ack = undefined

bar :: Int -> Int -> Int
{-@ bar :: n:Int -> {v:_ | v == ack n } @-}
bar m = ack m

{-
foo :: Int -> Int -> Int
{- foo :: n:Int -> Int -> Int  @-}
foo n x = bar x n
-}
