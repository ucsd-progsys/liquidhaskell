{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}

{-@ measure ackF :: Int -> Int -> Int  @-}

{-@ assume ack :: n:Int -> {v: (x:Int -> {v:Int | v == ackF n x}) | v == ackF n } @-}
ack :: Int -> Int -> Int
ack = undefined

bar :: Int -> Int -> Int
{-@ bar :: n:Int -> {v:_ | false } @-}
bar m n = ack m n

{-
foo :: Int -> Int -> Int
{- foo :: n:Int -> Int -> Int  @-}
foo n x = bar x n
-}
