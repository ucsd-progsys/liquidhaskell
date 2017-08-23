{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--maxparams=5"     @-}


{-@ measure ackF :: Int -> Int -> Int  @-}

{-@ assume ack :: n:Int -> {v: (x:Int -> {v:Int | v == ackF n x}) | v == ackF n } @-}
ack :: Int -> Int -> Int
ack = undefined

bar :: Int -> Int -> Int
{-@ bar :: n:Int -> {v:_ | v == ackF n } @-}
bar m = ack m

