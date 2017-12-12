module Class1 where 

data Dict a = D { meth :: a -> Int -> Int }

data T1 = T1 

data T2 = T2 

t1 = D (\T1 x -> x + 1)

t2 = D (\T2 x -> x + 2) 

{-@ test1 :: {v:Int | v = 1} @-}
test1 = meth t1 T1 0 

{-@ test2 :: {v:Int | v = 2} @-}
test2 = meth t2 T2 0

