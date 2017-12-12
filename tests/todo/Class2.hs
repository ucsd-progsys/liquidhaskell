module Class2 where 

class Dict a where 
  meth :: a -> Int -> Int 

data T1 = T1 

data T2 = T2 

instance Dict T1 where 
  meth T1 x = x + 1

instance Dict T2 where 
  meth T2 x = x + 2

{-@ test1 :: {v:Int | v = 1} @-}
test1 = meth T1 0 

{-@ test2 :: {v:Int | v = 2} @-}
test2 = meth T2 0

