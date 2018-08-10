module LocalSig where 

foo = incr 10 
  where 
    {-@ incr :: Nat -> Nat @-}
    incr :: Int -> Int 
    incr x = x - 1 
