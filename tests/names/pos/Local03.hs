module Local03 where

-- tests that we don't resolve against the local.


{-@ foo :: Nat -> Nat @-} 
foo :: Int -> Int 
foo x = x + 1 


bar :: Bool -> Bool 
bar x = foo x 
  where 
    foo y = not y

main :: IO ()
main = pure ()
