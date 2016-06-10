module NT where 

{-@ newtype Natural = Natural { toInt :: Int } @-}
newtype Natural = Natural { toInt :: Int } 

{-@ natural :: Nat -> Natural @-}
natural = Natural 

foo :: Int -> Maybe Natural 
foo n 
  | 0 <= n    = Just (natural n) 
  | otherwise = Nothing 
