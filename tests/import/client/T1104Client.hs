import T1104Lib 

-- 'bar' should ALSO work but right now, but right now 'twerp' is simpler. 

{- bar :: Foo a b -> Maybe ({v:Foo a b | isFoo v}) @-}
bar :: Foo a b -> Maybe (Foo a b)
bar x | isFoo x   = Just x 
      | otherwise = Nothing 

{-@ burp :: (Foo a b) -> Nat @-} 
burp :: Foo a b -> Int 
burp x = toNat x 

{-@ twerp :: x:(Foo a b) -> {v:Bool | v = isFoo x} @-}
twerp x = g x
  where 
    g = isFoo
