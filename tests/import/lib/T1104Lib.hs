module T1104Lib where 

data Foo a b = Foo {fooA :: a, fooB :: b}  |  Bar

{-@ measure isFoo @-}
isFoo :: Foo a b -> Bool
isFoo (Foo _ _) = True 
isFoo Bar       = False 

{-@ measure toNat @-}
{-@ toNat :: Foo a b -> Nat @-} 
toNat :: Foo a b -> Int 
toNat (Foo _ _) = 10 
toNat Bar       = 20 

{-@ twerp :: x:(Foo a b) -> {v:Bool | v = isFoo x} @-}
twerp x = g x
  where 
    g = isFoo
