module HasElem where

{-@ LIQUID "--no-termination" @-}

data L a = Nil | Cons a (L a)

{-@ measure hasElem @-}
hasElem :: Eq a => a -> L a -> Bool
hasElem x Nil = False
hasElem x (Cons y ys) = x == y || hasElem x ys

{-@ prop, prop1, prop2 :: {v:Bool | Prop v <=> true} @-}
prop :: Bool
prop = hasElem 1 (Cons 1 Nil)

prop1 :: Bool
prop1 = hasElem 1 (Cons 2 Nil)

prop2 :: Bool
prop2 = hasElem 1 Nil


nil = Nil
cons = Cons 
