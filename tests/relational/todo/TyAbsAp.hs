module TyAbsAp where

ap :: (a -> b) -> a -> b
ap f a = f a

ap''' :: (a -> b) -> a -> b
ap''' f a = f a

ap' :: (a -> b) -> a -> () -> b
ap' f a _ = f a

ap'' :: (a -> b) -> a -> c -> b
ap'' f a _ = f a

{-@ relational ap ~ ap''' :: f:(a -> b) -> x:a -> b ~ g:(a -> b) -> y:a -> b 
                          | f = g => x = y => r1 f x = r2 g y @-}

-- {-@ relational ap' ~ ap'' :: f:(a -> b) -> x:a -> u:() -> b ~ g:(a -> b) -> y:a -> z:c -> b 
--                            | f = g => x = y => true => r1 f x u = r2 g y z @-}

-- {-@ relational ap ~ ap :: f:(a -> b) -> x:a -> b ~ g:(b -> b) -> y:b -> b
--                        | f = g => x = y => r1 f x = r2 g y @-}

{- ap id () -}

apZero :: (b -> b) -> b -> b
apZero = ap 

-- {-@ relational ap ~ ap :: f:(a -> b) -> x:a -> b ~ g:(c -> d) -> y:c -> d
--                        | true => true => r1 f x = r2 g y @-}
