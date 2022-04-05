module SynchCase where

x, y :: Int
x = 0
y = 0

{-@ relational x ~ y :: _ ~ _ ~~ r1 = r2 @-}

foo :: Int -> Bool
foo x = if x == 0 then True else False

{-@ relational foo ~ foo :: x:_ -> _ ~ y:_ -> _ ~~ x = y => r1 x = r2 y @-}

foox, fooy :: Bool
foox = foo x
fooy = foo y

{-@ relational foox ~ fooy :: _ ~ _ ~~ r1 = r2 @-}

foox', fooy' :: Bool
foox' = if x == 0 then True else False
fooy' = if y == 0 then True else False

{-@ relational foox' ~ fooy' :: _ ~ _ ~~ r1 = r2 @-}

a, b :: Bool
a = True
b = True

{-@ relational a ~ b :: _ ~ _ ~~ r1 = r2 @-}

fooa, foob :: Int
fooa = if a then 1 else 0
foob = if b then 1 else 0

{-@ relational fooa ~ foob :: _ ~ _ ~~ r1 = r2 @-}
