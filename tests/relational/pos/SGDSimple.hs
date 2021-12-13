{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module SGDSimple where

{-@ relational update ~ update :: x1:_ -> _ ~ x2:_ -> _ ~~ x1 < x2 => r1 x1 < r2 x2 @-}
update :: Int -> Int
update x = x + 1

-- TODO: add x1 x2 to the env
-- TODO: support fo precs for functions
{-@ relational bind ~ bind :: x1:_ -> f1:(z1:_ -> _) -> _ 
                            ~ x2:_ -> f2:(z2:_ -> _) -> _ 
                           ~~ x1 < x2 => (z1 < z2 => r1 < r2) => r1 x1 f1 < r2 x2 f2 @-}
bind :: Int -> (Int -> Int) -> Int
bind x f = f x

{-@ relational bind1 ~ bind1 :: x1:_ -> _ 
                              ~ x2:_ -> _
                             ~~ x1 < x2 => r1 x1 < r2 x2 @-}
bind1 :: Int -> Int
bind1 x = x + 1

{-@ relational choice ~ choice :: x1:_ -> _ ~ x2:_ -> _ ~~ x1 < x2 => r1 < r2 @-}
choice :: Int -> Int
choice x = x + 1 

{-@ relational sgd ~ sgd :: x1:_ -> _ ~ x2:_ -> _ ~~ x1 < x2 => r1 x1 < r2 x2 @-}
sgd :: Int -> Int
sgd x = choice (bind x update)

