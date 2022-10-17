{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module SGDSimple where

{- reflect update @-}
{-@ relational update ~ update :: x1:_ -> _ ~ x2:_ -> _ ~~ x1 < x2 => r1 x1 < r2 x2 @-}
update :: Int -> Int
update x = x + 1

{- reflect update' @-}
{-@ relational update' ~ update' :: y1:_ -> x1:_ -> _ ~ y2:_ -> x2:_ -> _ ~~ true => x1 < x2 => r1 y1 x1 < r2 y2 x2 @-}
update' :: Int -> Int -> Int
update' _ x = x + 1

-- TODO: add x1 x2 to the env
-- TODO: support fo precs for functions
{-@ relational bind ~ bind :: x1:_ -> f1:(z1:_ -> _) -> _ 
                            ~ x2:_ -> f2:(z2:_ -> _) -> _ 
                           ~~ x1 < x2 => (z1 < z2 => r1 z1 < r2 z2) => 
                                    r1 x1 f1 < r2 x2 f2 @-}
bind :: Int -> (Int -> Int) -> Int
bind x f = f x

{-@ relational sgd ~ sgd :: x1:_ -> _ ~ x2:_ -> _ 
                         ~~ x1 < x2 => r1 x1 < r2 x2 @-}
sgd :: Int -> Int
sgd x = bind x update

-- TODO: support eta expansion
{-@ relational sgd' ~ sgd' :: x1:_ -> _ ~ x2:_ -> _ 
                         ~~ x1 < x2 => r1 x1 < r2 x2 @-}
sgd' :: Int -> Int
sgd' x = bind x (\z -> update z)


-- {-@ update' 0 ~ update' 0 :: true => x1 < x2 => r1 y1 x1 < r2 y2 x2 @-}

-- {-@ u' ~ u' :: x1 < x2 => r1 y1 x1 < r2 y2 x2 @-}

-- {-@ u' ~ u' :: x1 < x2 => (0 < 0 => r1 y1 x1 < r2 y2 x2) @-}

-- TODO: support multiple arguments
{-@ relational sgd'' ~ sgd'' :: x1:_ -> _ ~ x2:_ -> _ 
                         ~~ x1 < x2 => r1 x1 < r2 x2 @-}
sgd'' :: Int -> Int
sgd'' x = bind x (update' 0) 
      
      -- let b1 = bind x 
      --         u = update' 0
      --         in b1 u
        -- = let u' = update' 0
        --         in bind x u'


