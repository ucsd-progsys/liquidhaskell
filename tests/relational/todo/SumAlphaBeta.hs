module SumAlphaBeta where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- {-@ reflect foo @-}
-- {-@ foo :: xs:[Bool] -> α:N -> β:N -> n:N -> {v:N| v = n + α * countT xs + β * (len xs - countT xs)} @-}
-- foo :: [Bool] -> N -> N -> N -> N
-- foo []       _ _ n = n
-- foo (x : xs) α β n = if x then foo xs α β (n + α) else foo xs α β (n + β)

-- {-@ reflect countT @-}
-- countT :: [Bool] -> N
-- countT []           = 0
-- countT (True  : xs) = 1 + countT xs
-- countT (False : xs) = countT xs

-- -- Sum Negers, express countFalse through countTrue
-- {-@ thm :: xs:[Bool] -> α:N -> β:N -> n:N -> {foo xs α β n = n + α * countT xs + β * (len xs - countT xs)} @-}
-- thm :: [Bool] -> N -> N -> N -> ()
-- thm [] _ _ _ = ()
-- thm (True : xs) α β n = thm xs α β (α + n)
-- thm (False : xs) α β n = thm xs α β (β + n)

-- {-@ reflect foo' @-}
-- {-@ foo' :: xs:[Bool] -> α:N -> β:N -> n:N -> {v:N| v = n + α * countT xs + β * (len xs - countT xs)} @-}
-- foo' :: [Bool] -> Double -> Double -> Double -> Double
-- foo' []       _ _ n = n
-- foo' (x : xs) α β n = if x then foo' xs α β (n + α) else foo' xs α β (n + β)

-- {-@ reflect countT @-}
-- countT' :: [Bool] -> Double
-- countT' []           = 0
-- countT' (True  : xs) = 1 + countT' xs
-- countT' (False : xs) = countT' xs

-- {-@ reflect lend @-}
-- lend :: [a] -> Double
-- lend [] = 0
-- lend (_:xs) = 1 + lend xs

-- -- Sum Negers, express countFalse through countTrue
-- {-@ thm''' :: xs:[Bool] -> α:_ -> β:_ -> n:_ -> {foo xs α β n = n + α * countT xs + β * (lend xs - countT xs)} @-}
-- thm''' :: [Bool] -> Double -> Double -> Double -> ()
-- thm''' [] _ _ _ = ()
-- thm''' (True : xs) α β n = thm''' xs α β (α + n)
-- thm''' (False : xs) α β n = thm''' xs α β (β + n)

type N = Double

{-@ reflect α @-}
α :: N
{-@ reflect β @-}
β :: N

α = 1
β = 2

{-@ reflect foo @-}
{-@ foo :: xs:[Bool] -> n:N -> {v:N| v = n + α * countT xs + β * (len xs - countT xs)} @-}
foo :: [Bool] -> N -> N
foo []       n = n
foo (x : xs) n = if x then foo xs (n + α) else foo xs (n + β)

{-@ reflect countT @-}
countT :: [Bool] -> N
countT []           = 0
countT (True  : xs) = 1 + countT xs
countT (False : xs) = countT xs

{-@ relational foo ~ foo :: xs1:_ -> n1:_ -> _ ~ xs2:_ -> n2:_ -> _ | 
                            xs1 = xs2 => true => r1 xs1 n1 - r2 xs2 n2 = n1 - n2 @-}