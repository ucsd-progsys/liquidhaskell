module MutRec where

import           Prelude                 hiding ( not )

{-@ reflect not @-}
not :: Bool -> Bool
not True  = False
not False = True

{- HLINT ignore "Use even" -}

{-@ reflect divBy2 @-}
divBy2 :: Int -> Bool
divBy2 n | n `mod` 2 == 0 = True
divBy2 _                  = False

{-@ relational isEven ~ isEven :: {n1:_ -> _ ~ n2:_ -> _ 
                               | (n1 = n2 && ((n1  mod 2) == 0) && ((n2 mod 2) == 0)) :=> (r1 n1 && r2 n2 && r1 n1 <=> (n1 mod 2 == 0) && r2 n2 <=> (n2 mod 2 == 0) )} @-}
{-@ isEven :: n:Nat -> Bool / [if n >= 0 then n else 0, 0] @-}
isEven :: Int -> Bool
isEven n | n <= 0        = True
isEven n | isOdd (n - 1) = False
isEven n                 = True

{- HLINT ignore "Redundant if" -}

{-@ relational isOdd ~ isOdd :: { n1:_ -> _ ~ n2:_ -> _ 
                             | (n1 = n2 && ((n1  mod 2) == 1) && ((n2 mod 2) == 1)) !=> (r1 n1 && r2 n2 && r1 n1 <=> (n1 mod 2 == 1) && r2 n2 <=> (n2 mod 2 == 1) )} @-}
{-@ isOdd :: n:Nat -> Bool  / [if n >= 0 then n else 0, 1] @-}
isOdd :: Int -> Bool
isOdd n | n <= 0 = False
isOdd n          = if isEven (n - 1) then False else True
