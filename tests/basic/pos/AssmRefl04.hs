{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- Test for issue #2537: assume-reflected definitions should not lose
-- measure information when the actual function already has an assumed spec.

module AssmRefl04 where

import Data.Set as Set

{-@ infixr ++ @-}

test :: Int -> ()
test x = lemma ([x] ++ [x]) (Set.singleton x)

{-@ lemma :: x:[Int] -> {y:_ | Set.isSubsetOf y (Set.listElts x) } -> { Set.isSubsetOf y (Set.listElts x) } @-}
lemma :: [Int] -> Set Int -> ()
lemma _ _ = ()

{-@ reflect append @-}
{-@ assume append :: xs:[a] -> ys:[a] -> {v:[a] | len v = len xs + len ys} @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

{-@ assume reflect ++ as append @-}
