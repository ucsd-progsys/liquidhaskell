-- Ensure that rewrites work with refinements
module ReWrite3 where 

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--rw-termination-check" @-}
{-@ infix ++ @-}

import Prelude hiding ((++), drop, length)

{-@ measure length @-}
{-@ length :: [a] -> Int @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

{-@ reflect drop @-}
{-@ drop :: Int -> [a] -> [a] @-}
drop :: Int -> [a] -> [a]
drop n (x:xs) = drop (n - 1) xs
drop _ []     = []
drop 0 xs     = xs

{-@ dropProof :: n : Int -> { xs : [a] | length xs >= n } -> { drop n xs = [] } @-}
dropProof :: Int -> [a] -> ()
dropProof _ []     = ()
dropProof n (_:xs) = dropProof (n - 1) xs

{-@ rewriteWith dropProof' [dropProof]  @-}
{-@ dropProof' :: n : Int -> { xs : [a] | length xs >= n } -> { drop n xs = [] } @-}
dropProof' :: Int -> [a] -> ()
dropProof' _ _ = ()

