module ReWrite9 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding (length, (++))

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ys)

{-@ reflect length @-}
length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs


{-@ rewrite lengthSym @-}
{-@ assume lengthSym :: xs : [a] -> ys : [a] -> { length (xs ++ ys) == length (ys ++ xs) }@-}
lengthSym :: [a] -> [a] -> ()
lengthSym _ _ = ()
