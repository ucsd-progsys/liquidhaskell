-- Rewrites should be applied recursively
module ReWrite5 where

{-@ LIQUID "--max-rw-ordering-constraints=0" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

{-@ rewriteWith assoc3 [assoc] @-} 
{-@ assoc3 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a] -> vs:[a]
          -> { xs ++ (ys ++ (zs ++ (ws ++ vs))) == (((xs ++ ys) ++ zs) ++ ws) ++ vs } @-}
assoc3 :: [a] -> [a] -> [a] -> [a] -> [a] -> ()
assoc3 xs ys zs ws vs = ()

{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a]
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:xs) ys zs = assoc xs ys zs

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ys)
