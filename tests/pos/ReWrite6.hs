-- Should be able to apply multiple rewrite rules
module ReWrite6 where

{-@ LIQUID "--max-rw-ordering-constraints=0" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

{-@ rewriteWith assoc2 [assoc, identity] @-} 
{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws ++ [] } @-}
assoc2 :: [a] -> [a] -> [a] -> [a] -> ()
assoc2 xs ys zs ws = ()

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:xs) ys zs = assoc xs ys zs

{-@ identity :: xs:[a] -> {xs = xs ++ [] }@-}
identity []     = ()
identity (x:xs) = identity xs

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ys)

