module RewriteClient where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--rw-termination-check" @-}

{-@ infix ++ @-}

import RewriteLib

{-@ rewriteWith assoc2 [assoc] @-}
{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws } @-}
assoc2 :: [a] -> [a] -> [a] -> [a] -> ()
assoc2 xs ys zs ws
  = () {-
    assoc xs ys (zs ++ ws)
    `const` assoc (xs ++ ys) zs ws
-}
