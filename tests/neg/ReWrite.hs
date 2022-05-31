{-@ LIQUID "--expect-any-error" @-}
module ReWrite where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

-- Rewrites cannot prove themselves
{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc _ _ _       = ()

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ys)
