{-@ LIQUID "--expect-any-error" @-}
module ReWrite3 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] 
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc xs ys zs = assoc' xs ys zs

-- assoc calls assoc', therefore assoc' cannot use assoc
{-@ assoc' :: xs:[a] -> ys:[a] -> zs:[a]
          -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
assoc' :: [a] -> [a] -> [a] -> ()
assoc' _ _ _       = ()

{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ys)
