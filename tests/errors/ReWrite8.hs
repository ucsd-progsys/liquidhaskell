{-@ LIQUID "--expect-error-containing=Could not generate any rewrites from equality" @-}
module ReWrite8 where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix ++ @-}

import Prelude hiding ((++), length, head)

{-@ measure length @-}
length :: [a] -> Int
length (_:xs) = 1 + length xs
length     [] = 0

{-@ reflect head @-}
{-@ head :: {xs : [a] | length xs >= 1} -> a @-}
head (x:_) = x

{-@ rewrite singleProof @-}
{-@ assume singleProof :: 
          { xs : [a] | True } 
      ->  { ys : [a] | True } 
      ->  { xs = ys ++ [] } @-}
singleProof :: [a] -> [a] -> ()
singleProof _ _ = ()

-- Reject both sides free vars (assumed fn)
{-@ sp :: 
          { xs : [a] | True } 
      ->  { ys : [a] | True } 
      ->  { xs = ys ++ [] } @-}
sp :: [a] -> [a] -> ()
sp _ _ = ()


{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ ys = ys 
(x:xs) ++ ys = x:(xs ++ys)


