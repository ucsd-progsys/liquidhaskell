{-@ LIQUID "--no-termination" @-}
module Until where

import Prelude hiding (until)

{-@ until :: forall <p :: a -> Prop, i :: a -> Prop>.
             (a:a<i> -> {v:Bool | Prop v <=> papp1 p a})
          -> ({v:a<i> | not (papp1 p v)} -> a<i>)
          -> a<i>
          -> a<p>
  @-}
until :: (a -> Bool) -> (a -> a) -> a -> a
until p f = go
  where
    go x | p x          = x
         | otherwise    = go (f x)

{-@ predicate Btwn Lo N Hi = Lo <= N && N < Hi @-}
{-@ predicate Uint8 N = Btwn 0 N 256 @-}


{-@ assume addUint8 :: x:{Int | Uint8 x} -> y:{Int | Uint8 y && Uint8 (x+y)}
                    -> {v:Int | Uint8 v && v = x + y}
  @-}
addUint8 :: Int -> Int -> Int
addUint8 = (+)

{-@ ten :: {v:Int | Uint8 v && v >= 10} @-}
ten = until (\x -> gt10 x) (\x -> add1 x) 0 

{-@ gt10 :: x:Int -> {v:Bool | Prop v <=> x >= 10} @-}
gt10 :: Int -> Bool
gt10 x = x >= 10

{-@ add1 :: x:{Int | Btwn 0 x 255} -> {v:Int | Uint8 v && v = x +1} @-}
add1 x = addUint8 x 1


{-@ untilMono :: (x:{Int | Uint8 x && x <= 10} -> {v:Bool | Prop v <=> x >= 10})
              -> ({v:Int | Uint8 v && v < 10} -> {v:Int | Uint8 v && v <= 10})
              -> {v:Int | Uint8 v && v <= 10}
              -> {v:Int | Uint8 v && v >= 10}
  @-}
untilMono :: (Int -> Bool) -> (Int -> Int) -> Int -> Int
-- untilMono p f x = until p f x
untilMono p f = go
  where
    go x | p x          = x
         | otherwise    = go (f x)

{-@ tenMono :: {v:Int | Uint8 v && v >= 10} @-}
tenMono = untilMono gt10 add1 0 
