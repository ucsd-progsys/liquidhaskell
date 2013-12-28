module Max where

import Prelude hiding (max, div)

{-@ max :: forall <p :: a -> Prop>. Ord a => a<p> -> a<p> -> a<p> @-}
max :: Ord a => a -> a -> a
max x y = if x >= y then x else y


plus :: Num a => a -> a -> a
plus x y = x + y


{- plus' :: forall <p :: a -> Prop>. Num a => a<p> -> a<p> -> a<p> @-}
plus' :: Num a => a -> a -> a
plus' x y = x + y



-- 
--

{-@ div :: Int -> {v:Int|v!=0} -> Int @-}
div :: Int -> Int -> Int
div = undefined


data F = F Int

foo = let z = 12 in
      let w = F z in     -- w :: F 
      case w of
      F x -> 42 `div` x


data T = T Int
{-@ data T <p :: Int -> Prop> = T (t::Int<p>) @-}

bar = let z = 12 in
      let w = T z in     -- w :: T <{v = 12}> 
      case w of
      T x -> 42 `div` x


