{-@ LIQUID "--typed-holes" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module GroupByWC where

import Language.Haskell.Liquid.Synthesize.Error

data List a = N | Cons a (List a)
  deriving Eq 

{-@ data List [length'] a <p :: a -> a -> Bool> = N | Cons {hd :: a, tl :: (List (a<p hd>))} @-}

{-@ measure length' @-}
{-@ length' :: List a -> Nat @-}
length' :: List a -> Int
length' N = 0
length' (Cons _ xs) = 1 + length' xs

{-@ measure sLen @-}
{-@ sLen :: [ List a ] -> Nat @-}
sLen :: [ List a ] -> Int
sLen [ ]    = 0
sLen (x:xs) = length' x + sLen xs

{-@ span'' :: f:(a -> Bool) -> x:List a -> 
      { p:( List <{\h t -> f h && f t}> { v: a | f v }, { r: List a | length' r <= length' x } ) | length' (fst p) + length' (snd p) == length' x }
  @-}
span'' :: (a -> Bool) -> List a -> (List a, List a)
span'' _ N = (N, N)
span'' p (Cons x xs') = if p x then  let  (ys, zs) = span'' p xs' 
                                     in   (Cons x ys, zs)
                               else  let  xs = Cons x xs' in (N, xs)

{-@ groupBy'' :: p: (a -> a -> Bool) -> xs: List a
      -> { v: [ List <{\h t -> p h t}> a ] | length' xs == sLen v }
  @-} 
groupBy''  :: (a -> a -> Bool) -> List a -> [ List a ] 
groupBy'' = _goal
-- groupBy'' _ N           = []
-- groupBy'' f (Cons x xs) = 
--     let (ys, zs) = span'' (f x) xs 
--     in  Cons x ys : groupBy'' f zs 
