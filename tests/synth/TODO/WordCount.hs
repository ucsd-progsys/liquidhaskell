{-@ LIQUID "--typed-holes" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module WordCount where

-- import Data.String
import Language.Haskell.Liquid.Synthesize.Error
-----------------------------------------------------------------------------------------------------
-------------------------------------------DEFINITIONS-----------------------------------------------
-----------------------------------------------------------------------------------------------------

data List a = N | Cons a (List a)
  deriving Eq 

{-@ data List [length'] a <p :: a -> a -> Bool> = N | Cons {hd :: a, tl :: (List (a<p hd>))} @-}

{-@ measure length' @-}
{-@ length' :: List a -> Nat @-}
length' :: List a -> Int
length' N = 0
length' (Cons _ xs) = 1 + length' xs

{-@ type LPair a = (xs::List <{\h t -> h == t}> (List a), { ys: Nat | ys == length' xs }) @-}
type LPair a = (List (List a), Int)

{-@ measure fst'' @-}
{-@ fst'' :: LPair a -> List (List a) @-}
fst'' :: LPair a -> List (List a)
fst'' (x, _) = x

{-@ measure snd'' @-}
{-@ snd'' :: LPair a -> Nat @-}
snd'' :: LPair a -> Int
snd'' (_, x) = x

-----------------------------------------------------------------------------------------------------
----------------------------------------END OF DEFINITIONS-------------------------------------------
-----------------------------------------------------------------------------------------------------

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
groupBy'' _ N           = []
groupBy'' f (Cons x xs) = 
    let (ys, zs) = span'' (f x) xs 
    in  Cons x ys : groupBy'' f zs 

-- {-@ zipLen :: xs: [ List (List a)<{\h t -> h == t}> ] -> { v: [ LPair a ] | sumLen v == sLen' xs } @-} 
-- zipLen :: Eq a => [ List (List a) ] -> [ LPair a ]
-- zipLen xs = zipF' length'' xs 

{-@ zipLen0 :: xs: [ List <{\h t -> h == t}> (List a) ] -> { v: [ (xs::List <{\h t -> h == t}> (List a), Nat) ] | sumLen v == sLen xs } @-} 
zipLen0 :: Eq a => [ List (List a) ] -> [ (List (List a), Int) ]
zipLen0 xs = zipF'' length' xs 

{-@ zipF'' :: f: (List (List a) -> b) -> x: [ List (List a) ]
                -> { v: [ (y::List (List a), { z: b | z == f y}) ] | sumLen v == sLen x }
  @-}
zipF'' :: (List (List a) -> b) -> [List (List a)] -> [(List (List a), b)]
zipF'' _ []       = []
zipF'' f (x : xs) = (x, f x) : zipF'' f xs

{-@ zip' :: xs:List a -> {ys: List b | length' ys == length' xs } 
              -> { v: List (a, b) | length' v == length' xs } 
  @-}
zip' :: List a -> List b -> List (a, b) 
zip' N      N                = N
zip' (Cons x xs) (Cons y ys) = Cons (x, y) (zip' xs ys)

{-@ measure sumLen @-}
{-@ sumLen :: [ (List (List a), b) ] -> Nat @-}
sumLen :: [ (List (List a), b) ] -> Int
sumLen []          = 0
sumLen ((x, l):xs) = length' x + sumLen xs

{-@ measure sLen @-}
{-@ sLen :: [ List a ] -> Nat @-}
sLen :: [ List a ] -> Int
sLen [ ]    = 0
sLen (x:xs) = length' x + sLen xs

-- {-@ goal :: xs: List (List a) -> { v: [ LPair a ] | length' xs == sumLen v } @-}
-- goal :: Eq a => List (List a) -> [ () ]
-- -- -- goal = _hole
-- goal xs = zipLen0 (groupBy'' (==) xs) 

