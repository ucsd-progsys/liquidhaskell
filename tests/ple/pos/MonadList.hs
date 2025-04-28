{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

module MonadList where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (return, (>>=), (++))

-- We define a custom list type to prevent the SMT solver from
-- making it too easy
data List a = Nil | Cons a (List a)

{-@ reflect return @-}
return :: a -> List a
return x = Cons x Nil

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
Nil         ++ ys = ys
(Cons x xs) ++ ys = x `Cons` (xs ++ ys)

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: List a -> (a -> List b) -> List b
Nil         >>= _ = Nil
(Cons x xs) >>= f = f x ++ (xs >>= f)

{-@ rightIdentity :: x:List a -> { x >>= return = x } @-}
rightIdentity :: List a -> Proof
rightIdentity Nil         = trivial
rightIdentity (Cons x xs) = rightIdentity xs

{-@ appendIdR :: xs:List a -> { xs ++ Nil = xs } @-}
appendIdR :: List a -> Proof
appendIdR Nil         = trivial
appendIdR (Cons x xs) = appendIdR xs

{-@ leftIdentity :: x:a -> f:(a -> List b) -> { return x >>= f = f x } @-}
leftIdentity :: a -> (a -> List b) -> Proof
leftIdentity x f = appendIdR $ f x

{-@ appendAssoc :: xs:List a -> ys:List a -> zs:List a
                -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc Nil         ys zs = trivial
appendAssoc (Cons x xs) ys zs = appendAssoc xs ys zs

{-@ rightDistributive :: xs:List a -> ys:List a -> f:(a -> List b)
                      -> { xs ++ ys >>= f = (xs >>= f) ++ (ys >>= f) } @-}
rightDistributive :: List a -> List a -> (a -> List b) -> Proof
rightDistributive Nil         ys f = trivial
rightDistributive (Cons x xs) ys f = rightDistributive xs ys f
                                 &&& appendAssoc (f x) (xs >>= f) (ys >>= f)

{-@ associativity :: x:List a -> f:(a -> List a) -> g:(a -> List a)
                  -> { (x >>= f) >>= g = x >>= (\r:a -> f r >>= g) } @-}
associativity :: List a -> (a -> List a) -> (a -> List a) -> Proof
associativity Nil         _ _ = trivial
associativity (Cons x xs) f g = associativity xs f g
                            &&& rightDistributive (f x) (xs >>= f) g
