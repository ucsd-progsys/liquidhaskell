{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--etabeta"                   @-}

module MonadCont where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (return, (>>=))

{-@ data Cont r a = Cont { runCont :: (a -> r) -> r } @-}
data Cont r a = Cont { runCont :: (a -> r) -> r }

{-@ reflect return @-}
return :: a -> Cont r a
return x = Cont $ \k -> k x

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
(Cont x) >>= f = Cont $ \k -> x (\a -> runCont (f a) k)

{-@ leftIdentity :: x:a -> f:(a -> Cont r b) -> { return x >>= f = f x } @-}
leftIdentity :: a -> (a -> Cont r b) -> Proof
leftIdentity x f = case f x of Cont _ -> trivial

{-@ rightIdentity :: x:Cont r a -> { (x >>= return) = x } @-}
rightIdentity :: Cont r a -> Proof
rightIdentity (Cont k) = trivial

{-@ associativity :: x:Cont r a -> f:(a -> Cont r b) -> g:(b -> Cont r c)
                  -> { (x >>= f) >>= g = x >>= (\r:a -> f r >>= g) } @-}
associativity :: Cont r a -> (a -> Cont r b) -> (b -> Cont r c) -> Proof
associativity (Cont k) f g = trivial
