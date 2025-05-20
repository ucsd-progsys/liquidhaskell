{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--etabeta"                   @-}

module MonadReader where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (return, (>>=))


{-@ data Reader r a = Reader { runReader :: r -> a } @-}
data Reader r a     = Reader { runReader :: r -> a }

{-@ reflect return @-}
return :: a -> Reader r a
return x = Reader $ \y -> x

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: Reader r a -> (a -> Reader r b) -> Reader r b
(Reader x) >>= f = Reader $ \r -> runReader (f $ x r) r

{-@ readerId :: f:(Reader r a) -> { f = Reader (runReader f) } @-}
readerId :: (Reader r a) -> Proof
readerId (Reader _) = trivial

{-@ rightIdentity :: x:Reader r a -> { x >>= return = x } @-}
rightIdentity :: Reader r a -> Proof
rightIdentity (Reader _) = trivial

{-@ associativity :: x:Reader r a -> f: (a -> Reader r a) -> g:(a -> Reader r a)
                  -> { (x >>= f) >>= g = x >>= (\r:a -> f r >>= g) } @-}
associativity :: Reader r a -> (a -> Reader r a) -> (a -> Reader r a) -> Proof
associativity (Reader _) _ _ = trivial

{-@ leftIdentity :: x:a -> f:(a -> Reader r b) -> { return x >>= f = f x } @-}
leftIdentity :: a -> (a -> Reader r b) -> Proof
leftIdentity x f = case f x of Reader _ -> trivial
