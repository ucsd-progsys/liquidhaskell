{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--etabeta"                   @-}

module ReaderEta where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (return, Maybe(..), (>>=), const)


{-@ data Reader r a = Reader { runReader :: r -> a } @-}
data Reader r a     = Reader { runReader :: r -> a }

{-@ reflect const @-}
const :: a -> b -> a
const x _ = x

{-@ reflect return @-}
return :: a -> Reader r a
return x = Reader (const x)

{-@ reflect bindAux @-}
bindAux x f r = runReader (f (x r)) r

{-@ reflect bind @-}
bind :: Reader r a -> (a -> Reader r b) -> Reader r b
bind (Reader x) f = Reader (bindAux x f)

{-@ readerId :: f:(Reader r a) -> {f == Reader (runReader f)} @-} 
readerId :: (Reader r a) -> Proof 
readerId (Reader _) = trivial

{-@ right_identity :: x:Reader r a -> { bind x return == x } @-}
right_identity :: Reader r a -> Proof
right_identity (Reader _) = trivial


{-@ associativity :: x:Reader r a -> f: (a -> Reader r a) -> g:(a -> Reader r a) 
                        -> {bind (bind x f) g      ==  bind x (\r4:a ->(bind (f r4) g)) } @-}
associativity :: Reader r a -> (a -> Reader r a) -> (a -> Reader r a) -> Proof
associativity (Reader _) _ _ = trivial


{-@ left_identity :: x:a -> f:(a -> Reader r b) -> { bind (return x) f == f x } @-}
left_identity :: a -> (a -> Reader r b) -> Proof
left_identity x f = case f x of
    Reader _ -> trivial