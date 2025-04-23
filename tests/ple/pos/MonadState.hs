{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

module MonadState where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (return, (>>=))

data Pair a b = MkPair a b

{-@ data State s a = State { runState :: s -> Pair a s } @-}
data State s a     = State { runState :: s -> Pair a s }

{-@ reflect return @-}
return :: a -> State s a
return x = State $ \s -> MkPair x s

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: State s a -> (a -> State s b) -> State s b
(State x) >>= f = State $ \s -> let (MkPair a s') = x s in runState (f a) s'

{-@ leftIdentity :: x:a -> f:(a -> State s b) -> { return x >>= f = f x } @-}
leftIdentity :: a -> (a -> State s b) -> Proof
leftIdentity x f = case f x of State _ -> trivial

{-@ rightIdentity :: x:State s a -> { (x >>= return) = x } @-}
rightIdentity :: State s a -> Proof
rightIdentity (State k) = trivial

{-@ associativity :: x:State s a -> f:(a -> State s b) -> g:(b -> State s c)
                  -> { (x >>= f) >>= g = x >>= (\r:a -> f r >>= g) } @-}
associativity :: State s a -> (a -> State s b) -> (b -> State s c) -> Proof
associativity (State k) f g = trivial
