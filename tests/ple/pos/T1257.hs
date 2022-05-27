
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1257

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1257 where

data Foo = A | B deriving (Eq)
data Bar = C | D deriving (Eq)
data Baz = E | F deriving (Eq)

-- This triggers the bug
type Alias = Bar

silly :: Foo -> Alias -> Baz

-- This renders the program safe
-- silly :: Foo -> Bar -> Baz

{-@ reflect silly @-}
silly A _ = E
silly B C = F
silly _ _ = E

{-@ test :: {silly B C = F} @-}
test = ()
