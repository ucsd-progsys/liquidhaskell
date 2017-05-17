{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}

module RL1015 where

data Foo = Foo { fooFirst :: Int -> Int , fooSnd :: Int}

{-@ data Foo = Foo { fooFirst :: Int -> Int , fooSnd :: Nat } @-}

{-@ bar :: f:Foo -> { v: a | fooFirst f 0 == 10 } -> Int @-}
bar :: Foo -> a -> Int
bar f _ = 10

{-@ reflect bling @-}
bling :: Int -> Int
bling x = 10

bag = bar (Foo bling 10) (bling 0)
