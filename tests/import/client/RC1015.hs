{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder" @-}

module RC1015 where

import RL1015

{-@ car :: f:Foo -> { v: a | fooFirst f 0 == 10 } -> Int @-}
car :: Foo -> a -> Int
car f _ = 10

zag = car (Foo bling 10) (bling 0)
