{-@ LIQUID "--higherorder" @-}

module ReflectClient2 where

import ReflectLib2

{-@ proof :: a -> { v: Int | incr 5 == 6 } @-}
proof _ = incr 5
