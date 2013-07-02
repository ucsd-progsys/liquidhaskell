{-# LANGUAGE MagicHash #-}
module Fixme where

import GHC.Base
import Language.Haskell.Liquid.Prelude

bar :: Int -> Int
-- bar 0 = 0
bar n = bar (n-1)


foo = bar n
  where n = choose 0

{-@ assert length :: xs:[a] -> {v: GHC.Types.Int | v = len(xs)}  @-}
length                  :: [a] -> Int
length l                =  len l 0#
  where
    --LIQUID len takes `l` as a constant 1st param in core
    {-@ Decrease len 2 @-}
    len :: [a] -> Int# -> Int
    len []     a# = I# a#
    len (_:xs) a# = len xs (a# +# 1#)

foldl        :: (a -> b -> a) -> a -> [b] -> a
foldl f z0 xs0 = lgo z0 xs0
             where
                --LIQUID lgo takes `f` as the first param, once compiled to core
                {-@ Decrease lgo 3 @-}
                lgo z []     =  z
                lgo z (x:xs) = lgo (f z x) xs
