{-@ LIQUID "--reflection"     @-}

module PolyBag where

import Language.Haskell.Liquid.Bag

data Lst a = Emp | Cons a (Lst a)

{-@ measure lstHd @-}
lstHd :: Ord a => Lst a -> Bag a
lstHd  Emp       = empty
lstHd (Cons x _) = put x empty

{-@ lcons :: p: Lst l -> {v:Lst (Lst l) | v = Cons p Emp } @-}
lcons :: Lst l -> Lst (Lst l)
lcons p = Cons p Emp
