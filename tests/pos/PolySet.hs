{-@ LIQUID "--reflection"     @-}

-- Tests elaboration of set operations on polymorphic types
-- see https://github.com/ucsd-progsys/liquidhaskell/issues/2272

module PolySet where

import Data.Set

data Lst a = Emp | Cons a (Lst a)

{-@ measure lstHd @-}
lstHd :: Ord a => Lst a -> Set a
lstHd  Emp       = empty
lstHd (Cons x _) = singleton x

lcons ::  Lst l -> Lst (Lst l)
{-@ lcons :: p: Lst l -> {v:Lst (Lst l) | v = Cons p Emp } @-}
lcons p = Cons p Emp
