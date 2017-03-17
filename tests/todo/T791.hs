import Prelude hiding (null, head, tail, notElem, empty)

import Data.Vector hiding (singleton, empty)
import qualified Data.Vector.Mutable as M
import qualified Data.Vector as V
import Control.Monad.Primitive

{-@ measure mvlen :: forall a. (MVector s a) -> Int @-}
{-@ invariant {mv:MVector s a | 0 <= mvlen mv } @-}
{-@ assume Data.Vector.Mutable.new :: PrimMonad m => n:Nat -> m ({vs:MVector (PrimState m) a | mvlen vs == n }) @-}

{-@ minimal :: v:Vector a -> Vector a @-}
minimal :: Vector a -> Vector a
minimal v = create (M.new n >>= (\x -> go n x))
  where
    {-@ n :: {n:Nat | n == vlen v} @-}
    n = V.length v
    {-@ go :: n:Nat -> {mv:MVector (PrimState m) a | mvlen mv == n} -> m (MVector (PrimState m) a) @-}
    go :: (PrimMonad m) => Int -> MVector (PrimState m) a -> m (MVector (PrimState m) a)
    go _ mv = pure mv

{-@ qualif EqLen(v:MVector s a, x:Vector b): (mvlen v == vlen x) @-}
{-@ qualif MVLen(v:MVector s a, n:Int): (mvlen v == n) @-}
