import Prelude hiding (null, head, tail, notElem, empty)

import Data.Vector hiding (singleton, empty)
import qualified Data.Vector.Mutable as M
import Control.Monad.Primitive
import qualified Data.Vector as V


{-@ measure mvlen :: forall a. (MVector s a) -> Int @-}
{-@ invariant {mv:MVector s a | 0 <= mvlen mv } @-}
{-@ assume M.new :: PrimMonad m => n:Nat -> m ({vs:MVector (PrimState m) a | mvlen vs == n }) @-}

{-@ minimal :: v:Vector a -> Vector a @-}
minimal :: Vector a -> Vector a
minimal v = create (M.new (V.length v) >>=  go )
    {-@ go :: in:{in:MVector (PrimState m) a | mvlen in == vlen v + 1000 } -> m (MVector (PrimState m) a) @-}
  where go :: (PrimMonad m) => MVector (PrimState m) a -> m (MVector (PrimState m) a)
        go mv = pure mv


{-@ minimal1 :: v:Vector a -> Vector a @-}
minimal1 :: Vector a -> Vector a
minimal1 mickey = create (M.new 0 >>=  go )
    {-@ go :: in:{in:MVector (PrimState m) a | mvlen in == vlen mickey + 1000 } -> m (MVector (PrimState m) a) @-}
  where go :: (PrimMonad m) => MVector (PrimState m) a -> m (MVector (PrimState m) a)
        go mv = pure mv


