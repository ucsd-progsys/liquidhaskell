import Prelude hiding (null, head, tail, notElem, empty)

import Data.Vector hiding (singleton, empty)
import qualified Data.Vector.Mutable as M
import Control.Monad.Primitive
import qualified Data.Vector as V


{-@ measure mvlen :: forall a. (MVector s a) -> Int @-}
{- assume M.new :: PrimMonad m => n:Nat -> m ({vs:MVector (PrimState m) a | mvlen vs == n }) @-}

{-@ minimal1 :: v:Vector a -> Vector a @-}
minimal1 :: Vector a -> Vector a
minimal1 mickey = create (M.new 0 >>= \zong -> go zong)
    {-@ go :: {v:MVector (PrimState m) a | 12 = 45 } -> m (MVector (PrimState m) a) @-}
  where go :: (PrimMonad m) => MVector (PrimState m) a -> m (MVector (PrimState m) a)
        go mv = pure mv


