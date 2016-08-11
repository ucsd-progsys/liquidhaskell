import Prelude hiding (null, head, tail, notElem, empty)

import Data.Vector hiding (singleton, empty)
import qualified Data.Vector.Mutable as M
import Control.Monad.Primitive
import qualified Data.Vector as V

minimal1 mickey = create (M.new 0 >>= go)

{-@ go :: {v:MVector (PrimState m) a | false } -> m (MVector (PrimState m) a) @-}
go :: (PrimMonad m) => MVector (PrimState m) a -> m (MVector (PrimState m) a)
go mv = pure mv
