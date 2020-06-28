module spec T788 where

import GHC.Base

measure mvlen     :: Data.Vector.MVector s a -> Int

invariant         {v:Data.Vector.MVector s a | 0 <= mvlen v }

assume length     :: forall a. x:(Data.Vector.MVector s a) -> {v : Nat | v = mvlen x }

assume unsafeRead :: Control.Monad.Primitive.PrimMonad m
                  => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                  -> ix:{v:Nat | v < mvlen x }
		  -> m a

assume unsafeWrite :: Control.Monad.Primitive.PrimMonad m
                   => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                   -> ix:{v:Nat | v < mvlen x }
		   -> a
		   -> m ()

assume unsafeSwap :: Control.Monad.Primitive.PrimMonad m
                  => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                  -> i:{v:Nat | v < mvlen x }
                  -> j:{v:Nat | v < mvlen x }
		  -> m ()
