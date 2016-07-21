module spec Data.Vector.Mutable where

import GHC.Base

measure mvlen     :: Data.Vector.MVector s a -> Int

invariant         {v:Data.Vector.MVector s a | 0 <= mvlen v }

assume length     :: forall a. x:(Data.Vector.MVector s a) -> {v : Nat | v = mvlen x }

assume unsafeRead :: Control.Monad.Primitive.PrimMonad m
                  => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                  -> ix:{v:Nat | v < mvlen x }
		  -> (m a)

assume unsafeWrite :: Control.Monad.Primitive.PrimMonad m
                   => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                   -> ix:{v:Nat | v < mvlen x }
		   -> a
		   -> (m ())

assume unsafeSwap :: Control.Monad.Primitive.PrimMonad m
                  => x:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                  -> i:{v:Nat | v < mvlen x }
                  -> j:{v:Nat | v < mvlen x }
		  -> (m ())

assume unsafeInit :: x:{v:(Data.Vector.MVector s a) | mvlen v > 0}
                  -> {y:(Data.Vector.MVector s a) | mvlen y == mvlen x - 1}

assume unsafeNew :: Control.Monad.Primitive.PrimMonad m
                 => x:Nat
		 -> (m {v:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a) | mvlen v = x})

assume unsafeDrop :: n:Nat
                  -> in:(Data.Vector.MVector s a)
		  -> {out:(Data.Vector.MVector s a) | if (n <= mvlen in)
		                                        then (mvlen out == mvlen in - n)
							else (mvlen out == 0) }

assume unsafeTake :: n:Nat
                  -> in:(Data.Vector.MVector s a)
		  -> {out:(Data.Vector.MVector s a) | if (n <= mvlen in)
		                                        then (mvlen out == n)
							else (mvlen out == mvlen in) }

assume unsafeCopy :: Control.Monad.Primitive.PrimMonad m
                  => in1:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a)
                  -> in2x:{in2:(Data.Vector.MVector (Control.Monad.Primitive.PrimState m) a) | mvlen in1 = mvlen in2}
		  -> (m ())
