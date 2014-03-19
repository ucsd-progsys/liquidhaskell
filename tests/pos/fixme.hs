module ToyMVar where

import Prelude hiding (IO)
data RealWorld
data State# s 

data IO a = IO (State# RealWorld -> (State# RealWorld, a))
{-@ data IO a <p :: State# -> Prop, q :: State# -> a -> Prop>
      = IO (io :: State# RealWorld -> ((State# RealWorld, a)<q>))
  @-}
instance Monad IO where
  return = returnIO
returnIO :: a -> IO a
returnIO x = IO $ \s -> (s, x)
