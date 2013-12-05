module EmptyOr where

import GHC.Base
import GHC.ForeignPtr
import GHC.Ptr

{-@ updPtr :: forall <q :: Ptr a -> Prop>.
              (z:Ptr a -> (Ptr a)<q>) -> x:ForeignPtr a
           -> exists [p:(Ptr a)<q>].{v:ForeignPtr a | (fpLen v) = (pLen p)}
  @-}
updPtr :: (Ptr a -> Ptr a) -> ForeignPtr a -> ForeignPtr a
updPtr f (ForeignPtr p c) = case f (Ptr p) of { Ptr q -> ForeignPtr q c }
{-# INLINE updPtr #-}

{-@ measure addrLen :: Addr# -> Int @-}
{-@ measure pLen :: Ptr a -> Int
    pLen (Ptr a) = (addrLen a)
  @-}
{-@ measure fpLen :: ForeignPtr a -> Int
    fpLen (ForeignPtr a c) = (addrLen a)
  @-}
