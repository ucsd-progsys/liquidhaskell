{-@ LIQUID "--expect-error-containing=Multiple instance measures `sizeOf` for type `GHC.Ptr.Ptr`" @-}
module MultiInstMeasures where

import Data.Word
import GHC.Ptr

{-@ class measure sizeOf :: forall a . Ptr a -> Int @-}

{-@ instance measure sizeOf :: (Ptr GHC.Word.Word16) -> Int
      sizeOf (Ptr x) = 2
@-}

{-@ instance measure sizeOf :: (Ptr GHC.Word.Word32) -> Int
      sizeOf (Ptr y) = 4
@-}

{-@ bar :: { p : Ptr Word32 | plen p >= (sizeOf p) } -> () @-}
bar :: Ptr Word32 -> ()
bar (Ptr unused) = ()

{-@ qux :: { p : Ptr Word32 | plen p >= 0 } -> () @-}
qux :: Ptr Word32 -> ()
qux (Ptr addr) = let x = Ptr addr in bar x

