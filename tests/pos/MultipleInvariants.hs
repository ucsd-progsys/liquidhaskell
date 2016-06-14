module Blank where

import Data.Word
import GHC.Ptr


{-@ measure sizeOf :: forall a . Ptr a -> Int @-}

{-@ invariant {v:Ptr Word16 | sizeOf v = 2} @-}
{-@ invariant {v:Ptr Word32 | sizeOf v = 4} @-}


{-@ bar :: p:_ -> {v:_ | sizeOf p == 4 }@-}
bar :: Ptr Word32 -> ()
bar (Ptr _) = ()

{-@ foo :: p:_ -> {v:_ | sizeOf p == 2 }@-}
foo :: Ptr Word16 -> ()
foo (Ptr _) = ()

