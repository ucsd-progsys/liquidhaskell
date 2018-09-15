import Control.Monad.Primitive

{-@ silly :: PrimMonad m => m () @-}
silly :: PrimMonad m => m () 
silly = return () 

