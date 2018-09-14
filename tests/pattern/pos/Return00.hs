-- import Control.Monad.Primitive

{- silly :: PrimMonad m => m () @-}
-- silly :: PrimMonad m => m () 
--
{-@ silly :: (Monad m) => m () @-}
silly :: (Monad m) => m ()
silly = return () 

{-@ billy :: Int -> () @-}
billy :: Int -> ()
billy _ = () 

