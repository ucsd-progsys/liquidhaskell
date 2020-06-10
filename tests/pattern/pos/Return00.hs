
module Return00 where



{-@ silly :: (Monad m) => m Int @-}
silly :: (Monad m) => m Int
silly = return 0 
