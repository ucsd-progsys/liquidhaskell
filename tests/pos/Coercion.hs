
{-@ LIQUID "--no-termination" @-}

module Encoding () where

data F a = F a
data BS = BS (F Int)
bar :: IO (F Int)
bar = undefined

foo = undefined


-- start ::  F Int -> IO BS
start fp = foo fp $ go
  where go ptr = do
         -- ensure :: (IO BS ~ IO b) => IO b -> IO b
         let ensure act
               | False = act
               | otherwise = do
                   fp' <- bar
                   start fp -- ((start fp) `cast` (IO BS ~ IO b)) 
         ensure $ return $ BS fp
      


