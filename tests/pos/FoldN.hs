{-@ LIQUID "--pruneunsorted" @-}
{-@ LIQUID "--no-termination" @-}

module FoldN () where

-- Testing "existential-types"

{-@ foldN :: forall a <p :: x0:Int -> x1:a -> Bool>. 
                (i:Int -> a<p i> -> a<p (i+1)>) 
              -> n:{v: Int | v >= 0}
              -> a <p 0> 
              -> a <p n>
  @-}

foldN :: (Int -> a -> a) -> Int -> a -> a
foldN f n = go 0 
  where go i x | i < n     = go (i+1) (f i x)
               | otherwise = x
