{-@ LIQUID "--pruneunsorted" @-}
{-@ LIQUID "--no-termination" @-}

module Ex0 where

-- Testing "existential-types"

{-@ foldN :: forall a <p :: x0:Int -> x1:a -> Bool>. 
                (i:Int -> a<p i> -> a<p (i+1)>) 
              -> n:{v: Int | v >= 0}
              -> a <p 0> 
              -> a <p n>
  @-}

foldN :: (Int -> a -> a) -> Int -> a -> a
foldN f n = go 0 
  where 
    go i x 
      | i < n     = go (i+1) (f i x)
      | otherwise = x

{-@ goo :: forall a <pig :: x0:Int -> x1:a -> Bool>. 
                (i:Int -> a<pig i> -> a<pig (i+1)>) 
              -> i:{v: Int | 0 <= v}
              -> n:{v: Int | i <= v}
              -> a <pig i> 
              -> a <pig n>
  @-}

goo :: (Int -> a -> a) -> Int -> Int -> a -> a
goo f i n x 
  | i < n     = goo f (i+1) n (f i x) 
  | otherwise = x




{-@ count :: m: {v: Int | v > 0 } -> {v: Int | v = m} @-}
count :: Int -> Int
count m = foldN (\_ n -> n + 1) m 0

