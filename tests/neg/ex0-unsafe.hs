module Ex where

-- Testing "existential-types"

{-@ foldN :: forall a <p :: x0000:Int -> x1111:a -> Prop>. 
                (i:Int -> a<p i> -> a<p (i+1)>) 
              -> n:{v: Int | v >= 0}
              -> a <p 0>
              -> a <p n>
  @-}

foldN :: (Int -> a -> a) -> Int -> a -> a
foldN f n = go 0 
  where go i x | i < n     = go (i+1) (f i x)
               | otherwise = x


fooBar :: (Int -> a -> a) -> Int -> a -> a
fooBar f n = go 0
  where go i x | i < n     = go (i+1) (f i x)
               | otherwise = x


{-@ count :: m: {v: Int | v > 0 } -> {v: Int | v = 44 } @-}
count :: Int -> Int
count m = foldN (\_ n -> n + 1) m 0
-- count m = fooBar (\_ n -> n + 1) m 0
