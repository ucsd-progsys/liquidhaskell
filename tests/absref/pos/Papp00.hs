module Papp00 where

{-@ goo :: forall a <pig :: x0:Int -> x1:a -> Bool>.
                (i:Int -> a<pig i> -> a<pig (i+1)>) 
              -> i:{v: Int | 0 <= v}
              -> n:{v: Int | i <= v}
              -> a <pig i> 
              -> a <pig n>
              / [n - i]
  @-}

goo :: (Int -> a -> a) -> Int -> Int -> a -> a
goo f i n xink 
  | i < n     = goo f (i+1) n (f i xink) 
  | otherwise = xink

main :: IO ()
main = pure ()
