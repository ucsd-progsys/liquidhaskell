module Fixme where

{-@ filterElts :: forall <p :: a -> Prop>. Eq a => [a<p>] -> [a] -> [a<p>] @-}
filterElts :: Eq a => [a] -> [a] -> [a]
filterElts xs ys = go xs xs ys


{-@ go :: forall <p :: a -> Prop>. Eq a => xs:[a<p>] -> ws:[a<p>] -> zs:[a] -> [a<p>] /[(len zs), (len ws)] @-}
go :: Eq a => [a] -> [a] -> [a] -> [a]
go xs (w:ws) (z:zs) | w == z    = z : go xs xs zs
                    | otherwise = go xs ws (z:zs)
go xs []     (z:zs)             = go xs xs zs
go xs ws     []                 = []

