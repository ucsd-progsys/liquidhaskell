module ReflectLib1 where

{-@ measure isNull @-}
isNull :: [a] -> Bool
isNull []     = True
isNull (x:xs) = False
