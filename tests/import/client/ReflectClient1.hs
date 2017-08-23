module ReflectClient0 where

import ReflectLib1

{-@ myHead :: {v:[a] | not (isNull v) } -> a @-}
myHead :: [a] -> a
myHead (x:_) = x
