module BoolMeasure where

{-@ myhead :: {v:[a] | nonEmpty v} -> a @-}
myhead (x:_) = x

{-@ measure nonEmpty @-}   
nonEmpty :: [a] -> Bool
nonEmpty (x:xs) = True 
nonEmpty []     = False







