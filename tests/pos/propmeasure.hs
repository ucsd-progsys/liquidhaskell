{-@ LIQUID "--totality" @-}
{-# LANGUAGE EmptyDataDecls #-}

module PropMeasure where

{-@ myhead :: {v:[a] | nonEmpty v} -> a @-}
myhead (x:_) = x

{-@ measure nonEmpty @-}   
nonEmpty (x:xs) = True 
nonEmpty []     = False

