{-@ LIQUID "--totality" @-}
{-# LANGUAGE EmptyDataDecls #-}

module PropMeasure where

{-@ myhead :: {v:[a] | nonEmpty v} -> a @-}
myhead (x:_) = x

{-@ measure nonEmpty @-}   
nonEmpty (x:xs) = True 
nonEmpty []     = False



{-@ foo  :: x:[a] -> {v: Bool | (Prop v) <=> (nonEmpty x) } @-}
foo  :: [a] -> Bool
foo x = nonEmpty x
