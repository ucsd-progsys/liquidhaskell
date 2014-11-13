{-@ LIQUID "--totality" @-}
{-# LANGUAGE EmptyDataDecls #-}

module PropMeasure where

{-@ myhead :: {v:[a] | nonEmpty v} -> a @-}
myhead (x:_) = x

{-@ measure nonEmpty @-}   
nonEmpty (x:xs) = true 
nonEmpty []     = false

-- | Perhaps its easiest to model `Prop` with a type like so-

data Prop = TT | FF

true :: Prop
true = TT 

false :: Prop
false = FF 

and, or :: Prop -> Prop -> Prop
and = undefined
or  = undefined

not :: Prop -> Prop
not = undefined

