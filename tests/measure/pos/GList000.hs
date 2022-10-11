-- TAG: absref 

module GList000 where

{-@ safeHead :: {v:[a] | false } -> a  @-} 
safeHead :: [a] -> a 
safeHead (x:_) = x 
