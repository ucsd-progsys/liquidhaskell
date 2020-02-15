{-@ LIQUID "--typed-holes" @-}

module ListSplit where

import qualified Data.Set as S

-- Case split on expressions 
{-@ split :: xs: [a] -> 
    { v: ( [a], [a] ) | len xs == len (fst v) + len (snd v) && 
                        listElts xs == S.union (listElts (fst v)) (listElts (snd v)) }    
 @-}
split :: [a] -> ([a], [a])
split = _goal
