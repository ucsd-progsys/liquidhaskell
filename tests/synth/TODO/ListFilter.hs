{-@ LIQUID "--typed-holes" @-}

module ListFilter where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ filter' :: forall a <p :: a -> Bool>. 
                    (x: a -> Maybe { v: a<p> | v == x }) -> xs: [a] 
                        -> { v: [ a<p> ] | S.isSubsetOf (listElts v) (listElts xs) } 
  @-}
filter' :: (a -> Maybe a) -> [a] -> [a]
-- filter' = _goal
filter' _ [ ]    = [ ]
filter' f (x:xs) =  case f x of
                        Just x' -> x' : filter' f xs
                        Nothing -> filter' f xs
