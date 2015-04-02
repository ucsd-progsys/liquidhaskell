module Goo where

import qualified Data.Set as S

data T a = T a

{-@ measure elems @-}
elems       :: T a -> S.Set a
elems (T a) = S.singleton a

{-@ inline eqelems @-}
eqelems :: Eq a => T a -> T a -> Bool
eqelems s t = (elems s) == (elems t)
         
