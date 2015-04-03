module Goo where

import qualified Data.Set as S

data T a = T a

{-@ measure elems @-}
elems       :: T a -> S.Set a
elems (T a) = S.singleton a

{-@ member :: x:a -> t:T a -> {v:Bool | Prop v <=> S.member x (elems t)} @-}
member :: a -> T a -> Bool
member = undefined

        
