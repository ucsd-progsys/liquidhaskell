module MaybeMonad where

import Prelude hiding (take)

{-@ monadicStyle :: Pos -> [a] -> Maybe [a] @-}
monadicStyle i xs =
  do checkSizeMaybe i head xs
     return (take i xs)

{-@ maybeStyle :: Pos -> [a] -> Maybe [a] @-}
maybeStyle i xs =
  case checkSizeMaybe i head xs of 
    Just _  -> Just $ take i xs 
    Nothing -> Nothing 


{-@ type Pos = {v:Int | 0 < v } @-}

{-@
checkSizeMaybe :: 
       n:Nat
    -> (bs:{[a] | n <= len bs } -> b)
    -> bs:[a]
    -> {v:Maybe b | isJust v => n <= len bs}
@-}

checkSizeMaybe :: Int -> ([a] -> b) -> [a] -> Maybe b
checkSizeMaybe sz f bs
  | length bs >= sz = Just (f bs)
  | otherwise       = Nothing

{-@ take :: i:Nat -> xs:{[a] | i <= len xs} -> [a] @-} 
take :: Int -> [a] -> [a]
take 0 []        = [] 
take i (x:xs) = if i == 0 then [] else x:(take (i-1) xs)