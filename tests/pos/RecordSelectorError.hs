module RecordSelectorError where

data F a b = F {fx :: a, fy :: b} | G {fx :: a}
{-@ data F a b = F {fx :: a, fy :: b} | G {fx :: a} @-}

{-@ measure isF @-}
isF :: F a b -> Bool
isF (F x y) = True 
isF (G x)   = False

-- Record's selector type it defaulted to true as imported
{-@ fy  :: {v:F a b | isF v} -> b @-}
{-@ bar :: {v:F a b | isF v} -> b @-}
bar :: F a b  -> b
bar = fy


