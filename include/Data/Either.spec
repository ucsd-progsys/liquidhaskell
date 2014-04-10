module spec Data.Either where

invariant {v:[Either a b] | (((lenRight v) >= 0) && ((lenRight v) <= (len v)))}
measure lenRight :: [Either a b] -> Int 
    lenRight(x:xs) = (if (isLeft x) then (lenRight xs) else ((lenRight xs) + 1))
    lenRight([])   = 0

measure isLeftHd :: [Either a b] -> Prop
    isLeftHd(x:xs) = isLeft(x)
    isLeftHd([])   = false

measure isLeft :: (Either a b) -> Prop 
    isLeft(Left x)  = true 
    isLeft(Right x) = false
