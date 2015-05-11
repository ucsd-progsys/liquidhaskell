module spec Data.Either where

invariant {v:[Data.Either.Either a b] | (lenRight v >= 0) && (lenRight v <= len v)}

measure lenRight :: [Data.Either.Either a b] -> GHC.Types.Int
lenRight (x:xs) = if (isLeft x) then (lenRight xs) else (lenRight xs + 1)
lenRight ([])   = 0

measure isLeftHd :: [Data.Either.Either a b] -> Prop
isLeftHd (x:xs) = (isLeft x)
isLeftHd ([])   = false

measure isLeft :: Data.Either.Either a b -> Prop 
isLeft (Left x)  = true
isLeft (Right x) = false
