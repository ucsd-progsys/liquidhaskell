module GD where

type Dbl = Double

{-@ type StepSize = {v:Dbl|0 <= v} @-}
type StepSize = Dbl
type DataPoint = (Dbl, Dbl)
type Weight = Dbl
type LossFunction = DataPoint -> [Weight] -> Dbl

{-@ gd :: [DataPoint] -> ws:[Weight] -> StepSize -> {v:[Weight]|len v == len ws} @-}
gd :: [DataPoint] -> [Weight] -> StepSize -> [Weight]
gd []       ws _ = ws
gd (z : zs) ws α = gd zs (update z ws α) α

{-@ update :: DataPoint -> ws:[Weight] -> StepSize -> {v:[Weight]|len v = len ws} @-}
update :: DataPoint -> [Weight] -> StepSize -> [Weight]
update _ ws _ = ws

{-@ reflect diff @-}
{-@ diff :: xs:[a] -> ys:{[a]|len ys == len xs} -> {v:Dbl|0 <= v} @-}
diff :: Eq a => [a] -> [a] -> Dbl
diff (x : xs) (y : ys) | x == y = diff xs ys
diff (x : xs) (y : ys) | x /= y = 1 + diff xs ys
diff _ _                        = 0

{-@ measure dist :: [Weight] -> [Weight] -> Dbl @-}

{-@ measure loss :: LossFunction @-}
loss :: LossFunction
loss _ _ = 0

{-@ measure lip :: {v:Dbl|0 <= v} @-}
lip :: Dbl
lip = 10

{-@ relational update ~ update :: {z1:DataPoint -> ws1:[Weight] -> α1:StepSize -> {v:[Weight]|len v = len ws1}
                                ~ z2:DataPoint -> ws2:[Weight] -> α2:StepSize -> {v:[Weight]|len v = len ws2}
                               | z1 = z2 :=> true :=> true :=> 
                                    dist (r1 z1 ws1 α1) (r2 z2 ws2 α2) <= 
                                      dist ws1 ws2} @-}

{-@ relational update ~ update :: {z1:DataPoint -> ws1:[Weight] -> α1:StepSize -> {v:[Weight]|len v = len ws1}
                                ~ z2:DataPoint -> ws2:[Weight] -> α2:StepSize -> {v:[Weight]|len v = len ws2}
                               | true :=> true :=> true :=> 
                                    dist (r1 z1 ws1 α1) (r2 z2 ws2 α2) <=
                                      dist ws1 ws2 + 2.0} @-}

{-@ relational gd ~ gd :: {zs1:[DataPoint] -> ws1:[Weight] -> α1:StepSize -> {v:[Weight]|len v == len ws1} 
                        ~ zs2:[DataPoint] -> ws2:[Weight] -> α2:StepSize -> {v:[Weight]|len v == len ws2}
                       | len zs1 = len zs2 :=> true :=> true :=>
                              dist (r1 zs1 ws1 α1) (r2 zs2 ws2 α2) <= 
                                  dist ws1 ws2 + 2.0 * GD.diff zs1 zs2} @-}
