{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage wxs = divide totElems totWeight 
  where
    elems     = map (\(w, x) -> w * x) wxs
    weights   = map (\(w, _) -> w    ) wxs
    totElems  = sum elems 
    totWeight = sum weights 

{-@ map       :: (a -> b) -> [a] -> [b]  @-}
map _ []      = []
map f (x:xs)  = f x : map f xs 

sum []        = die "cannot add up empty list"
sum _         = foldr1 (+)
