module GhcSort where

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}

{-@ assert sort3 :: (Ord a) => [a] -> OList a @-}
sort3 :: (Ord a) => [a] -> [a]
sort3 ls = qsort d1 0 0 ls d1 0 
  where d1 = (length ls) 


{-@ Decrease qsort 6 7 @-}
{-@ Decrease qpart 6 7 @-}
{-@ qs :: (Ord a) => a -> xs:[a] -> [a] -> {v:Int | v = (len xs)}-> {v:Int | v = 0} -> [a] @-}
qs = undefined
qs :: (Ord a) => a -> [a] -> [a] -> Int -> Int -> [a]
qsort:: (Ord a) => Int -> Int -> Int -> [a] -> Int -> Int -> [a]
{-@ qsort:: (Ord a) => Int -> Int -> Int -> xs:[a] -> {v:Int |v = (len xs)} -> {v:Int | v = 0} -> OList a @-}
qsort _ _  _ []  _ _  = []
-- qsort _ _ _ [x]    = [x]
qsort _ _ _ (x:xs) _ _ = qpart x xs [] [] d1 d2
  where d1 = (length xs) 
        d2 = (length xs + 1) 

qp = undefined
{-@ qp :: (Ord a) => a -> a -> q:[a] -> r:[a] -> p:[a] -> [a] -> {v:Int | v = ((len r) + (len p) + (len q))} -> {v:Int | v = (len q) + 1} -> [a] @-}
qp :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> Int -> Int -> [a]
qpart  :: (Ord a) => a -> [a] -> [a] -> [a] -> Int -> Int -> [a]
{-@ qpart  :: (Ord a) => x:a -> q:[a] -> r:[{v:a | ((true) && (v < x))}] -> p:[{v:a | ((true) && (v >= x))}] -> {v:Int | v = ((len r) + (len q) + (len p))} -> {v:Int|v = (len q) + 1} -> OList a @-}
qpart x [] rlt rge _ d =
    app x (qsort d1 d1 d2 rlt d1 d2) (x:qsort d1 d3 d2 rge d3 d2)
  where d1 = length rlt
        d2 = 0
        d3 = length rge
qpart x (y:ys) rlt rge dd d =
    case compare x y of
        GT -> qpart x ys (y:rlt) rge dd (d-1)
        _  -> qpart x ys rlt (y:rge) dd (d-1)
    where d1l = length ys + length (y:rlt) + length rge
          d1g = length ys + length rlt + length (y:rge)
          d2  = length ys + 1


{-@ app :: Ord a => x:a -> (OList ({v:a | v < x})) -> (OList ({v:a| v >= x})) -> OList a @-} 
app :: Ord a => a -> [a] -> [a] -> [a]
app k []     ys = ys
app k (x:xs) ys = x : (app k xs ys)

{-
rqsort :: (Ord a) => a -> [a] -> [a] -> [a]
rqsort _ []     r = r
rqsort _ [x]    r = x:r
rqsort w (x:xs) r = rqpart w x xs [] [] r

rqpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
rqpart w x [] rle rgt r =
    qsort x rle (x:qsort w rgt r)
rqpart w x (y:ys) rle rgt r =
    case compare y x of
        GT -> rqpart w x ys rle (y:rgt) r
        _  -> rqpart w x ys (y:rle) rgt r
-}
