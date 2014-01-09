module GhcSort () where

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}

{-@ assert sort3 :: (Ord a) => w:a -> [{v:a|v<=w}] -> OList a @-}
sort3 :: (Ord a) => a -> [a] -> [a]
sort3 w ls = qsort w ls [] (length ls) 0

{-@ Decrease qsort 5 6 @-}
{-@ Decrease rqsort 5 6 @-}
{-@ Decrease qpart 8 9 @-}
{-@ Decrease rqpart 8 9 @-}
qsort :: (Ord a) =>  a -> [a] -> [a] -> Int -> Int -> [a]
{-@ qsort, rqsort :: (Ord a) =>  w:a -> xs:[{v:a|v<=w}] -> OList {v:a|v>=w} -> {v:Int | v = (len xs) } -> {v:Int | v = 0 } -> OList a @-}
qsort _ []     r _ _ = r
qsort _ [x]    r _ _ = x:r
qsort w (x:xs) r _ _ = qpart w x xs [] [] r (length xs) (length xs + 1)

{-@ qpart, rqpart :: (Ord a) => w:a -> x:{v:a|v<=w} -> xs:[{v:a|v <= w}] -> lt:[{v:a|((v<=x) && (v<=w))}] -> ge:[{v:a|((v >= x) && (v<=w))}] -> rs:(OList {v:a|v >= w}) -> {v:Int | v = ((len xs) + (len lt) + (len ge))} -> {v:Int|v = (len xs) + 1} -> OList a @-}
qpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> Int -> Int -> [a]
qpart w x [] rlt rge r _ _ =
    rqsort x rlt (x:rqsort w rge r (length rge) 0) (length rlt) 0
qpart w x (y:ys) rlt rge r d1 d2 =
    case compare x y of
        GT -> qpart w x ys (y:rlt) rge r d1 (d2 - 1)
        _  -> qpart w x ys rlt (y:rge) r d1 (d2 - 1)

{- rqsort :: (Ord a) =>  w:a -> xs:[{v:a|v<=w}] -> OList {v:a|v>=w} -> {v:Int | v = (len xs) } -> {v:Int | v = 0 } -> OList a @-}
rqsort :: (Ord a) => a -> [a] -> [a] -> Int -> Int -> [a]
rqsort _ []     r _ _ = r
rqsort _ [x]    r _ _ = x:r
rqsort w (x:xs) r _ _ = rqpart w x xs [] [] r (length xs) (length xs + 1)

rqpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> Int -> Int -> [a]
rqpart w x [] rle rgt r _ _ =
    qsort x rle (x:qsort w rgt r (length rgt) 0) (length rle) 0 
rqpart w x (y:ys) rle rgt r d1 d2 =
    case compare y x of
        GT -> rqpart w x ys rle (y:rgt) r d1 (d2-1)
        _  -> rqpart w x ys (y:rle) rgt r d1 (d2-1)

