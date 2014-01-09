module GhcSort () where

{-@ LIQUID "--no-termination" @-}

{-@ type OList a =  [a]<{\fld v -> (v >= fld)}>  @-}

{-@ assert sort3 :: (Ord a) => w:a -> [{v:a|v<=w}] -> OList a @-}
sort3 :: (Ord a) => a -> [a] -> [a]
sort3 w ls = qsort w ls []

qsort :: (Ord a) =>  a -> [a] -> [a] -> [a]
qsort _ []     r = r
qsort _ [x]    r = x:r
qsort w (x:xs) r = qpart w x xs [] [] r

qpart :: (Ord a) => a -> a -> [a] -> [a] -> [a] -> [a] -> [a]
qpart w x [] rlt rge r =
    rqsort x rlt (x:rqsort w rge r)
qpart w x (y:ys) rlt rge r =
    case compare x y of
        GT -> qpart w x ys (y:rlt) rge r
        _  -> qpart w x ys rlt (y:rge) r

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

