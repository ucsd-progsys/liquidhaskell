sort = sortBy compare
sortBy cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `cmp` b == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | a `cmp` b == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = as [a]: sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = merge a b: mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as

{-
sortBy cmp l = mergesort cmp l
sort l = mergesort compare l

Quicksort replaced by mergesort, 14/5/2002.

From: Ian Lynagh <igloo@earth.li>

I am curious as to why the List.sort implementation in GHC is a
quicksort algorithm rather than an algorithm that guarantees n log n
time in the worst case? I have attached a mergesort implementation along
with a few scripts to time it's performance, the results of which are
shown below (* means it didn't finish successfully - in all cases this
was due to a stack overflow).

If I heap profile the random_list case with only 10000 then I see
random_list peaks at using about 2.5M of memory, whereas in the same
program using List.sort it uses only 100k.

Input style     Input length     Sort data     Sort alg    User time
stdin           10000            random_list   sort        2.82
stdin           10000            random_list   mergesort   2.96
stdin           10000            sorted        sort        31.37
stdin           10000            sorted        mergesort   1.90
stdin           10000            revsorted     sort        31.21
stdin           10000            revsorted     mergesort   1.88
stdin           100000           random_list   sort        *
stdin           100000           random_list   mergesort   *
stdin           100000           sorted        sort        *
stdin           100000           sorted        mergesort   *
stdin           100000           revsorted     sort        *
stdin           100000           revsorted     mergesort   *
func            10000            random_list   sort        0.31
func            10000            random_list   mergesort   0.91
func            10000            sorted        sort        19.09
func            10000            sorted        mergesort   0.15
func            10000            revsorted     sort        19.17
func            10000            revsorted     mergesort   0.16
func            100000           random_list   sort        3.85
func            100000           random_list   mergesort   *
func            100000           sorted        sort        5831.47
func            100000           sorted        mergesort   2.23
func            100000           revsorted     sort        5872.34
func            100000           revsorted     mergesort   2.24

mergesort :: (a -> a -> Ordering) -> [a] -> [a]
mergesort cmp = mergesort' cmp . map wrap

mergesort' :: (a -> a -> Ordering) -> [[a]] -> [a]
mergesort' _   [] = []
mergesort' _   [xs] = xs
mergesort' cmp xss = mergesort' cmp (merge_pairs cmp xss)

merge_pairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
merge_pairs _   [] = []
merge_pairs _   [xs] = [xs]
merge_pairs cmp (xs:ys:xss) = merge cmp xs ys : merge_pairs cmp xss

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _   [] ys = ys
merge _   xs [] = xs
merge cmp (x:xs) (y:ys)
 = case x `cmp` y of
        GT -> y : merge cmp (x:xs)   ys
        _  -> x : merge cmp    xs (y:ys)

wrap :: a -> [a]
wrap x = [x]



OLDER: qsort version

-- qsort is stable and does not concatenate.
qsort :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
qsort _   []     r = r
qsort _   [x]    r = x:r
qsort cmp (x:xs) r = qpart cmp x xs [] [] r

-- qpart partitions and sorts the sublists
qpart :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [a] -> [a] -> [a]
qpart cmp x [] rlt rge r =
    -- rlt and rge are in reverse order and must be sorted with an
    -- anti-stable sorting
    rqsort cmp rlt (x:rqsort cmp rge r)
qpart cmp x (y:ys) rlt rge r =
    case cmp x y of
        GT -> qpart cmp x ys (y:rlt) rge r
        _  -> qpart cmp x ys rlt (y:rge) r

-- rqsort is as qsort but anti-stable, i.e. reverses equal elements
rqsort :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
rqsort _   []     r = r
rqsort _   [x]    r = x:r
rqsort cmp (x:xs) r = rqpart cmp x xs [] [] r

rqpart :: (a -> a -> Ordering) -> a -> [a] -> [a] -> [a] -> [a] -> [a]
rqpart cmp x [] rle rgt r =
    qsort cmp rle (x:qsort cmp rgt r)
rqpart cmp x (y:ys) rle rgt r =
    case cmp y x of
        GT -> rqpart cmp x ys rle (y:rgt) r
        _  -> rqpart cmp x ys (y:rle) rgt r
-}

#endif /* USE_REPORT_PRELUDE */

