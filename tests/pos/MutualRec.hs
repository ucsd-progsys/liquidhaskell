module MutualRec where


bin = undefined
singleton = undefined

fromDistinctAscList xs
  = create const (length xs) xs
  where
    create c 0 xs' = c undefined xs'
    create c 5 xs' = case xs' of
                       ((k1,x1):(k2,x2):(k3,x3):(k4,x4):(k5,x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList create"
    create c n xs' = seq nr $ create (createR nr c) nl xs'
      where nl = n `div` 2
            nr = n - nl

    createR n c l ((k,x):ys) = create (createB l k x c) (n-1) ys
    createR _ _ _ []         = error "fromDistinctAscList createR []"
    createB l k x c r zs     = c (bin k x l r) zs


