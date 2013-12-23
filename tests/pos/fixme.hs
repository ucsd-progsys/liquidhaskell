module Fixme where


pop cmp a l u = popTo cmp a l u u
{-# INLINE pop #-}

popTo cmp a l u t = undefined
{-# INLINE popTo #-}

sortHeap cmp a l m u = loop (u-1) >> unsafeSwap a l m
 where
  loop k
    | m < k     = pop cmp a l k >> loop (k-1)
    | otherwise = return ()
{- INLINE sortHeap #-}


unsafeSwap = undefined
