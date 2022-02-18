{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--checks=lma_msort" @-}

{-# LANGUAGE GADTs #-}

module Merge where

import           Prelude hiding ((++)) 
import           Language.Haskell.Liquid.ProofCombinators ((?), (===), (=>=), (***), (&&&), Proof, QED(..))

------------------------------
-- | Array Definitions
------------------------------

type Array a = [a]

{-@ reflect make @-}
{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n} @-}
make :: Int -> a -> Array a
make 0 x = []
make n x = (x:(make (n-1) x))

{-@ measure size @-}
-- {-@ reflect size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size [] = 0
size (_:xs) = 1 + (size xs)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (x:_) 0 = x
get (_:xs) n = get xs (n-1)

{-@ reflect set @-}
{-@ set :: xs:_ -> {n:Nat | n < size xs } -> x:_ -> nxs:{(size nxs) = (size xs)} @-}
set :: Array a -> Int -> a -> Array a
set (x:xs) 0 y = (y:xs)
set (x:xs) n y = x:(set xs (n-1) y)


-- lemma showing that get n from set n xs x is x
{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_ 
      -> { pf:_ | get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (x:xs) 0 x' 
  = get (set (x:xs) 0 x') 0 
  -- === get (x':xs) 0
  === x'
  *** QED
lma_gs (x:xs) n x' 
  =  get (set (x:xs) n x') n
  -- === get (x:(set xs (n-1) x')) n
  -- === get (set xs (n-1) x') (n-1)
    ? lma_gs xs (n-1) x'
  === x'
  *** QED

-- lemma showing that get n from set m xs x is 
{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs } -> m:{v:Nat | v /= n && v < size xs} -> x:_ 
      -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (x:xs) 0 m x'
  = get (set (x:xs) 0 x') m
  -- === get (x':xs) m
  -- === get xs (m-1)
  === get (x:xs) m
  *** QED

lma_gns (x:xs) n 0 x'
  = get (set (x:xs) n x') 0
  -- === get (x:(set xs (n-1) x')) 0
  -- === x
  === get (x:xs) 0
  *** QED

lma_gns (x:xs) n m x'
  = get (set (x:xs) n x') m
  -- === get (x:(set xs (n-1) x')) m
  -- === get (set xs (n-1) x') (m-1)
    ? lma_gns xs (n-1) (m-1) x'
  -- === get xs (m-1)
  === get (x:xs) m
  *** QED

-----------------------------
-- | Order Properties
-----------------------------

-- subfunctions in measure has to be measure as well? TODO:
{-@ reflect isSorted @-}
isSorted :: Ord a => Array a -> Bool
isSorted xs = isSortedFstN xs (size xs)


{-@ reflect isSortedFstN @-}
{-@ isSortedFstN :: xs:_ -> m:{n:Nat | n <= size xs} -> b:_ / [m] @-}
isSortedFstN :: Ord a => Array a -> Int -> Bool
isSortedFstN xs 0 = True
isSortedFstN xs 1 = True
isSortedFstN xs n = ((get xs (n-2)) <= (get xs (n-1))) && (isSortedFstN xs (n-1))

-- lemma showing that isSorted xs implies isSorted for first n when n in range
{-@ lma_is_isfn :: xs:{isSorted xs} -> n:{v:Nat |  v <= size xs} 
      -> { pf:_ | isSortedFstN xs n} / [n] @-}
lma_is_isfn :: Ord a => Array a -> Int -> Proof
lma_is_isfn xs n 
  = True
  -- === isSorted xs
  -- === isSortedFstN xs (size xs)
    ? lma_isfn1 xs (size xs) n
  === isSortedFstN xs n
  *** QED


-- lemma showing that set xs n x does not change the fact that the first m<n of xs is sorted
{-@ lma_isfn_set :: xs:_ -> x:_ -> n:{v:Nat |  v < size xs} -> m:{v:Nat | v <= n } 
      -> {(isSortedFstN (set xs n x) m) = (isSortedFstN xs m)} / [m] @-}
lma_isfn_set :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_isfn_set xs x n 0 = ()
lma_isfn_set xs x n 1 = ()
lma_isfn_set xs x n m 
  = isSortedFstN (set xs n x) m
  -- === (((get (set xs n x) (m-2)) <= (get (set xs n x) (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? (lma_gns xs n (m-2) x) &&& (lma_gns xs n (m-1) x)
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? lma_isfn_set xs x n (m-1)
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN xs (m-1)))
  === isSortedFstN xs m
  *** QED


-- lemma showing (isSortedFstN xs n) => (isSortedFstN xs m) for all m < n
{-@ lma_isfn1 :: xs:_ -> n:{v:Nat | v <= size xs && (isSortedFstN xs v)} -> m:{v:Nat | v <= n} 
      -> { pf:_ | isSortedFstN xs m} / [n-m] @-}
lma_isfn1 :: Ord a => Array a -> Int -> Int -> Proof
lma_isfn1 xs n 0 = () -- TODO: this line is necessary?
lma_isfn1 xs n m | m == (n) = ()
           | otherwise = True
    ? lma_isfn1 xs n (m+1)
  -- === isSortedFstN xs (m+1)
  -- === (((get xs (m-1)) <= (get xs (m))) && (isSortedFstN xs (m)))
  === (isSortedFstN xs (m))
  *** QED


--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------
 
-- >>>  merge [1:3:4:6] [2:5] 4 2

-- merging the first n,m indices of xs, ys
{-@ reflect merge @-}
{-@ merge :: xs:_ -> ys:_ -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v <= size ys} 
      -> zs:{(size zs) = ((size xs) + (size ys))} / [m+n] @-}
merge :: Ord a => Array a -> Array a -> Int -> Int -> Array a
merge [] ys _ _ = ys
merge xs ys 0 0 = (make ((size xs)+(size ys)) (get xs 0))
merge xs ys 0 m = let zs = merge xs ys 0 (m-1) in (set zs (m-1) (get ys (m-1)))
merge xs ys n 0 = let zs = merge xs ys (n-1) 0 in (set zs (n-1) (get xs (n-1)))
merge xs ys n m | xs_n <= ys_m = let zs = merge xs ys (n) (m-1)   
                                  in (set zs (m+n-1) ys_m)
                | otherwise    = let zs = merge xs ys (n-1) (m) 
                                  in (set zs (m+n-1) xs_n)
                  where 
                    xs_n = get xs (n-1)
                    ys_m = get ys (m-1) 


-- >>>  msort (fromList [1,3,2,9,6,0,5,2,10,-1])

-- TODO: Inefficient implementation 
-- need to show xs == ys 
{-@ reflect msort @-}
{-@ msort :: xs:_ -> ys:{(size ys == size xs)} / [size xs] @-}
msort :: Ord a => Array a -> Array a
msort xs | (size xs) == 0 = xs
         | (size xs) == 1 = xs
         | otherwise      = let  
                              ls' = (msort ls)
                              rs' = (msort rs)
                              (ls, rs) = splitMid xs
                            in merge ls' rs' (size ls') (size rs')


{-@ reflect splitMid @-}
{-@ splitMid :: xs:{size xs >= 2} -> {t:_ | ((size (fst t)) < (size xs) && (size (snd t)) < (size xs)) && (size xs = (size (fst t)) + (size (snd t)))} @-}
splitMid :: Array a -> (Array a, Array a)
splitMid xs = ((subArray xs 0 m m), (subArray xs m n (n-m)))
  where 
    n = size xs 
    m = mydiv n

{-@ reflect subArray @-}
{-@ subArray :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> c:{v:Nat | v <= m-n} -> {ys:_ | size ys == m-n} / [c] @-}
subArray :: Array a -> Int -> Int -> Int -> Array a
subArray xs n m 0 = make (m-n) (get xs 0)  
subArray xs n m c = set (subArray xs n m (c-1)) (c-1) (get xs (n+c-1))

-- mydiv n = div n 2
{-@ reflect mydiv @-}
{-@ mydiv :: n:{n >= 2} -> m:{v:Nat | (v > 0 && v < n)} @-}
mydiv :: Int -> Int
mydiv 2 = 1
mydiv 3 = 1 
mydiv n = 1 + (mydiv (n-2))

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

-- TODO: I really want to get rid of the edge cases where n-1 can be -1
-- FIXME: constrains z >= (get xs (n-1)) does not enforce n > 0, but it makes the program into a loop
--        nor does it check the constrain of n when i am calling this method, another loop
-- n = 0 implies  -- TODO: Forever loop, Not working
-- {-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{  ((n > 0) => (z >= (get xs (n-1)))) && z >= (get ys (m-1))}
      -- -> { z >= get (merge xs ys n m) (n+m-1) } @-}
{-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v > 0 && v <= size xs} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{  z >= (get xs (n-1)) && z >= (get ys (m-1))} 
      -> { pf:_ | z >= get (merge xs ys n m) (n+m-1) } @-}
lma_merge_max ::  Ord a => Array a -> Array a -> Int -> Int -> a -> Proof
-- lma_merge_max xs ys 0 m z 
--   = z
--   =>= ys_m
--     ? lma_gs zs (m-1) ys_m
--   === get (set zs (m-1) ys_m) (m-1)
--   === get (merge xs ys 0 m) (m-1)
--   *** QED
--     where 
--       zs  = merge xs ys 0 (m-1)
--       ys_m = get ys (m-1)
lma_merge_max xs ys n m z 
  | xs_n <= ys_m 
    = z
    =>= ys_m
      ? lma_gs zs (m+n-1) ys_m
    -- === get (set zs (m+n-1) ys_m) (m+n-1)
    === get (merge xs ys n m) (m+n-1)
    *** QED
  | otherwise
    = z
    =>= xs_n
      ? lma_gs zs' (m+n-1) xs_n
    -- === get (set zs' (m+n-1) xs_n) (m+n-1)
    === get (merge xs ys n m) (m+n-1)
    *** QED
      where 
        zs  = merge xs ys n (m-1)
        zs' = merge xs ys (n-1) m
        xs_n = get xs (n-1)
        ys_m = get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_m :: xs:_ -> ys:{isSorted ys} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{ z >= (get ys (m-1))}
      -> { pf:_ | z >= get (merge xs ys 0 m) (m-1) } @-}
lma_merge_max_m ::  Ord a => Array a -> Array a -> Int -> a -> Proof
lma_merge_max_m xs ys m z 
  = z
  =>= ys_m
    ? lma_gs zs (m-1) ys_m
  -- === get (set zs (m-1) ys_m) (m-1)
  === get (merge xs ys 0 m) (m-1)
  *** QED
    where
      zs  = merge xs ys 0 (m-1)
      ys_m = get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_n :: xs:{isSorted xs} -> ys:_ -> n:{v:Nat | v > 0 && v <= size xs} -> z:{ z >= (get xs (n-1))}
      -> { pf:_ | z >= get (merge xs ys n 0) (n-1) } @-}
lma_merge_max_n ::  Ord a => Array a -> Array a -> Int -> a -> Proof
lma_merge_max_n xs ys n z 
  = z
  =>= xs_n
    ? lma_gs zs (n-1) xs_n
  -- === get (set zs (n-1) xs_n) (n-1)
  === get (merge xs ys n 0) (n-1)
  *** QED
    where
      zs  = merge xs ys (n-1) 0
      xs_n = get xs (n-1)


-- Commenting out intermediate steps greatly reduces the runtime (12'5 -> 3'53)
-- showing the output of merge is sorted if the inputs are sorted
-- TODO: Interesting observation: one less line of proof increase the compile time by 1/5 (from 100s to 80s)
{-@ lma_merge :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v <= size ys} 
      -> { pf:_ | isSortedFstN (merge xs ys n m) (n+m)} / [n+m] @-}
lma_merge :: Ord a => Array a -> Array a -> Int -> Int -> Proof
-- -- lma_merge [] ys _ _ = ()
lma_merge xs ys 0 0 = ()
lma_merge xs ys 0 1 = ()
lma_merge xs ys 1 0 = ()
lma_merge xs ys 0 m 
  = isSortedFstN mer1 m
  -- === (((get mer1 (m-2)) <= (get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((get mer2 (m-2)) <= (get mer2 (m-1))) && (isSortedFstN mer2 (m-1)))
    ? (lma_gs zs (m-1) ys_m) &&& (lma_gns zs (m-1) (m-2) ys_m)
  -- === (((get zs (m-2)) <= ys_m) && (isSortedFstN mer2 (m-1)))
    ? lma_isfn_set zs ys_m (m-1) (m-1)
  -- === (((get zs (m-2)) <= ys_m) && (isSortedFstN zs (m-1)))
    ? lma_merge xs ys 0 (m-1)
  -- === ((get zs (m-2)) <= ys_m)
    ? lma_merge_max_m xs ys (m-1) (ys_m ? lma_is_isfn ys m)
  === True
  *** QED
    where 
      mer1 = (merge xs ys 0 m)
      mer2 = (set zs (m-1) ys_m)
      zs =  merge xs ys 0 (m-1)
      ys_m = (get ys (m-1))
lma_merge xs ys n 0 
  = isSortedFstN mer1 n
  -- === (((get mer1 (m-2)) <= (get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((get mer2 (n-2)) <= (get mer2 (n-1))) && (isSortedFstN mer2 (n-1)))
    ? (lma_gs zs (n-1) xs_n) &&& (lma_gns zs (n-1) (n-2) xs_n)
  -- === (((get zs (n-2)) <= xs_n) && (isSortedFstN mer2 (n-1)))
    ? lma_isfn_set zs xs_n (n-1) (n-1)
  -- === (((get zs (n-2)) <= xs_n) && (isSortedFstN zs (n-1)))
    ? lma_merge xs ys (n-1) 0
  -- === ((get zs (n-2)) <= xs_n)
    ? lma_merge_max_n xs ys (n-1) (xs_n ? lma_is_isfn xs n)
  === True
  *** QED
    where 
      mer1 = (merge xs ys n 0)
      mer2 = (set zs (n-1) xs_n)
      zs =  merge xs ys (n-1) 0
      xs_n = (get xs (n-1))

lma_merge xs ys n m = 
  let 
    mer1 = (merge xs ys n m)
    mer2 = (set zs1 (m+n-1) ys_m)
    mer3 = (set zs2 (m+n-1) xs_n)
    zs1 = merge xs ys n (m-1)
    zs2 = merge xs ys (n-1) m
    xs_n = get xs (n-1)
    ys_m = get ys (m-1)
    merged = (set (merge xs ys (n) (m-1)) (m+n-1) ys_m) 
  in case xs_n <= ys_m of
    True -> isSortedFstN mer1 (n+m)
      -- === (((get mer1 (n+m-2)) <= (get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((get mer2 (n+m-2)) <= (get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_gs zs1 (n+m-1) ys_m) &&& (lma_gns zs1 (n+m-1) (n+m-2) ys_m)
      -- === (((get zs1 (n+m-2)) <= ys_m) &&  (isSortedFstN mer2 (n+m-1)))
        ? lma_isfn_set zs1 ys_m (n+m-1) (n+m-1)
      -- === (((get zs1 (n+m-2)) <= ys_m) && (isSortedFstN zs1 (n+m-1)))
        ? lma_merge xs ys n (m-1)
      -- === ((get zs1 (n+m-2)) <= ys_m)-- ys_m => get (merge xs ys n (m-1)) (n+m-2)
        ? (if m > 1
            then lma_merge_max xs ys n (m-1) (ys_m ? (lma_is_isfn ys m))  
            else lma_merge_max_n xs ys n ys_m)
      === True
      *** QED
    False -> isSortedFstN mer1 (n+m) 
      -- === (((get mer1 (n+m-2)) <= (get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1))) 
      -- === (((get mer3 (n+m-2)) <= (get mer3 (n+m-1))) && (isSortedFstN mer3 (n+m-1)))
      -- ==! True *** QED
        ? (lma_gs zs2 (n+m-1) xs_n) &&& (lma_gns zs2 (n+m-1) (n+m-2) xs_n)
      -- === (((get zs2 (n+m-2)) <= xs_n) && (isSortedFstN mer3 (n+m-1)))
        ? lma_isfn_set zs2 xs_n (n+m-1) (n+m-1)
      -- === (((get zs2 (n+m-2)) <= xs_n) && (isSortedFstN zs2 (n+m-1)))
        ? lma_merge xs ys (n-1) m
      -- === ((get zs2 (n+m-2)) <= xs_n) -- ys_m => get (merge xs ys n (m-1)) (n+m-2)
        ? (if n > 1
            then lma_merge_max xs ys (n-1) m (xs_n ? (lma_is_isfn xs n)) 
            else lma_merge_max_m xs ys m xs_n)
      === True
      *** QED
 

{-@ lma_msort :: xs:_ -> { pf:_ | isSortedFstN (msort xs) (size xs)} / [size xs] @-}
lma_msort ::  Ord a => Array a -> Proof
lma_msort xs  
  | (size xs == 0) = ()
  | (size xs == 1) = ()
  | otherwise      =
    let 
      ls' = (msort ls)
      rs' = (msort rs)
      (ls, rs) = splitMid xs
      sxs = merge ls' rs' (size ls') (size rs')
      n = (size xs)
    in
      isSortedFstN (msort xs) n
      -- === isSortedFstN (merge ls' rs' (size ls') (size rs')) n
        ? (lma_merge (ls' ? (lma_msort ls)) (rs' ? (lma_msort rs)) (size ls') (size rs'))
      === True
      *** QED
