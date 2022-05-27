\begin{code}

{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP, NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_HADDOCK hide #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.List
-- Copyright   :  (c) The University of Glasgow 1994-2002
-- License     :  see libraries/base/LICENSE
-- 
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC Extensions)
--
-- The List data type and its operations
--
-----------------------------------------------------------------------------

-- #hide
module GHC.List (
   -- [] (..),          -- Not Haskell 98; built in syntax

   map, (++), filter, concat,
   head, last, tail, init, null, length, (!!),
   foldl, scanl, scanl1, foldr, foldr1, scanr, scanr1,
   iterate, repeat, replicate, cycle,
   take, drop, splitAt, takeWhile, dropWhile, span, break,
   reverse, and, or,
   any, all, elem, notElem, lookup,
   concatMap,
   zip, zip3, zipWith, zipWith3, unzip, unzip3,
   errorEmptyList,

#ifndef USE_REPORT_PRELUDE
   -- non-standard, but hidden when creating the Prelude
   -- export list.
   takeUInt_append
#endif

 ) where

import Data.Maybe
import GHC.Base
import GHC.Num
import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)

infixl 9  !!
infix  4 `elem`, `notElem`




\end{code}

%*********************************************************
%*                                                      *
\subsection{List-manipulation functions}
%*                                                      *
%*********************************************************

\begin{code}
-- | Extract the first element of a list, which must be non-empty.
{-@ assert head         :: xs:{v: [a] | len(v) > 0} -> a @-}
head                    :: [a] -> a
head (x:_)              =  x
head []                 =  errorEmptyList "head"

badHead :: a
badHead = error "errorEmptyList head" -- errorEmptyList "head"

-- This rule is useful in cases like 
--      head [y | (x,y) <- ps, x==t]
{- RULES
"head/build"    forall (g::forall b.(a->b->b)->b->b) .
                head (build g) = g (\x _ -> x) badHead
"head/augment"  forall xs (g::forall b. (a->b->b) -> b -> b) . 
                head (augment g xs) = g (\x _ -> x) (head xs)
 -}

-- | Extract the elements after the head of a list, which must be non-empty.
{-@ assert tail         :: xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = (len(xs) - 1)}  @-}
tail                    :: [a] -> [a]
tail (_:xs)             =  xs
tail []                 =  liquidError "tail" -- errorEmptyList "tail"

-- | Extract the last element of a list, which must be finite and non-empty.
{-@ assert last         :: xs:{v: [a] | len(v) > 0} -> a @-}
last                    :: [a] -> a
#ifdef USE_REPORT_PRELUDE
last [x]                =  x
last (_:xs)             =  last xs
last []                 =  liquidError "last" -- errorEmptyList "last"
#else
-- eliminate repeated cases
last []                 =  liquidError "last" -- errorEmptyList "last"
last (x:xs)             =  last' x xs
  where last' y []     = y
        last' _ (y:ys) = last' y ys
#endif

-- | Return all the elements of a list except the last one.
-- The list must be non-empty.
{-@ assert init         :: xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) - 1}  @-}
init                    :: [a] -> [a]
#ifdef USE_REPORT_PRELUDE
init [x]                =  []
init (x:xs)             =  x : init xs
init []                 =  liquidError "init" -- errorEmptyList "init"
#else
-- eliminate repeated cases
init []                 =  liquidError "init" --errorEmptyList "init"
init (x:xs)             =  init' x xs
  where init' _ []     = []
        init' y (z:zs) = y : init' z zs
#endif

-- | Test whether a list is empty.
{-@ assert null :: xs:[a] -> {v: Bool | (Prop(v) <=> len(xs) = 0) }  @-}
null                    :: [a] -> Bool
null []                 =  True
null (_:_)              =  False

-- | /O(n)/. 'length' returns the length of a finite list as an 'Int'.
-- It is an instance of the more general 'Data.List.genericLength',
-- the result type of which may be any kind of number.
{-@ assert length :: xs:[a] -> {v: GHC.Types.Int | v = len(xs)}  @-}
length                  :: [a] -> Int
length l                =  len l 0#
  where
    --LIQUID FIXME: leaving the type signature causes this to compile to very strange core
    --LIQUID len :: [a] -> Int# -> Int
    len []     a# = I# a#
    len (_:xs) a# = len xs (a# +# 1#)

-- | 'filter', applied to a predicate and a list, returns the list of
-- those elements that satisfy the predicate; i.e.,
--
-- > filter p xs = [ x | x <- xs, p x]

{-@ assert filter :: (a -> GHC.Types.Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)} @-}
filter :: (a -> Bool) -> [a] -> [a]
filter _pred []    = []
filter pred (x:xs)
  | pred x         = x : filter pred xs
  | otherwise      = filter pred xs

{-# NOINLINE [0] filterFB #-}
filterFB :: (a -> b -> b) -> (a -> Bool) -> a -> b -> b
filterFB c p x r | p x       = x `c` r
                 | otherwise = r

{- RULES
"filter"     [~1] forall p xs.  filter p xs = build (\c n -> foldr (filterFB c p) n xs)
"filterList" [1]  forall p.     foldr (filterFB (:) p) [] = filter p
"filterFB"        forall c p q. filterFB (filterFB c p) q = filterFB c (\x -> q x && p x)
 -}

-- Note the filterFB rule, which has p and q the "wrong way round" in the RHS.
--     filterFB (filterFB c p) q a b
--   = if q a then filterFB c p a b else b
--   = if q a then (if p a then c a b else b) else b
--   = if q a && p a then c a b else b
--   = filterFB c (\x -> q x && p x) a b
-- I originally wrote (\x -> p x && q x), which is wrong, and actually
-- gave rise to a live bug report.  SLPJ.


-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a list, reduces the list
-- using the binary operator, from left to right:
--
-- > foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
--
-- The list must be finite.

-- We write foldl as a non-recursive thing, so that it
-- can be inlined, and then (often) strictness-analysed,
-- and hence the classic space leak on foldl (+) 0 xs

foldl        :: (a -> b -> a) -> a -> [b] -> a
foldl f z0 xs0 = lgo z0 xs0
             where
                lgo z []     = z
                lgo z (x:xs) = lgo (f z x) xs

-- | 'scanl' is similar to 'foldl', but returns a list of successive
-- reduced values from the left:
--
-- > scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
--
-- Note that
--
-- > last (scanl f z xs) == foldl f z xs.
{-@ assert scanl        :: (a -> b -> a) -> a -> xs:[b] -> {v: [a] | len(v) = 1 + len(xs) } @-}
scanl                   :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q ls            =  q : (case ls of
                                []   -> []
                                x:xs -> scanl f (f q x) xs)

-- | 'scanl1' is a variant of 'scanl' that has no starting value argument:
--
-- > scanl1 f [x1, x2, ...] == [x1, x1 `f` x2, ...]

{-@ assert scanl1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) } @-}
scanl1                  :: (a -> a -> a) -> [a] -> [a]
scanl1 f (x:xs)         =  scanl f x xs
scanl1 _ []             =  []

-- foldr, foldr1, scanr, and scanr1 are the right-to-left duals of the
-- above functions.

-- | 'foldr1' is a variant of 'foldr' that has no starting value argument,
-- and thus must be applied to non-empty lists.

{-@ assert foldr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> a @-}
foldr1                  :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]            =  x
foldr1 f (x:xs@(_:_))   =  f x (foldr1 f xs)
foldr1 _ []             =  liquidError "foldr1" -- errorEmptyList "foldr1"

-- | 'scanr' is the right-to-left dual of 'scanl'.
-- Note that
--
-- > head (scanr f z xs) == foldr f z xs.

{-@ assert scanr        :: (a -> b -> b) -> b -> xs:[a] -> {v: [b] | len(v) = 1 + len(xs) } @-}
scanr                   :: (a -> b -> b) -> b -> [a] -> [b]
scanr _ q0 []           =  [q0]
scanr f q0 (x:xs)       =  f x q : qs
                           where qs@(q:_) = scanr f q0 xs 

-- | 'scanr1' is a variant of 'scanr' that has no starting value argument.

{-@ assert scanr1       :: (a -> a -> a) -> xs:{v: [a] | len(v) > 0} -> {v: [a] | len(v) = len(xs) } @-}
scanr1                  :: (a -> a -> a) -> [a] -> [a]
scanr1 _ []             =  []
scanr1 _ [x]            =  [x]
scanr1 f (x:xs@(_:_))   =  f x q : qs
                           where qs@(q:_) = scanr1 f xs 

-- | 'iterate' @f x@ returns an infinite list of repeated applications
-- of @f@ to @x@:
--
-- > iterate f x == [x, f x, f (f x), ...]

{-@ lazy GHC.List.iterate @-}
{-@ iterate :: (a -> a) -> a -> [a] @-}
iterate :: (a -> a) -> a -> [a]
iterate f x =  x : iterate f (f x)

{-@ lazy GHC.List.iterateFB @-}
{-@ iterateFB :: (a -> b -> b) -> (a -> a) -> a -> b @-}
iterateFB :: (a -> b -> b) -> (a -> a) -> a -> b
iterateFB c f x = x `c` iterateFB c f (f x)


{- RULES
"iterate"    [~1] forall f x.   iterate f x = build (\c _n -> iterateFB c f x)
"iterateFB"  [1]                iterateFB (:) = iterate
 -}


-- | 'repeat' @x@ is an infinite list, with @x@ the value of every element.
{- measure inf :: Int @-}
{- invariant {v:Int | v < inf} @-}
{- repeat :: a -> {v:[a] | (len v) = inf} @-}
{-@ repeat :: a -> [a] @-}
{-@ lazy GHC.List.repeat @-}
repeat :: a -> [a]
{-# INLINE [0] repeat #-}
-- The pragma just gives the rules more chance to fire
repeat x = xs where xs = x : xs

{-# INLINE [0] repeatFB #-}     -- ditto
{-@ lazy GHC.List.repeatFB @-}
{-@ repeatFB :: (a -> b -> b) -> a -> b @-}
repeatFB :: (a -> b -> b) -> a -> b
repeatFB c x = xs where xs = x `c` xs


{- RULES
"repeat"    [~1] forall x. repeat x = build (\c _n -> repeatFB c x)
"repeatFB"  [1]  repeatFB (:)       = repeat
 -}

-- | 'replicate' @n x@ is a list of length @n@ with @x@ the value of
-- every element.
-- It is an instance of the more general 'Data.List.genericReplicate',
-- in which @n@ may be of any integral type.
{-# INLINE replicate #-}
{-@ assert replicate    :: n:Nat -> x:a -> {v: [{v:a | v = x}] | len(v) = n} @-}
replicate               :: Int -> a -> [a]
--LIQUID replicate n x           =  take n (repeat x)
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

-- | 'cycle' ties a finite list into a circular one, or equivalently,
-- the infinite repetition of the original list.  It is the identity
-- on infinite lists.

{-@ assert cycle        :: {v: [a] | len(v) > 0 } -> [a] @-}
{-@ lazy cycle @-}
cycle                   :: [a] -> [a]
cycle []                = liquidError {- error -} "Prelude.cycle: empty list"
cycle xs                = xs' where xs' = xs ++ xs'

-- | 'takeWhile', applied to a predicate @p@ and a list @xs@, returns the
-- longest prefix (possibly empty) of @xs@ of elements that satisfy @p@:
--
-- > takeWhile (< 3) [1,2,3,4,1,2,3,4] == [1,2]
-- > takeWhile (< 9) [1,2,3] == [1,2,3]
-- > takeWhile (< 0) [1,2,3] == []
--

{-@ assert takeWhile    :: (a -> Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)} @-}
takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile _ []          =  []
takeWhile p (x:xs) 
            | p x       =  x : takeWhile p xs
            | otherwise =  []

-- | 'dropWhile' @p xs@ returns the suffix remaining after 'takeWhile' @p xs@:
--
-- > dropWhile (< 3) [1,2,3,4,5,1,2,3] == [3,4,5,1,2,3]
-- > dropWhile (< 9) [1,2,3] == []
-- > dropWhile (< 0) [1,2,3] == [1,2,3]
--

{-@ assert dropWhile    :: (a -> Bool) -> xs:[a] -> {v: [a] | len(v) <= len(xs)} @-}
dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile _ []          =  []
dropWhile p xs@(x:xs')
            | p x       =  dropWhile p xs'
            | otherwise =  xs

-- | 'take' @n@, applied to a list @xs@, returns the prefix of @xs@
-- of length @n@, or @xs@ itself if @n > 'length' xs@:
--
-- > take 5 "Hello World!" == "Hello"
-- > take 3 [1,2,3,4,5] == [1,2,3]
-- > take 3 [1,2] == [1,2]
-- > take 3 [] == []
-- > take (-1) [1,2] == []
-- > take 0 [1,2] == []
--
-- It is an instance of the more general 'Data.List.genericTake',
-- in which @n@ may be of any integral type.


{-@ take :: n:Int
         -> xs:[a] 
         -> {v:[a] | (if (n >=0) then ((len v) = ((len(xs) < n) ? len(xs):n)) else ((len v) = 0))} 
  @-}
take                   :: Int -> [a] -> [a]

-- | 'drop' @n xs@ returns the suffix of @xs@
-- after the first @n@ elements, or @[]@ if @n > 'length' xs@:
--
-- > drop 6 "Hello World!" == "World!"
-- > drop 3 [1,2,3,4,5] == [4,5]
-- > drop 3 [1,2] == []
-- > drop 3 [] == []
-- > drop (-1) [1,2] == [1,2]
-- > drop 0 [1,2] == [1,2]
--
-- It is an instance of the more general 'Data.List.genericDrop',
-- in which @n@ may be of any integral type.
{-@ drop  :: n: Int 
          -> xs:[a] 
          -> {v:[a] | (if (n >= 0) then (len(v) = ((len(xs) <  n) ? 0 : len(xs) - n)) else ((len v) = (len xs)))} @-}
drop                   :: Int -> [a] -> [a]

-- | 'splitAt' @n xs@ returns a tuple where first element is @xs@ prefix of
-- length @n@ and second element is the remainder of the list:
--
-- > splitAt 6 "Hello World!" == ("Hello ","World!")
-- > splitAt 3 [1,2,3,4,5] == ([1,2,3],[4,5])
-- > splitAt 1 [1,2,3] == ([1],[2,3])
-- > splitAt 3 [1,2,3] == ([1,2,3],[])
-- > splitAt 4 [1,2,3] == ([1,2,3],[])
-- > splitAt 0 [1,2,3] == ([],[1,2,3])
-- > splitAt (-1) [1,2,3] == ([],[1,2,3])
--
-- It is equivalent to @('take' n xs, 'drop' n xs)@ when @n@ is not @_|_@
-- (@splitAt _|_ xs = _|_@).
-- 'splitAt' is an instance of the more general 'Data.List.genericSplitAt',
-- in which @n@ may be of any integral type.
-- Liquid: TODO
{-@ splitAt :: n:Int -> x:[a] -> ({v:[a] | (if (n >= 0) then (Min (len v) (len x) n) else ((len v) = 0))},[a])<{\x1 x2 -> (len x2) = (len x) - (len x1)}> @-}
splitAt                :: Int -> [a] -> ([a],[a])

#ifdef USE_REPORT_PRELUDE
take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (n-1) xs

drop n xs     | n <= 0 =  xs
drop _ []              =  []
drop n (_:xs)          =  drop (n-1) xs

splitAt n xs           =  (take n xs, drop n xs)

#else /* hack away */
{- RULES
"take"     [~1] forall n xs . take n xs = takeFoldr n xs 
"takeList"  [1] forall n xs . foldr (takeFB (:) []) (takeConst []) xs n = takeUInt n xs
 -}

{-# INLINE takeFoldr #-}
takeFoldr :: Int -> [a] -> [a]
takeFoldr (I# n#) xs
  = build (\c nil -> if n# <=# 0# then nil else
                     foldr (takeFB c nil) (takeConst nil) xs n#)

{-# NOINLINE [0] takeConst #-}
-- just a version of const that doesn't get inlined too early, so we
-- can spot it in rules.  Also we need a type sig due to the unboxed Int#.
takeConst :: a -> Int# -> a
takeConst x _ = x

{-# NOINLINE [0] takeFB #-}
takeFB :: (a -> b -> b) -> b -> a -> (Int# -> b) -> Int# -> b
takeFB c n x xs m | m <=# 1#  = x `c` n
                  | otherwise = x `c` xs (m -# 1#)

{-- INLINE [0] take #-}
take (I# n#) xs = takeUInt n# xs

-- The general code for take, below, checks n <= maxInt
-- No need to check for maxInt overflow when specialised
-- at type Int or Int# since the Int must be <= maxInt

takeUInt :: Int# -> [b] -> [b]
takeUInt n xs
  | n >=# 0#  =  take_unsafe_UInt n xs
  | otherwise =  []

take_unsafe_UInt :: Int# -> [b] -> [b]
take_unsafe_UInt 0#  _  = []
take_unsafe_UInt m   ls =
  case ls of
    []     -> []
    (x:xs) -> x : take_unsafe_UInt (m -# 1#) xs

takeUInt_append :: Int# -> [b] -> [b] -> [b]
takeUInt_append n xs rs
  | n >=# 0#  =  take_unsafe_UInt_append n xs rs
  | otherwise =  []

take_unsafe_UInt_append :: Int# -> [b] -> [b] -> [b]
take_unsafe_UInt_append 0#  _ rs  = rs
take_unsafe_UInt_append m  ls rs  =
  case ls of
    []     -> rs
    (x:xs) -> x : take_unsafe_UInt_append (m -# 1#) xs rs

drop (I# n#) ls
  | n# <# 0#    = ls
  | otherwise   = drop# n# ls
    where
        drop# :: Int# -> [a] -> [a]
        drop# 0# xs      = xs
        drop# _  xs@[]   = xs
        drop# m# (_:xs)  = drop# (m# -# 1#) xs

splitAt (I# n#) ls
  | n# <# 0#    = ([], ls)
  | otherwise   = splitAt# n# ls
    where
        splitAt# :: Int# -> [a] -> ([a], [a])
        splitAt# 0# xs     = ([], xs)
        splitAt# _  xs@[]  = (xs, xs)
        splitAt# m# (x:xs) = (x:xs', xs'')
          where
            (xs', xs'') = splitAt# (m# -# 1#) xs

#endif /* USE_REPORT_PRELUDE */

-- | 'span', applied to a predicate @p@ and a list @xs@, returns a tuple where
-- first element is longest prefix (possibly empty) of @xs@ of elements that
-- satisfy @p@ and second element is the remainder of the list:
-- 
-- > span (< 3) [1,2,3,4,1,2,3,4] == ([1,2],[3,4,1,2,3,4])
-- > span (< 9) [1,2,3] == ([1,2,3],[])
-- > span (< 0) [1,2,3] == ([],[1,2,3])
-- 
-- 'span' @p xs@ is equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
-- Liquid: TODO
{-@
span    :: (a -> Bool) 
        -> xs:[a] 
        -> ({v:[a]|((len v)<=(len xs))}, {v:[a]|((len v)<=(len xs))})
@-}
span                    :: (a -> Bool) -> [a] -> ([a], [a])
span _ xs@[]            =  (xs, xs)
span p xs@(x:xs')
         | p x          =  let (ys,zs) = span p xs' in (x:ys,zs)
         | otherwise    =  ([],xs)

-- | 'break', applied to a predicate @p@ and a list @xs@, returns a tuple where
-- first element is longest prefix (possibly empty) of @xs@ of elements that
-- /do not satisfy/ @p@ and second element is the remainder of the list:
-- 
-- > break (> 3) [1,2,3,4,1,2,3,4] == ([1,2,3],[4,1,2,3,4])
-- > break (< 9) [1,2,3] == ([],[1,2,3])
-- > break (> 9) [1,2,3] == ([1,2,3],[])
--
-- 'break' @p@ is equivalent to @'span' ('not' . p)@.
-- liquid:TODO
{-@ break :: (a -> Bool) -> xs:[a] -> ([a],[a])<{\x y -> (len xs) = (len x) + (len y)}> @-}
break                   :: (a -> Bool) -> [a] -> ([a],[a])
#ifdef USE_REPORT_PRELUDE
break p                 =  span (not . p)
#else
-- HBC version (stolen)
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([],xs)
           | otherwise  =  let (ys,zs) = break p xs' in (x:ys,zs)
#endif

-- | 'reverse' @xs@ returns the elements of @xs@ in reverse order.
-- @xs@ must be finite.
{-@ assert reverse      :: xs:[a] -> {v: [a] | len(v) = len(xs)} @-}
{-@ include <len.hquals> @-}
reverse                 :: [a] -> [a]
#ifdef USE_REPORT_PRELUDE
reverse                 =  foldl (flip (:)) []
#else
reverse l =  rev l []
  where
    rev []     a = a
    rev (x:xs) a = rev xs (x:a)
#endif

-- | 'and' returns the conjunction of a Boolean list.  For the result to be
-- 'True', the list must be finite; 'False', however, results from a 'False'
-- value at a finite index of a finite or infinite list.
and                     :: [Bool] -> Bool

-- | 'or' returns the disjunction of a Boolean list.  For the result to be
-- 'False', the list must be finite; 'True', however, results from a 'True'
-- value at a finite index of a finite or infinite list.
or                      :: [Bool] -> Bool
#ifdef USE_REPORT_PRELUDE
and                     =  foldr (&&) True
or                      =  foldr (||) False
#else
and []          =  True
and (x:xs)      =  x && and xs
or []           =  False
or (x:xs)       =  x || or xs

{- RULES
"and/build"     forall (g::forall b.(Bool->b->b)->b->b) . 
                and (build g) = g (&&) True
"or/build"      forall (g::forall b.(Bool->b->b)->b->b) . 
                or (build g) = g (||) False
 -}
#endif

-- | Applied to a predicate and a list, 'any' determines if any element
-- of the list satisfies the predicate.  For the result to be
-- 'False', the list must be finite; 'True', however, results from a 'True'
-- value for the predicate applied to an element at a finite index of a finite or infinite list.
any                     :: (a -> Bool) -> [a] -> Bool

-- | Applied to a predicate and a list, 'all' determines if all elements
-- of the list satisfy the predicate. For the result to be
-- 'True', the list must be finite; 'False', however, results from a 'False'
-- value for the predicate applied to an element at a finite index of a finite or infinite list.
all                     :: (a -> Bool) -> [a] -> Bool
#ifdef USE_REPORT_PRELUDE
any p                   =  or . map p
all p                   =  and . map p
#else
any _ []        = False
any p (x:xs)    = p x || any p xs

all _ []        =  True
all p (x:xs)    =  p x && all p xs
{- RULES
"any/build"     forall p (g::forall b.(a->b->b)->b->b) . 
                any p (build g) = g ((||) . p) False
"all/build"     forall p (g::forall b.(a->b->b)->b->b) . 
                all p (build g) = g ((&&) . p) True
 -}
#endif

-- | 'elem' is the list membership predicate, usually written in infix form,
-- e.g., @x \`elem\` xs@.  For the result to be
-- 'False', the list must be finite; 'True', however, results from an element equal to @x@ found at a finite index of a finite or infinite list.
elem                    :: (Eq a) => a -> [a] -> Bool

-- | 'notElem' is the negation of 'elem'.
notElem                 :: (Eq a) => a -> [a] -> Bool
#ifdef USE_REPORT_PRELUDE
elem x                  =  any (== x)
notElem x               =  all (/= x)
#else
elem _ []       = False
elem x (y:ys)   = x==y || elem x ys

notElem _ []    =  True
notElem x (y:ys)=  x /= y && notElem x ys
#endif

-- | 'lookup' @key assocs@ looks up a key in an association list.
lookup                  :: (Eq a) => a -> [(a,b)] -> Maybe b
lookup _key []          =  Nothing
lookup  key ((x,y):xys)
    | key == x          =  Just y
    | otherwise         =  lookup key xys

-- | Map a function over a list and concatenate the results.
concatMap               :: (a -> [b]) -> [a] -> [b]
concatMap f             =  foldr ((++) . f) []

-- | Concatenate a list of lists.
concat :: [[a]] -> [a]
concat = foldr (++) []

{- RULES
  "concat" forall xs. concat xs = build (\c n -> foldr (\x y -> foldr c y x) n xs)
-- We don't bother to turn non-fusible applications of concat back into concat
 -}

\end{code}


\begin{code}
-- | List index (subscript) operator, starting from 0.
-- It is an instance of the more general 'Data.List.genericIndex',
-- which takes an index of any integral type.

{-@ assert GHC.List.!!         :: xs:[a] -> {v: Int | ((0 <= v) && (v < len(xs)))} -> a @-}
(!!)                    :: [a] -> Int -> a
#ifdef USE_REPORT_PRELUDE
xs     !! n | n < 0 =  liquidError {- error -} "Prelude.!!: negative index"
[]     !! _         =  liquidError {- error -} "Prelude.!!: index too large"
(x:_)  !! 0         =  x
(_:xs) !! n         =  xs !! (n-1)
#else
-- HBC version (stolen), then unboxified
-- The semantics is not quite the same for error conditions
-- in the more efficient version.
--
xs !! (I# n0) | n0 <# 0#   =  liquidError {- error -} "Prelude.(!!): negative index\n"
               | otherwise =  sub xs n0
                         where
                            sub :: [a] -> Int# -> a
                            sub []     _ = liquidError {- error -} "Prelude.(!!): index too large\n"
                            sub (y:ys) n = if n ==# 0#
                                           then y
                                           else sub ys (n -# 1#)
#endif
\end{code}


%*********************************************************
%*                                                      *
\subsection{The zip family}
%*                                                      *
%*********************************************************

\begin{code}
foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 _k z []    _ys    = z
foldr2 _k z _xs   []     = z
foldr2 k z (x:xs) (y:ys) = k x y (foldr2 k z xs ys)

foldr2_left :: (a -> b -> c -> d) -> d -> a -> ([b] -> c) -> [b] -> d
foldr2_left _k  z _x _r []     = z
foldr2_left  k _z  x  r (y:ys) = k x y (r ys)

foldr2_right :: (a -> b -> c -> d) -> d -> b -> ([a] -> c) -> [a] -> d
foldr2_right _k z  _y _r []     = z
foldr2_right  k _z  y  r (x:xs) = k x y (r xs)

-- foldr2 k z xs ys = foldr (foldr2_left k z)  (\_ -> z) xs ys
-- foldr2 k z xs ys = foldr (foldr2_right k z) (\_ -> z) ys xs
{- RULES
"foldr2/left"   forall k z ys (g::forall b.(a->b->b)->b->b) . 
                  foldr2 k z (build g) ys = g (foldr2_left  k z) (\_ -> z) ys

"foldr2/right"  forall k z xs (g::forall b.(a->b->b)->b->b) . 
                  foldr2 k z xs (build g) = g (foldr2_right k z) (\_ -> z) xs
 -}
\end{code}

The foldr2/right rule isn't exactly right, because it changes
the strictness of foldr2 (and thereby zip)

E.g. main = print (null (zip nonobviousNil (build undefined)))
          where   nonobviousNil = f 3
                  f n = if n == 0 then [] else f (n-1)

I'm going to leave it though.


Zips for larger tuples are in the List module.

\begin{code}
----------------------------------------------
-- | 'zip' takes two lists and returns a list of corresponding pairs.
-- If one input list is short, excess elements of the longer list are
-- discarded.

{-@ zip :: xs : [a] -> ys:[b] 
            -> {v : [(a, b)] | ((((len v) <= (len xs)) && ((len v) <= (len ys)))
            && (((len xs) = (len ys)) => ((len v) = (len xs))) )} @-}

zip :: [a] -> [b] -> [(a,b)]
zip (a:as) (b:bs) = (a,b) : zip as bs
zip _      _      = []

{-# INLINE [0] zipFB #-}
zipFB :: ((a, b) -> c -> d) -> a -> b -> c -> d
zipFB c = \x y r -> (x,y) `c` r

{- RULES
"zip"      [~1] forall xs ys. zip xs ys = build (\c n -> foldr2 (zipFB c) n xs ys)
"zipList"  [1]  foldr2 (zipFB (:)) []   = zip
 -}
\end{code}

\begin{code}
----------------------------------------------
-- | 'zip3' takes three lists and returns a list of triples, analogous to
-- 'zip'.
zip3 :: [a] -> [b] -> [c] -> [(a,b,c)]
-- Specification
-- zip3 =  zipWith3 (,,)
zip3 (a:as) (b:bs) (c:cs) = (a,b,c) : zip3 as bs cs
zip3 _      _      _      = []
\end{code}


-- The zipWith family generalises the zip family by zipping with the
-- function given as the first argument, instead of a tupling function.

\begin{code}
----------------------------------------------
-- | 'zipWith' generalises 'zip' by zipping with the function given
-- as the first argument, instead of a tupling function.
-- For example, @'zipWith' (+)@ is applied to two lists to produce the
-- list of corresponding sums.


{-@ zipWith :: (a -> b -> c) 
            -> xs : [a] -> ys:[b] 
            -> {v : [c] | (((len v) <= (len xs)) && ((len v) <= (len ys)))} @-}
zipWith :: (a->b->c) -> [a]->[b]->[c]
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ _      _      = []

-- zipWithFB must have arity 2 since it gets two arguments in the "zipWith"
-- rule; it might not get inlined otherwise
{-# INLINE [0] zipWithFB #-}
zipWithFB :: (a -> b -> c) -> (d -> e -> a) -> d -> e -> b -> c
zipWithFB c f = \x y r -> (x `f` y) `c` r

{- RULES
"zipWith"       [~1] forall f xs ys.    zipWith f xs ys = build (\c n -> foldr2 (zipWithFB c f) n xs ys)
"zipWithList"   [1]  forall f.  foldr2 (zipWithFB (:) f) [] = zipWith f
  -}
\end{code}

\begin{code}
-- | The 'zipWith3' function takes a function which combines three
-- elements, as well as three lists and returns a list of their point-wise
-- combination, analogous to 'zipWith'.
zipWith3                :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z (a:as) (b:bs) (c:cs)
                        =  z a b c : zipWith3 z as bs cs
zipWith3 _ _ _ _        =  []

-- | 'unzip' transforms a list of pairs into a list of first components
-- and a list of second components.
unzip    :: [(a,b)] -> ([a],[b])
{-# INLINE unzip #-}
unzip    =  foldr (\(a,b) ~(as,bs) -> (a:as,b:bs)) ([],[])

-- | The 'unzip3' function takes a list of triples and returns three
-- lists, analogous to 'unzip'.
unzip3   :: [(a,b,c)] -> ([a],[b],[c])
{-# INLINE unzip3 #-}
unzip3   =  foldr (\(a,b,c) ~(as,bs,cs) -> (a:as,b:bs,c:cs))
                  ([],[],[])
\end{code}


%*********************************************************
%*                                                      *
\subsection{Error code}
%*                                                      *
%*********************************************************

Common up near identical calls to `error' to reduce the number
constant strings created when compiled:

\begin{code}
{-@ assert errorEmptyList :: {v: String | (0 = 1)} -> a @-}
errorEmptyList :: String -> a
errorEmptyList fun =
  liquidError {- error -} (prel_list_str ++ fun ++ ": empty list")

prel_list_str :: String
prel_list_str = "Prelude."
\end{code}
