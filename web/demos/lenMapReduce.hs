module ListLengths where

import qualified Data.Hashable as H 
import Prelude hiding (length, map, filter, head, tail, foldl1)
import Language.Haskell.Liquid.Prelude (liquidError)
import qualified Data.HashMap.Strict as M

-- liquidError = error

-- | The length of a List

-- measure len :: forall a. [a] -> GHC.Types.Int
-- len ([])     = 0
-- len (y:ys)   = 1 + (len ys)

------------------------------------------------------------------------------

-- | Constructing Lists

{-@ xs :: {v:[String] | (len v) = 1 } @-}
xs = "dog" : []

{-@ ys :: {v:[String] | (len v) = 2 } @-}
ys = ["cat", "dog"]

{-@ zs :: {v:[String] | (len v) = 3 } @-}
zs = "hippo" : ys

-- Hover your mouse over the `:` and `[]` above to confirm their types!

-- | Deconstructing Lists

{-@ zs' :: {v:[String] | (len v) = 2 } @-}
zs' = case zs of
        h : t -> t


-- | Reasoning about Lengths

{-@ length :: xs:[a] -> {v: Int | v = (len xs)} @-}
length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs


-- | Some old friends ...

{-@ map      :: (a -> b) -> xs:[a] -> {v:[b] | (len v) = (len xs)} @-}
map _ []     = []
map f (x:xs) = (f x) : (map f xs)

{-@ filter :: (a -> Bool) -> xs:[a] -> {v:[a] | (len v) <= (len xs)} @-}
filter _ []     = []
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   = filter f xs

{-@ append :: xs:[a] -> ys:[a] -> {v:[a] | (len v) = (len xs) + (len ys)} @-}
append [] ys     = ys
append (x:xs) ys = x : append xs ys

------------------------------------------------------------------------------

{-@ predicate NonNull X = ((len X) > 0) @-}

-- | Safe head

{-@ head   :: {v:[a] | (NonNull v)} -> a @-}
head (x:_) = x
head []    = liquidError "Fear not! 'twill ne'er come to pass"

-- | Safe tail

{-@ tail :: {v:[a] | (NonNull v)} -> [a] @-}
tail (_:xs) = xs
tail []     = liquidError "Relaxeth! this too shall ne'er be"

-- | Using head, safely

{-@ eliminateStutter :: (Eq a) => [a] -> [a] @-}
eliminateStutter xs = map head $ groupEq xs

-- (Put your mouse over the `map` identifier to see inferred type.)


-- `groupEq` gathers consecutive equal elements in the list into a single non-empty list.

groupEq []     = []
groupEq (x:xs) = (x:ys) : groupEq zs
                 where (ys,zs) = span (x ==) xs

-- (Put your mouse over the `groupEq` identifier to see inferred type.)

------------------------------------------------------------------------------
-- Neil Mitchell's "risers"

{-@ risers :: (Ord a) => zs:[a] -> {v: [[a]] | ((NonNull zs) => (NonNull v)) } @-} 

risers []        = []
risers [x]       = [[x]]
risers (x:y:etc) = if x <= y then (x:s):ss else [x]:(s:ss)
    where 
      (s, ss)    = safeSplit $ risers (y:etc)

safeSplit (x:xs) = (x, xs)
safeSplit _      = liquidError "don't worry, be happy"

------------------------------------------------------------------------------

-- | A Simple map-reduce library

mapReduce       :: (Eq k, H.Hashable k) 
                => (a -> [(k, v)]) -- ^ key-mapper
                -> (v -> v -> v)   -- ^ reduction operator
                -> [a]             -- ^ inputs
                -> [(k, v)]        -- ^ output key-values

mapReduce f op  = M.toList
                . reduce op
                . group
                . keyMap f

-- | `keyMap` expands a list of inputs into a list of key-value pairs:

keyMap :: (a -> [(k, v)]) -> [a] -> [(k, v)]
keyMap f xs = concatMap f xs

-- | `group` gathers the key-value pairs into a `Map` from keys to the 
-- lists of values with that same key.

group     :: (Eq k, H.Hashable k) 
          => [(k, a)] -> M.HashMap k [a]

group kvs = foldr (\(k, v) m -> inserts k v m) M.empty kvs


-- | `inserts` adds the new value `v` to the list of previously known 
--  values `lookupDefault [] k m` for the key `k`.

inserts   :: (Eq k, H.Hashable k) 
          => k -> a -> M.HashMap k [a] -> M.HashMap k [a]

inserts k v m = M.insert k (v : vs) m
  where vs    = M.lookupDefault [] k m


-- | `reduces` crunches a list of values for a given key in the 
-- table to a single value

reduce    :: (v -> v -> v) -> M.HashMap k [v] -> M.HashMap k v
reduce op = M.map (foldl1 op)


{-@ foldl1      :: (a -> a -> a) -> {v:[a] | (NonNull v)} -> a @-}
foldl1 f (x:xs) =  foldl f x xs
foldl1 _ []     =  liquidError "will. never. happen."


-- Now, if we want to compute the frequency of `Char` in a given list of words, we can write:


{-@ charFrequency :: [String] -> [(Char, Int)] @-}
charFrequency     :: [String] -> [(Char, Int)]
charFrequency     = mapReduce wordChars (+)
  where wordChars = map (\c -> (c, 1))


-- You can take it out for a spin like so:


f0 = charFrequency [ "the", "quick" , "brown"
                   , "fox", "jumped", "over"
                   , "the", "lazy"  , "cow"   ]

