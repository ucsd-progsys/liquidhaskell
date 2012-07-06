{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
#endif
#if __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Sequence
-- Copyright   :  (c) Ross Paterson 2005
--                (c) Louis Wasserman 2009
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- General purpose finite sequences.
-- Apart from being finite and having strict operations, sequences
-- also differ from lists in supporting a wider variety of operations
-- efficiently.
--
-- An amortized running time is given for each operation, with /n/ referring
-- to the length of the sequence and /i/ being the integral index used by
-- some operations.  These bounds hold even in a persistent (shared) setting.
--
-- The implementation uses 2-3 finger trees annotated with sizes,
-- as described in section 4.2 of
--
--    * Ralf Hinze and Ross Paterson,
--      \"Finger trees: a simple general-purpose data structure\",
--      /Journal of Functional Programming/ 16:2 (2006) pp 197-217.
--      <http://www.soi.city.ac.uk/~ross/papers/FingerTree.html>
--
-- /Note/: Many of these operations have the same names as similar
-- operations on lists in the "Prelude".  The ambiguity may be resolved
-- using either qualification or the @hiding@ clause.
--
-----------------------------------------------------------------------------

module Data.Sequence (
#if !defined(TESTING)
    Seq,
#else
    Seq(..), Elem(..), FingerTree(..), Node(..), Digit(..),
#endif
    -- * Construction
    empty,          -- :: Seq a
    singleton,      -- :: a -> Seq a
    (<|),           -- :: a -> Seq a -> Seq a
    (|>),           -- :: Seq a -> a -> Seq a
    (><),           -- :: Seq a -> Seq a -> Seq a
    fromList,       -- :: [a] -> Seq a
    -- ** Repetition
    replicate,      -- :: Int -> a -> Seq a
    replicateA,     -- :: Applicative f => Int -> f a -> f (Seq a)
    replicateM,     -- :: Monad m => Int -> m a -> m (Seq a)
    -- ** Iterative construction
    iterateN,       -- :: Int -> (a -> a) -> a -> Seq a
    unfoldr,        -- :: (b -> Maybe (a, b)) -> b -> Seq a
    unfoldl,        -- :: (b -> Maybe (b, a)) -> b -> Seq a
    -- * Deconstruction
    -- | Additional functions for deconstructing sequences are available
    -- via the 'Foldable' instance of 'Seq'.

    -- ** Queries
    null,           -- :: Seq a -> Bool
    length,         -- :: Seq a -> Int
    -- ** Views
    ViewL(..),
    viewl,          -- :: Seq a -> ViewL a
    ViewR(..),
    viewr,          -- :: Seq a -> ViewR a
    -- * Scans
    scanl,          -- :: (a -> b -> a) -> a -> Seq b -> Seq a
    scanl1,         -- :: (a -> a -> a) -> Seq a -> Seq a
    scanr,          -- :: (a -> b -> b) -> b -> Seq a -> Seq b
    scanr1,         -- :: (a -> a -> a) -> Seq a -> Seq a
    -- * Sublists
    tails,          -- :: Seq a -> Seq (Seq a)
    inits,          -- :: Seq a -> Seq (Seq a)
    -- ** Sequential searches
    takeWhileL,     -- :: (a -> Bool) -> Seq a -> Seq a
    takeWhileR,     -- :: (a -> Bool) -> Seq a -> Seq a
    dropWhileL,     -- :: (a -> Bool) -> Seq a -> Seq a
    dropWhileR,     -- :: (a -> Bool) -> Seq a -> Seq a
    spanl,          -- :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
    spanr,          -- :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
    breakl,         -- :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
    breakr,         -- :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
    partition,      -- :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
    filter,         -- :: (a -> Bool) -> Seq a -> Seq a
    -- * Sorting
    sort,           -- :: Ord a => Seq a -> Seq a
    sortBy,         -- :: (a -> a -> Ordering) -> Seq a -> Seq a
    unstableSort,   -- :: Ord a => Seq a -> Seq a
    unstableSortBy, -- :: (a -> a -> Ordering) -> Seq a -> Seq a
    -- * Indexing
    index,          -- :: Seq a -> Int -> a
    adjust,         -- :: (a -> a) -> Int -> Seq a -> Seq a
    update,         -- :: Int -> a -> Seq a -> Seq a
    take,           -- :: Int -> Seq a -> Seq a
    drop,           -- :: Int -> Seq a -> Seq a
    splitAt,        -- :: Int -> Seq a -> (Seq a, Seq a)
    -- ** Indexing with predicates
    -- | These functions perform sequential searches from the left
    -- or right ends of the sequence, returning indices of matching
    -- elements.
    elemIndexL,     -- :: Eq a => a -> Seq a -> Maybe Int
    elemIndicesL,   -- :: Eq a => a -> Seq a -> [Int]
    elemIndexR,     -- :: Eq a => a -> Seq a -> Maybe Int
    elemIndicesR,   -- :: Eq a => a -> Seq a -> [Int]
    findIndexL,     -- :: (a -> Bool) -> Seq a -> Maybe Int
    findIndicesL,   -- :: (a -> Bool) -> Seq a -> [Int]
    findIndexR,     -- :: (a -> Bool) -> Seq a -> Maybe Int
    findIndicesR,   -- :: (a -> Bool) -> Seq a -> [Int]
    -- * Folds
    -- | General folds are available via the 'Foldable' instance of 'Seq'.
    foldlWithIndex, -- :: (b -> Int -> a -> b) -> b -> Seq a -> b
    foldrWithIndex, -- :: (Int -> a -> b -> b) -> b -> Seq a -> b
    -- * Transformations
    mapWithIndex,   -- :: (Int -> a -> b) -> Seq a -> Seq b
    reverse,        -- :: Seq a -> Seq a
    -- ** Zips
    zip,            -- :: Seq a -> Seq b -> Seq (a, b)
    zipWith,        -- :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
    zip3,           -- :: Seq a -> Seq b -> Seq c -> Seq (a, b, c)
    zipWith3,       -- :: (a -> b -> c -> d) -> Seq a -> Seq b -> Seq c -> Seq d
    zip4,           -- :: Seq a -> Seq b -> Seq c -> Seq d -> Seq (a, b, c, d)
    zipWith4,       -- :: (a -> b -> c -> d -> e) -> Seq a -> Seq b -> Seq c -> Seq d -> Seq e
#if TESTING
    Sized(..),
    deep,
    node2,
    node3,
#endif
    ) where

import Prelude hiding (
    Functor(..),
    null, length, take, drop, splitAt, foldl, foldl1, foldr, foldr1,
    scanl, scanl1, scanr, scanr1, replicate, zip, zipWith, zip3, zipWith3,
    takeWhile, dropWhile, iterate, reverse, filter, mapM, sum, all)
import qualified Data.List
import Control.Applicative (Applicative(..), (<$>), WrappedMonad(..), liftA, liftA2, liftA3)
import Control.DeepSeq (NFData(rnf))
import Control.Monad (MonadPlus(..), ap)
import Data.Monoid (Monoid(..))
import Data.Functor (Functor(..))
import Data.Foldable
import Data.Traversable
import Data.Typeable

#ifdef __GLASGOW_HASKELL__
import GHC.Exts (build)
import Text.Read (Lexeme(Ident), lexP, parens, prec,
    readPrec, readListPrec, readListPrecDefault)
import Data.Data
#endif

infixr 5 `consTree`
infixl 5 `snocTree`

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

class Sized a where
    size :: a -> Int

-- | General-purpose finite sequences.
newtype Seq a = Seq (FingerTree (Elem a))

instance Functor Seq where
    fmap f (Seq xs) = Seq (fmap (fmap f) xs)
#ifdef __GLASGOW_HASKELL__
    x <$ s = replicate (length s) x
#endif

instance Foldable Seq where
    foldr f z (Seq xs) = foldr (flip (foldr f)) z xs
    foldl f z (Seq xs) = foldl (foldl f) z xs

    foldr1 f (Seq xs) = getElem (foldr1 f' xs)
      where f' (Elem x) (Elem y) = Elem (f x y)

    foldl1 f (Seq xs) = getElem (foldl1 f' xs)
      where f' (Elem x) (Elem y) = Elem (f x y)

instance Traversable Seq where
    traverse f (Seq xs) = Seq <$> traverse (traverse f) xs

instance NFData a => NFData (Seq a) where
    rnf (Seq xs) = rnf xs

instance Monad Seq where
    return = singleton
    xs >>= f = foldl' add empty xs
      where add ys x = ys >< f x

instance MonadPlus Seq where
    mzero = empty
    mplus = (><)

instance Eq a => Eq (Seq a) where
    xs == ys = length xs == length ys && toList xs == toList ys

instance Ord a => Ord (Seq a) where
    compare xs ys = compare (toList xs) (toList ys)

#if TESTING
instance Show a => Show (Seq a) where
    showsPrec p (Seq x) = showsPrec p x
#else
instance Show a => Show (Seq a) where
    showsPrec p xs = showParen (p > 10) $
        showString "fromList " . shows (toList xs)
#endif

instance Read a => Read (Seq a) where
#ifdef __GLASGOW_HASKELL__
    readPrec = parens $ prec 10 $ do
        Ident "fromList" <- lexP
        xs <- readPrec
        return (fromList xs)

    readListPrec = readListPrecDefault
#else
    readsPrec p = readParen (p > 10) $ \ r -> do
        ("fromList",s) <- lex r
        (xs,t) <- reads s
        return (fromList xs,t)
#endif

instance Monoid (Seq a) where
    mempty = empty
    mappend = (><)

#include "Typeable.h"
INSTANCE_TYPEABLE1(Seq,seqTc,"Seq")

#if __GLASGOW_HASKELL__
instance Data a => Data (Seq a) where
    gfoldl f z s    = case viewl s of
        EmptyL  -> z empty
        x :< xs -> z (<|) `f` x `f` xs

    gunfold k z c   = case constrIndex c of
        1 -> z empty
        2 -> k (k (z (<|)))
        _ -> error "gunfold"

    toConstr xs
      | null xs     = emptyConstr
      | otherwise   = consConstr

    dataTypeOf _    = seqDataType

    dataCast1 f     = gcast1 f

emptyConstr, consConstr :: Constr
emptyConstr = mkConstr seqDataType "empty" [] Prefix
consConstr  = mkConstr seqDataType "<|" [] Infix

seqDataType :: DataType
seqDataType = mkDataType "Data.Sequence.Seq" [emptyConstr, consConstr]
#endif

-- Finger trees

data FingerTree a
    = Empty
    | Single a
    | Deep {-# UNPACK #-} !Int !(Digit a) (FingerTree (Node a)) !(Digit a)
#if TESTING
    deriving Show
#endif

instance Sized a => Sized (FingerTree a) where
    {-# SPECIALIZE instance Sized (FingerTree (Elem a)) #-}
    {-# SPECIALIZE instance Sized (FingerTree (Node a)) #-}
    size Empty              = 0
    size (Single x)         = size x
    size (Deep v _ _ _)     = v

instance Foldable FingerTree where
    foldr _ z Empty = z
    foldr f z (Single x) = x `f` z
    foldr f z (Deep _ pr m sf) =
        foldr f (foldr (flip (foldr f)) (foldr f z sf) m) pr

    foldl _ z Empty = z
    foldl f z (Single x) = z `f` x
    foldl f z (Deep _ pr m sf) =
        foldl f (foldl (foldl f) (foldl f z pr) m) sf

    foldr1 _ Empty = error "foldr1: empty sequence"
    foldr1 _ (Single x) = x
    foldr1 f (Deep _ pr m sf) =
        foldr f (foldr (flip (foldr f)) (foldr1 f sf) m) pr

    foldl1 _ Empty = error "foldl1: empty sequence"
    foldl1 _ (Single x) = x
    foldl1 f (Deep _ pr m sf) =
        foldl f (foldl (foldl f) (foldl1 f pr) m) sf

instance Functor FingerTree where
    fmap _ Empty = Empty
    fmap f (Single x) = Single (f x)
    fmap f (Deep v pr m sf) =
        Deep v (fmap f pr) (fmap (fmap f) m) (fmap f sf)

instance Traversable FingerTree where
    traverse _ Empty = pure Empty
    traverse f (Single x) = Single <$> f x
    traverse f (Deep v pr m sf) =
        Deep v <$> traverse f pr <*> traverse (traverse f) m <*>
            traverse f sf

instance NFData a => NFData (FingerTree a) where
    rnf (Empty) = ()
    rnf (Single x) = rnf x
    rnf (Deep _ pr m sf) = rnf pr `seq` rnf m `seq` rnf sf

{-# INLINE deep #-}
deep            :: Sized a => Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
deep pr m sf    =  Deep (size pr + size m + size sf) pr m sf

{-# INLINE pullL #-}
pullL :: Sized a => Int -> FingerTree (Node a) -> Digit a -> FingerTree a
pullL s m sf = case viewLTree m of
    Nothing2        -> digitToTree' s sf
    Just2 pr m'     -> Deep s (nodeToDigit pr) m' sf

{-# INLINE pullR #-}
pullR :: Sized a => Int -> Digit a -> FingerTree (Node a) -> FingerTree a
pullR s pr m = case viewRTree m of
    Nothing2        -> digitToTree' s pr
    Just2 m' sf     -> Deep s pr m' (nodeToDigit sf)

{-# SPECIALIZE deepL :: Maybe (Digit (Elem a)) -> FingerTree (Node (Elem a)) -> Digit (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE deepL :: Maybe (Digit (Node a)) -> FingerTree (Node (Node a)) -> Digit (Node a) -> FingerTree (Node a) #-}
deepL :: Sized a => Maybe (Digit a) -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL Nothing m sf      = pullL (size m + size sf) m sf
deepL (Just pr) m sf    = deep pr m sf

{-# SPECIALIZE deepR :: Digit (Elem a) -> FingerTree (Node (Elem a)) -> Maybe (Digit (Elem a)) -> FingerTree (Elem a) #-}
{-# SPECIALIZE deepR :: Digit (Node a) -> FingerTree (Node (Node a)) -> Maybe (Digit (Node a)) -> FingerTree (Node a) #-}
deepR :: Sized a => Digit a -> FingerTree (Node a) -> Maybe (Digit a) -> FingerTree a
deepR pr m Nothing      = pullR (size m + size pr) pr m
deepR pr m (Just sf)    = deep pr m sf

-- Digits

data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a
#if TESTING
    deriving Show
#endif

instance Foldable Digit where
    foldr f z (One a) = a `f` z
    foldr f z (Two a b) = a `f` (b `f` z)
    foldr f z (Three a b c) = a `f` (b `f` (c `f` z))
    foldr f z (Four a b c d) = a `f` (b `f` (c `f` (d `f` z)))

    foldl f z (One a) = z `f` a
    foldl f z (Two a b) = (z `f` a) `f` b
    foldl f z (Three a b c) = ((z `f` a) `f` b) `f` c
    foldl f z (Four a b c d) = (((z `f` a) `f` b) `f` c) `f` d

    foldr1 _ (One a) = a
    foldr1 f (Two a b) = a `f` b
    foldr1 f (Three a b c) = a `f` (b `f` c)
    foldr1 f (Four a b c d) = a `f` (b `f` (c `f` d))

    foldl1 _ (One a) = a
    foldl1 f (Two a b) = a `f` b
    foldl1 f (Three a b c) = (a `f` b) `f` c
    foldl1 f (Four a b c d) = ((a `f` b) `f` c) `f` d

instance Functor Digit where
    {-# INLINE fmap #-}
    fmap f (One a) = One (f a)
    fmap f (Two a b) = Two (f a) (f b)
    fmap f (Three a b c) = Three (f a) (f b) (f c)
    fmap f (Four a b c d) = Four (f a) (f b) (f c) (f d)

instance Traversable Digit where
    {-# INLINE traverse #-}
    traverse f (One a) = One <$> f a
    traverse f (Two a b) = Two <$> f a <*> f b
    traverse f (Three a b c) = Three <$> f a <*> f b <*> f c
    traverse f (Four a b c d) = Four <$> f a <*> f b <*> f c <*> f d

instance NFData a => NFData (Digit a) where
    rnf (One a) = rnf a
    rnf (Two a b) = rnf a `seq` rnf b
    rnf (Three a b c) = rnf a `seq` rnf b `seq` rnf c
    rnf (Four a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

instance Sized a => Sized (Digit a) where
    {-# INLINE size #-}
    size = foldl1 (+) . fmap size

{-# SPECIALIZE digitToTree :: Digit (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE digitToTree :: Digit (Node a) -> FingerTree (Node a) #-}
digitToTree     :: Sized a => Digit a -> FingerTree a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

-- | Given the size of a digit and the digit itself, efficiently converts
-- it to a FingerTree.
digitToTree' :: Int -> Digit a -> FingerTree a
digitToTree' n (Four a b c d) = Deep n (Two a b) Empty (Two c d)
digitToTree' n (Three a b c) = Deep n (Two a b) Empty (One c)
digitToTree' n (Two a b) = Deep n (One a) Empty (One b)
digitToTree' n (One a) = n `seq` Single a

-- Nodes

data Node a
    = Node2 {-# UNPACK #-} !Int a a
    | Node3 {-# UNPACK #-} !Int a a a
#if TESTING
    deriving Show
#endif

instance Foldable Node where
    foldr f z (Node2 _ a b) = a `f` (b `f` z)
    foldr f z (Node3 _ a b c) = a `f` (b `f` (c `f` z))

    foldl f z (Node2 _ a b) = (z `f` a) `f` b
    foldl f z (Node3 _ a b c) = ((z `f` a) `f` b) `f` c

instance Functor Node where
    {-# INLINE fmap #-}
    fmap f (Node2 v a b) = Node2 v (f a) (f b)
    fmap f (Node3 v a b c) = Node3 v (f a) (f b) (f c)

instance Traversable Node where
    {-# INLINE traverse #-}
    traverse f (Node2 v a b) = Node2 v <$> f a <*> f b
    traverse f (Node3 v a b c) = Node3 v <$> f a <*> f b <*> f c

instance NFData a => NFData (Node a) where
    rnf (Node2 _ a b) = rnf a `seq` rnf b
    rnf (Node3 _ a b c) = rnf a `seq` rnf b `seq` rnf c

instance Sized (Node a) where
    size (Node2 v _ _)      = v
    size (Node3 v _ _ _)    = v

{-# INLINE node2 #-}
node2           :: Sized a => a -> a -> Node a
node2 a b       =  Node2 (size a + size b) a b

{-# INLINE node3 #-}
node3           :: Sized a => a -> a -> a -> Node a
node3 a b c     =  Node3 (size a + size b + size c) a b c

nodeToDigit :: Node a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

-- Elements

newtype Elem a  =  Elem { getElem :: a }
#if TESTING
    deriving Show
#endif

instance Sized (Elem a) where
    size _ = 1

instance Functor Elem where
    fmap f (Elem x) = Elem (f x)

instance Foldable Elem where
    foldr f z (Elem x) = f x z
    foldl f z (Elem x) = f z x

instance Traversable Elem where
    traverse f (Elem x) = Elem <$> f x

instance NFData a => NFData (Elem a) where
    rnf (Elem x) = rnf x

-------------------------------------------------------
-- Applicative construction
-------------------------------------------------------

newtype Id a = Id {runId :: a}

instance Functor Id where
    fmap f (Id x) = Id (f x)

instance Monad Id where
    return = Id
    m >>= k = k (runId m)

instance Applicative Id where
    pure = return
    (<*>) = ap

-- | This is essentially a clone of Control.Monad.State.Strict.
newtype State s a = State {runState :: s -> (s, a)}

instance Functor (State s) where
    fmap = liftA

instance Monad (State s) where
    {-# INLINE return #-}
    {-# INLINE (>>=) #-}
    return x = State $ \ s -> (s, x)
    m >>= k = State $ \ s -> case runState m s of
        (s', x) -> runState (k x) s'

instance Applicative (State s) where
    pure = return
    (<*>) = ap

execState :: State s a -> s -> a
execState m x = snd (runState m x)

-- | A helper method: a strict version of mapAccumL.
mapAccumL' :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
mapAccumL' f s t = runState (traverse (State . flip f) t) s

-- | 'applicativeTree' takes an Applicative-wrapped construction of a
-- piece of a FingerTree, assumed to always have the same size (which
-- is put in the second argument), and replicates it as many times as
-- specified.  This is a generalization of 'replicateA', which itself
-- is a generalization of many Data.Sequence methods.
{-# SPECIALIZE applicativeTree :: Int -> Int -> State s a -> State s (FingerTree a) #-}
{-# SPECIALIZE applicativeTree :: Int -> Int -> Id a -> Id (FingerTree a) #-}
-- Special note: the Id specialization automatically does node sharing,
-- reducing memory usage of the resulting tree to /O(log n)/.
applicativeTree :: Applicative f => Int -> Int -> f a -> f (FingerTree a)
applicativeTree n mSize m = mSize `seq` case n of
    0 -> pure Empty
    1 -> liftA Single m
    2 -> deepA one emptyTree one
    3 -> deepA two emptyTree one
    4 -> deepA two emptyTree two
    5 -> deepA three emptyTree two
    6 -> deepA three emptyTree three
    7 -> deepA four emptyTree three
    8 -> deepA four emptyTree four
    _ -> let (q, r) = n `quotRem` 3 in q `seq` case r of
        0 -> deepA three (applicativeTree (q - 2) mSize' n3) three
        1 -> deepA four (applicativeTree (q - 2) mSize' n3) three
        _ -> deepA four (applicativeTree (q - 2) mSize' n3) four
  where
    one = liftA One m
    two = liftA2 Two m m
    three = liftA3 Three m m m
    four = liftA3 Four m m m <*> m
    deepA = liftA3 (Deep (n * mSize))
    mSize' = 3 * mSize
    n3 = liftA3 (Node3 mSize') m m m
    emptyTree = pure Empty

------------------------------------------------------------------------
-- Construction
------------------------------------------------------------------------

-- | /O(1)/. The empty sequence.
empty           :: Seq a
empty           =  Seq Empty

-- | /O(1)/. A singleton sequence.
singleton       :: a -> Seq a
singleton x     =  Seq (Single (Elem x))

-- | /O(log n)/. @replicate n x@ is a sequence consisting of @n@ copies of @x@.
replicate       :: Int -> a -> Seq a
replicate n x
  | n >= 0      = runId (replicateA n (Id x))
  | otherwise   = error "replicate takes a nonnegative integer argument"

-- | 'replicateA' is an 'Applicative' version of 'replicate', and makes
-- /O(log n)/ calls to '<*>' and 'pure'.
--
-- > replicateA n x = sequenceA (replicate n x)
replicateA :: Applicative f => Int -> f a -> f (Seq a)
replicateA n x
  | n >= 0      = Seq <$> applicativeTree n 1 (Elem <$> x)
  | otherwise   = error "replicateA takes a nonnegative integer argument"

-- | 'replicateM' is a sequence counterpart of 'Control.Monad.replicateM'.
--
-- > replicateM n x = sequence (replicate n x)
replicateM :: Monad m => Int -> m a -> m (Seq a)
replicateM n x
  | n >= 0      = unwrapMonad (replicateA n (WrapMonad x))
  | otherwise   = error "replicateM takes a nonnegative integer argument"

-- | /O(1)/. Add an element to the left end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(<|)            :: a -> Seq a -> Seq a
x <| Seq xs     =  Seq (Elem x `consTree` xs)

{-# SPECIALIZE consTree :: Elem a -> FingerTree (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE consTree :: Node a -> FingerTree (Node a) -> FingerTree (Node a) #-}
consTree        :: Sized a => a -> FingerTree a -> FingerTree a
consTree a Empty        = Single a
consTree a (Single b)   = deep (One a) Empty (One b)
consTree a (Deep s (Four b c d e) m sf) = m `seq`
    Deep (size a + s) (Two a b) (node3 c d e `consTree` m) sf
consTree a (Deep s (Three b c d) m sf) =
    Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size a + s) (Two a b) m sf

-- | /O(1)/. Add an element to the right end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(|>)            :: Seq a -> a -> Seq a
Seq xs |> x     =  Seq (xs `snocTree` Elem x)

{-# SPECIALIZE snocTree :: FingerTree (Elem a) -> Elem a -> FingerTree (Elem a) #-}
{-# SPECIALIZE snocTree :: FingerTree (Node a) -> Node a -> FingerTree (Node a) #-}
snocTree        :: Sized a => FingerTree a -> a -> FingerTree a
snocTree Empty a        =  Single a
snocTree (Single a) b   =  deep (One a) Empty (One b)
snocTree (Deep s pr m (Four a b c d)) e = m `seq`
    Deep (s + size e) pr (m `snocTree` node3 a b c) (Two d e)
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size b) pr m (Two a b)

-- | /O(log(min(n1,n2)))/. Concatenate two sequences.
(><)            :: Seq a -> Seq a -> Seq a
Seq xs >< Seq ys = Seq (appendTree0 xs ys)

-- The appendTree/addDigits gunk below is machine generated

appendTree0 :: FingerTree (Elem a) -> FingerTree (Elem a) -> FingerTree (Elem a)
appendTree0 Empty xs =
    xs
appendTree0 xs Empty =
    xs
appendTree0 (Single x) xs =
    x `consTree` xs
appendTree0 xs (Single x) =
    xs `snocTree` x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    Deep (s1 + s2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2

addDigits0 :: FingerTree (Node (Elem a)) -> Digit (Elem a) -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> FingerTree (Node (Elem a))
addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

appendTree1 :: FingerTree (Node a) -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree1 Empty a xs =
    a `consTree` xs
appendTree1 xs a Empty =
    xs `snocTree` a
appendTree1 (Single x) a xs =
    x `consTree` a `consTree` xs
appendTree1 xs a (Single x) =
    xs `snocTree` a `snocTree` x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + s2) pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits1 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

appendTree2 :: FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree2 Empty a b xs =
    a `consTree` b `consTree` xs
appendTree2 xs a b Empty =
    xs `snocTree` a `snocTree` b
appendTree2 (Single x) a b xs =
    x `consTree` a `consTree` b `consTree` xs
appendTree2 xs a b (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + s2) pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

addDigits2 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

appendTree3 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree3 Empty a b c xs =
    a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c Empty =
    xs `snocTree` a `snocTree` b `snocTree` c
appendTree3 (Single x) a b c xs =
    x `consTree` a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + s2) pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

addDigits3 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

appendTree4 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree4 Empty a b c d xs =
    a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d Empty =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d
appendTree4 (Single x) a b c d xs =
    x `consTree` a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d `snocTree` x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + size d + s2) pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

addDigits4 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

-- | Builds a sequence from a seed value.  Takes time linear in the
-- number of generated elements.  /WARNING:/ If the number of generated
-- elements is infinite, this method will not terminate.
unfoldr :: (b -> Maybe (a, b)) -> b -> Seq a
unfoldr f = unfoldr' empty
  -- uses tail recursion rather than, for instance, the List implementation.
  where unfoldr' as b = maybe as (\ (a, b') -> unfoldr' (as |> a) b') (f b)

-- | @'unfoldl' f x@ is equivalent to @'reverse' ('unfoldr' ('fmap' swap . f) x)@.
unfoldl :: (b -> Maybe (b, a)) -> b -> Seq a
unfoldl f = unfoldl' empty
  where unfoldl' as b = maybe as (\ (b', a) -> unfoldl' (a <| as) b') (f b)

-- | /O(n)/.  Constructs a sequence by repeated application of a function
-- to a seed value.
--
-- > iterateN n f x = fromList (Prelude.take n (Prelude.iterate f x))
iterateN :: Int -> (a -> a) -> a -> Seq a
iterateN n f x
  | n >= 0      = replicateA n (State (\ y -> (f y, y))) `execState` x
  | otherwise   = error "iterateN takes a nonnegative integer argument"

------------------------------------------------------------------------
-- Deconstruction
------------------------------------------------------------------------

-- | /O(1)/. Is this the empty sequence?
null            :: Seq a -> Bool
null (Seq Empty) = True
null _          =  False

-- | /O(1)/. The number of elements in the sequence.
length          :: Seq a -> Int
length (Seq xs) =  size xs

-- Views

data Maybe2 a b = Nothing2 | Just2 a b

-- | View of the left end of a sequence.
data ViewL a
    = EmptyL        -- ^ empty sequence
    | a :< Seq a    -- ^ leftmost element and the rest of the sequence
#if __GLASGOW_HASKELL__
    deriving (Eq, Ord, Show, Read, Data)
#else
    deriving (Eq, Ord, Show, Read)
#endif

INSTANCE_TYPEABLE1(ViewL,viewLTc,"ViewL")

instance Functor ViewL where
    {-# INLINE fmap #-}
    fmap _ EmptyL       = EmptyL
    fmap f (x :< xs)    = f x :< fmap f xs

instance Foldable ViewL where
    foldr _ z EmptyL = z
    foldr f z (x :< xs) = f x (foldr f z xs)

    foldl _ z EmptyL = z
    foldl f z (x :< xs) = foldl f (f z x) xs

    foldl1 _ EmptyL = error "foldl1: empty view"
    foldl1 f (x :< xs) = foldl f x xs

instance Traversable ViewL where
    traverse _ EmptyL       = pure EmptyL
    traverse f (x :< xs)    = (:<) <$> f x <*> traverse f xs

-- | /O(1)/. Analyse the left end of a sequence.
viewl           ::  Seq a -> ViewL a
viewl (Seq xs)  =  case viewLTree xs of
    Nothing2 -> EmptyL
    Just2 (Elem x) xs' -> x :< Seq xs'

{-# SPECIALIZE viewLTree :: FingerTree (Elem a) -> Maybe2 (Elem a) (FingerTree (Elem a)) #-}
{-# SPECIALIZE viewLTree :: FingerTree (Node a) -> Maybe2 (Node a) (FingerTree (Node a)) #-}
viewLTree       :: Sized a => FingerTree a -> Maybe2 a (FingerTree a)
viewLTree Empty                 = Nothing2
viewLTree (Single a)            = Just2 a Empty
viewLTree (Deep s (One a) m sf) = Just2 a (pullL (s - size a) m sf)
viewLTree (Deep s (Two a b) m sf) =
    Just2 a (Deep (s - size a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
    Just2 a (Deep (s - size a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
    Just2 a (Deep (s - size a) (Three b c d) m sf)

-- | View of the right end of a sequence.
data ViewR a
    = EmptyR        -- ^ empty sequence
    | Seq a :> a    -- ^ the sequence minus the rightmost element,
            -- and the rightmost element
#if __GLASGOW_HASKELL__
    deriving (Eq, Ord, Show, Read, Data)
#else
    deriving (Eq, Ord, Show, Read)
#endif

INSTANCE_TYPEABLE1(ViewR,viewRTc,"ViewR")

instance Functor ViewR where
    {-# INLINE fmap #-}
    fmap _ EmptyR       = EmptyR
    fmap f (xs :> x)    = fmap f xs :> f x

instance Foldable ViewR where
    foldr _ z EmptyR = z
    foldr f z (xs :> x) = foldr f (f x z) xs

    foldl _ z EmptyR = z
    foldl f z (xs :> x) = foldl f z xs `f` x

    foldr1 _ EmptyR = error "foldr1: empty view"
    foldr1 f (xs :> x) = foldr f x xs

instance Traversable ViewR where
    traverse _ EmptyR       = pure EmptyR
    traverse f (xs :> x)    = (:>) <$> traverse f xs <*> f x

-- | /O(1)/. Analyse the right end of a sequence.
viewr           ::  Seq a -> ViewR a
viewr (Seq xs)  =  case viewRTree xs of
    Nothing2 -> EmptyR
    Just2 xs' (Elem x) -> Seq xs' :> x

{-# SPECIALIZE viewRTree :: FingerTree (Elem a) -> Maybe2 (FingerTree (Elem a)) (Elem a) #-}
{-# SPECIALIZE viewRTree :: FingerTree (Node a) -> Maybe2 (FingerTree (Node a)) (Node a) #-}
viewRTree       :: Sized a => FingerTree a -> Maybe2 (FingerTree a) a
viewRTree Empty                 = Nothing2
viewRTree (Single z)            = Just2 Empty z
viewRTree (Deep s pr m (One z)) = Just2 (pullR (s - size z) pr m) z
viewRTree (Deep s pr m (Two y z)) =
    Just2 (Deep (s - size z) pr m (One y)) z
viewRTree (Deep s pr m (Three x y z)) =
    Just2 (Deep (s - size z) pr m (Two x y)) z
viewRTree (Deep s pr m (Four w x y z)) =
    Just2 (Deep (s - size z) pr m (Three w x y)) z

------------------------------------------------------------------------
-- Scans
--
-- These are not particularly complex applications of the Traversable
-- functor, though making the correspondence with Data.List exact
-- requires the use of (<|) and (|>).
--
-- Note that save for the single (<|) or (|>), we maintain the original
-- structure of the Seq, not having to do any restructuring of our own.
--
-- wasserman.louis@gmail.com, 5/23/09
------------------------------------------------------------------------

-- | 'scanl' is similar to 'foldl', but returns a sequence of reduced
-- values from the left:
--
-- > scanl f z (fromList [x1, x2, ...]) = fromList [z, z `f` x1, (z `f` x1) `f` x2, ...]
scanl :: (a -> b -> a) -> a -> Seq b -> Seq a
scanl f z0 xs = z0 <| snd (mapAccumL (\ x z -> let x' = f x z in (x', x')) z0 xs)

-- | 'scanl1' is a variant of 'scanl' that has no starting value argument:
--
-- > scanl1 f (fromList [x1, x2, ...]) = fromList [x1, x1 `f` x2, ...]
scanl1 :: (a -> a -> a) -> Seq a -> Seq a
scanl1 f xs = case viewl xs of
    EmptyL          -> error "scanl1 takes a nonempty sequence as an argument"
    x :< xs'        -> scanl f x xs'

-- | 'scanr' is the right-to-left dual of 'scanl'.
scanr :: (a -> b -> b) -> b -> Seq a -> Seq b
scanr f z0 xs = snd (mapAccumR (\ z x -> let z' = f x z in (z', z')) z0 xs) |> z0

-- | 'scanr1' is a variant of 'scanr' that has no starting value argument.
scanr1 :: (a -> a -> a) -> Seq a -> Seq a
scanr1 f xs = case viewr xs of
    EmptyR          -> error "scanr1 takes a nonempty sequence as an argument"
    xs' :> x        -> scanr f x xs'

-- Indexing

-- | /O(log(min(i,n-i)))/. The element at the specified position,
-- counting from 0.  The argument should thus be a non-negative
-- integer less than the size of the sequence.
-- If the position is out of range, 'index' fails with an error.
index           :: Seq a -> Int -> a
index (Seq xs) i
  | 0 <= i && i < size xs = case lookupTree i xs of
                Place _ (Elem x) -> x
  | otherwise   = error "index out of bounds"

data Place a = Place {-# UNPACK #-} !Int a
#if TESTING
    deriving Show
#endif

{-# SPECIALIZE lookupTree :: Int -> FingerTree (Elem a) -> Place (Elem a) #-}
{-# SPECIALIZE lookupTree :: Int -> FingerTree (Node a) -> Place (Node a) #-}
lookupTree :: Sized a => Int -> FingerTree a -> Place a
lookupTree _ Empty = error "lookupTree of empty tree"
lookupTree i (Single x) = Place i x
lookupTree i (Deep _ pr m sf)
  | i < spr     =  lookupDigit i pr
  | i < spm     =  case lookupTree (i - spr) m of
                   Place i' xs -> lookupNode i' xs
  | otherwise   =  lookupDigit (i - spm) sf
  where
    spr     = size pr
    spm     = spr + size m

{-# SPECIALIZE lookupNode :: Int -> Node (Elem a) -> Place (Elem a) #-}
{-# SPECIALIZE lookupNode :: Int -> Node (Node a) -> Place (Node a) #-}
lookupNode :: Sized a => Int -> Node a -> Place a
lookupNode i (Node2 _ a b)
  | i < sa      = Place i a
  | otherwise   = Place (i - sa) b
  where
    sa      = size a
lookupNode i (Node3 _ a b c)
  | i < sa      = Place i a
  | i < sab     = Place (i - sa) b
  | otherwise   = Place (i - sab) c
  where
    sa      = size a
    sab     = sa + size b

{-# SPECIALIZE lookupDigit :: Int -> Digit (Elem a) -> Place (Elem a) #-}
{-# SPECIALIZE lookupDigit :: Int -> Digit (Node a) -> Place (Node a) #-}
lookupDigit :: Sized a => Int -> Digit a -> Place a
lookupDigit i (One a) = Place i a
lookupDigit i (Two a b)
  | i < sa      = Place i a
  | otherwise   = Place (i - sa) b
  where
    sa      = size a
lookupDigit i (Three a b c)
  | i < sa      = Place i a
  | i < sab     = Place (i - sa) b
  | otherwise   = Place (i - sab) c
  where
    sa      = size a
    sab     = sa + size b
lookupDigit i (Four a b c d)
  | i < sa      = Place i a
  | i < sab     = Place (i - sa) b
  | i < sabc    = Place (i - sab) c
  | otherwise   = Place (i - sabc) d
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c

-- | /O(log(min(i,n-i)))/. Replace the element at the specified position.
-- If the position is out of range, the original sequence is returned.
update          :: Int -> a -> Seq a -> Seq a
update i x      = adjust (const x) i

-- | /O(log(min(i,n-i)))/. Update the element at the specified position.
-- If the position is out of range, the original sequence is returned.
adjust          :: (a -> a) -> Int -> Seq a -> Seq a
adjust f i (Seq xs)
  | 0 <= i && i < size xs = Seq (adjustTree (const (fmap f)) i xs)
  | otherwise   = Seq xs

{-# SPECIALIZE adjustTree :: (Int -> Elem a -> Elem a) -> Int -> FingerTree (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE adjustTree :: (Int -> Node a -> Node a) -> Int -> FingerTree (Node a) -> FingerTree (Node a) #-}
adjustTree      :: Sized a => (Int -> a -> a) ->
            Int -> FingerTree a -> FingerTree a
adjustTree _ _ Empty = error "adjustTree of empty tree"
adjustTree f i (Single x) = Single (f i x)
adjustTree f i (Deep s pr m sf)
  | i < spr     = Deep s (adjustDigit f i pr) m sf
  | i < spm     = Deep s pr (adjustTree (adjustNode f) (i - spr) m) sf
  | otherwise   = Deep s pr m (adjustDigit f (i - spm) sf)
  where
    spr     = size pr
    spm     = spr + size m

{-# SPECIALIZE adjustNode :: (Int -> Elem a -> Elem a) -> Int -> Node (Elem a) -> Node (Elem a) #-}
{-# SPECIALIZE adjustNode :: (Int -> Node a -> Node a) -> Int -> Node (Node a) -> Node (Node a) #-}
adjustNode      :: Sized a => (Int -> a -> a) -> Int -> Node a -> Node a
adjustNode f i (Node2 s a b)
  | i < sa      = Node2 s (f i a) b
  | otherwise   = Node2 s a (f (i - sa) b)
  where
    sa      = size a
adjustNode f i (Node3 s a b c)
  | i < sa      = Node3 s (f i a) b c
  | i < sab     = Node3 s a (f (i - sa) b) c
  | otherwise   = Node3 s a b (f (i - sab) c)
  where
    sa      = size a
    sab     = sa + size b

{-# SPECIALIZE adjustDigit :: (Int -> Elem a -> Elem a) -> Int -> Digit (Elem a) -> Digit (Elem a) #-}
{-# SPECIALIZE adjustDigit :: (Int -> Node a -> Node a) -> Int -> Digit (Node a) -> Digit (Node a) #-}
adjustDigit     :: Sized a => (Int -> a -> a) -> Int -> Digit a -> Digit a
adjustDigit f i (One a) = One (f i a)
adjustDigit f i (Two a b)
  | i < sa      = Two (f i a) b
  | otherwise   = Two a (f (i - sa) b)
  where
    sa      = size a
adjustDigit f i (Three a b c)
  | i < sa      = Three (f i a) b c
  | i < sab     = Three a (f (i - sa) b) c
  | otherwise   = Three a b (f (i - sab) c)
  where
    sa      = size a
    sab     = sa + size b
adjustDigit f i (Four a b c d)
  | i < sa      = Four (f i a) b c d
  | i < sab     = Four a (f (i - sa) b) c d
  | i < sabc    = Four a b (f (i - sab) c) d
  | otherwise   = Four a b c (f (i- sabc) d)
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c

-- | A generalization of 'fmap', 'mapWithIndex' takes a mapping function
-- that also depends on the element's index, and applies it to every
-- element in the sequence.
mapWithIndex :: (Int -> a -> b) -> Seq a -> Seq b
mapWithIndex f xs = snd (mapAccumL' (\ i x -> (i + 1, f i x)) 0 xs)

-- Splitting

-- | /O(log(min(i,n-i)))/. The first @i@ elements of a sequence.
-- If @i@ is negative, @'take' i s@ yields the empty sequence.
-- If the sequence contains fewer than @i@ elements, the whole sequence
-- is returned.
take            :: Int -> Seq a -> Seq a
take i          =  fst . splitAt i

-- | /O(log(min(i,n-i)))/. Elements of a sequence after the first @i@.
-- If @i@ is negative, @'drop' i s@ yields the whole sequence.
-- If the sequence contains fewer than @i@ elements, the empty sequence
-- is returned.
drop            :: Int -> Seq a -> Seq a
drop i          =  snd . splitAt i

-- | /O(log(min(i,n-i)))/. Split a sequence at a given position.
-- @'splitAt' i s = ('take' i s, 'drop' i s)@.
splitAt                 :: Int -> Seq a -> (Seq a, Seq a)
splitAt i (Seq xs)      =  (Seq l, Seq r)
  where (l, r)          =  split i xs

split :: Int -> FingerTree (Elem a) ->
    (FingerTree (Elem a), FingerTree (Elem a))
split i Empty   = i `seq` (Empty, Empty)
split i xs
  | size xs > i = (l, consTree x r)
  | otherwise   = (xs, Empty)
  where Split l x r = splitTree i xs

data Split t a = Split t a t
#if TESTING
    deriving Show
#endif

{-# SPECIALIZE splitTree :: Int -> FingerTree (Elem a) -> Split (FingerTree (Elem a)) (Elem a) #-}
{-# SPECIALIZE splitTree :: Int -> FingerTree (Node a) -> Split (FingerTree (Node a)) (Node a) #-}
splitTree :: Sized a => Int -> FingerTree a -> Split (FingerTree a) a
splitTree _ Empty = error "splitTree of empty tree"
splitTree i (Single x) = i `seq` Split Empty x Empty
splitTree i (Deep _ pr m sf)
  | i < spr     = case splitDigit i pr of
            Split l x r -> Split (maybe Empty digitToTree l) x (deepL r m sf)
  | i < spm     = case splitTree im m of
            Split ml xs mr -> case splitNode (im - size ml) xs of
                Split l x r -> Split (deepR pr ml l) x (deepL r mr sf)
  | otherwise   = case splitDigit (i - spm) sf of
            Split l x r -> Split (deepR pr m l) x (maybe Empty digitToTree r)
  where
    spr     = size pr
    spm     = spr + size m
    im      = i - spr

{-# SPECIALIZE splitNode :: Int -> Node (Elem a) -> Split (Maybe (Digit (Elem a))) (Elem a) #-}
{-# SPECIALIZE splitNode :: Int -> Node (Node a) -> Split (Maybe (Digit (Node a))) (Node a) #-}
splitNode :: Sized a => Int -> Node a -> Split (Maybe (Digit a)) a
splitNode i (Node2 _ a b)
  | i < sa      = Split Nothing a (Just (One b))
  | otherwise   = Split (Just (One a)) b Nothing
  where
    sa      = size a
splitNode i (Node3 _ a b c)
  | i < sa      = Split Nothing a (Just (Two b c))
  | i < sab     = Split (Just (One a)) b (Just (One c))
  | otherwise   = Split (Just (Two a b)) c Nothing
  where
    sa      = size a
    sab     = sa + size b

{-# SPECIALIZE splitDigit :: Int -> Digit (Elem a) -> Split (Maybe (Digit (Elem a))) (Elem a) #-}
{-# SPECIALIZE splitDigit :: Int -> Digit (Node a) -> Split (Maybe (Digit (Node a))) (Node a) #-}
splitDigit :: Sized a => Int -> Digit a -> Split (Maybe (Digit a)) a
splitDigit i (One a) = i `seq` Split Nothing a Nothing
splitDigit i (Two a b)
  | i < sa      = Split Nothing a (Just (One b))
  | otherwise   = Split (Just (One a)) b Nothing
  where
    sa      = size a
splitDigit i (Three a b c)
  | i < sa      = Split Nothing a (Just (Two b c))
  | i < sab     = Split (Just (One a)) b (Just (One c))
  | otherwise   = Split (Just (Two a b)) c Nothing
  where
    sa      = size a
    sab     = sa + size b
splitDigit i (Four a b c d)
  | i < sa      = Split Nothing a (Just (Three b c d))
  | i < sab     = Split (Just (One a)) b (Just (Two c d))
  | i < sabc    = Split (Just (Two a b)) c (Just (One d))
  | otherwise   = Split (Just (Three a b c)) d Nothing
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c

-- | /O(n)/.  Returns a sequence of all suffixes of this sequence,
-- longest first.  For example,
--
-- > tails (fromList "abc") = fromList [fromList "abc", fromList "bc", fromList "c", fromList ""]
--
-- Evaluating the /i/th suffix takes /O(log(min(i, n-i)))/, but evaluating
-- every suffix in the sequence takes /O(n)/ due to sharing.
tails                   :: Seq a -> Seq (Seq a)
tails (Seq xs)          = Seq (tailsTree (Elem . Seq) xs) |> empty

-- | /O(n)/.  Returns a sequence of all prefixes of this sequence,
-- shortest first.  For example,
--
-- > inits (fromList "abc") = fromList [fromList "", fromList "a", fromList "ab", fromList "abc"]
--
-- Evaluating the /i/th prefix takes /O(log(min(i, n-i)))/, but evaluating
-- every prefix in the sequence takes /O(n)/ due to sharing.
inits                   :: Seq a -> Seq (Seq a)
inits (Seq xs)          = empty <| Seq (initsTree (Elem . Seq) xs)

-- This implementation of tails (and, analogously, inits) has the
-- following algorithmic advantages:
--      Evaluating each tail in the sequence takes linear total time,
--      which is better than we could say for
--              @fromList [drop n xs | n <- [0..length xs]]@.
--      Evaluating any individual tail takes logarithmic time, which is
--      better than we can say for either
--              @scanr (<|) empty xs@ or @iterateN (length xs + 1) (\ xs -> let _ :< xs' = viewl xs in xs') xs@.
--
-- Moreover, if we actually look at every tail in the sequence, the
-- following benchmarks demonstrate that this implementation is modestly
-- faster than any of the above:
--
-- Times (ms)
--               min      mean    +/-sd    median    max
-- Seq.tails:   21.986   24.961   10.169   22.417   86.485
-- scanr:       85.392   87.942    2.488   87.425  100.217
-- iterateN:       29.952   31.245    1.574   30.412   37.268
--
-- The algorithm for tails (and, analogously, inits) is as follows:
--
-- A Node in the FingerTree of tails is constructed by evaluating the
-- corresponding tail of the FingerTree of Nodes, considering the first
-- Node in this tail, and constructing a Node in which each tail of this
-- Node is made to be the prefix of the remaining tree.  This ends up
-- working quite elegantly, as the remainder of the tail of the FingerTree
-- of Nodes becomes the middle of a new tail, the suffix of the Node is
-- the prefix, and the suffix of the original tree is retained.
--
-- In particular, evaluating the /i/th tail involves making as
-- many partial evaluations as the Node depth of the /i/th element.
-- In addition, when we evaluate the /i/th tail, and we also evaluate
-- the /j/th tail, and /m/ Nodes are on the path to both /i/ and /j/,
-- each of those /m/ evaluations are shared between the computation of
-- the /i/th and /j/th tails.
--
-- wasserman.louis@gmail.com, 7/16/09

tailsDigit :: Digit a -> Digit (Digit a)
tailsDigit (One a) = One (One a)
tailsDigit (Two a b) = Two (Two a b) (One b)
tailsDigit (Three a b c) = Three (Three a b c) (Two b c) (One c)
tailsDigit (Four a b c d) = Four (Four a b c d) (Three b c d) (Two c d) (One d)

initsDigit :: Digit a -> Digit (Digit a)
initsDigit (One a) = One (One a)
initsDigit (Two a b) = Two (One a) (Two a b)
initsDigit (Three a b c) = Three (One a) (Two a b) (Three a b c)
initsDigit (Four a b c d) = Four (One a) (Two a b) (Three a b c) (Four a b c d)

tailsNode :: Node a -> Node (Digit a)
tailsNode (Node2 s a b) = Node2 s (Two a b) (One b)
tailsNode (Node3 s a b c) = Node3 s (Three a b c) (Two b c) (One c)

initsNode :: Node a -> Node (Digit a)
initsNode (Node2 s a b) = Node2 s (One a) (Two a b)
initsNode (Node3 s a b c) = Node3 s (One a) (Two a b) (Three a b c)

{-# SPECIALIZE tailsTree :: (FingerTree (Elem a) -> Elem b) -> FingerTree (Elem a) -> FingerTree (Elem b) #-}
{-# SPECIALIZE tailsTree :: (FingerTree (Node a) -> Node b) -> FingerTree (Node a) -> FingerTree (Node b) #-}
-- | Given a function to apply to tails of a tree, applies that function
-- to every tail of the specified tree.
tailsTree :: (Sized a, Sized b) => (FingerTree a -> b) -> FingerTree a -> FingerTree b
tailsTree _ Empty = Empty
tailsTree f (Single x) = Single (f (Single x))
tailsTree f (Deep n pr m sf) =
    Deep n (fmap (\ pr' -> f (deep pr' m sf)) (tailsDigit pr))
        (tailsTree f' m)
        (fmap (f . digitToTree) (tailsDigit sf))
  where
    f' ms = let Just2 node m' = viewLTree ms in
        fmap (\ pr' -> f (deep pr' m' sf)) (tailsNode node)

{-# SPECIALIZE initsTree :: (FingerTree (Elem a) -> Elem b) -> FingerTree (Elem a) -> FingerTree (Elem b) #-}
{-# SPECIALIZE initsTree :: (FingerTree (Node a) -> Node b) -> FingerTree (Node a) -> FingerTree (Node b) #-}
-- | Given a function to apply to inits of a tree, applies that function
-- to every init of the specified tree.
initsTree :: (Sized a, Sized b) => (FingerTree a -> b) -> FingerTree a -> FingerTree b
initsTree _ Empty = Empty
initsTree f (Single x) = Single (f (Single x))
initsTree f (Deep n pr m sf) =
    Deep n (fmap (f . digitToTree) (initsDigit pr))
        (initsTree f' m)
        (fmap (f . deep pr m) (initsDigit sf))
  where
    f' ms =  let Just2 m' node = viewRTree ms in
             fmap (\ sf' -> f (deep pr m' sf')) (initsNode node)

{-# INLINE foldlWithIndex #-}
-- | 'foldlWithIndex' is a version of 'foldl' that also provides access
-- to the index of each element.
foldlWithIndex :: (b -> Int -> a -> b) -> b -> Seq a -> b
foldlWithIndex f z xs = foldl (\ g x i -> i `seq` f (g (i - 1)) i x) (const z) xs (length xs - 1)

{-# INLINE foldrWithIndex #-}
-- | 'foldrWithIndex' is a version of 'foldr' that also provides access
-- to the index of each element.
foldrWithIndex :: (Int -> a -> b -> b) -> b -> Seq a -> b
foldrWithIndex f z xs = foldr (\ x g i -> i `seq` f i x (g (i+1))) (const z) xs 0

{-# INLINE listToMaybe' #-}
-- 'listToMaybe\'' is a good consumer version of 'listToMaybe'.
listToMaybe' :: [a] -> Maybe a
listToMaybe' = foldr (\ x _ -> Just x) Nothing

-- | /O(i)/ where /i/ is the prefix length.  'takeWhileL', applied
-- to a predicate @p@ and a sequence @xs@, returns the longest prefix
-- (possibly empty) of @xs@ of elements that satisfy @p@.
takeWhileL :: (a -> Bool) -> Seq a -> Seq a
takeWhileL p = fst . spanl p

-- | /O(i)/ where /i/ is the suffix length.  'takeWhileR', applied
-- to a predicate @p@ and a sequence @xs@, returns the longest suffix
-- (possibly empty) of @xs@ of elements that satisfy @p@.
--
-- @'takeWhileR' p xs@ is equivalent to @'reverse' ('takeWhileL' p ('reverse' xs))@.
takeWhileR :: (a -> Bool) -> Seq a -> Seq a
takeWhileR p = fst . spanr p

-- | /O(i)/ where /i/ is the prefix length.  @'dropWhileL' p xs@ returns
-- the suffix remaining after @'takeWhileL' p xs@.
dropWhileL :: (a -> Bool) -> Seq a -> Seq a
dropWhileL p = snd . spanl p

-- | /O(i)/ where /i/ is the suffix length.  @'dropWhileR' p xs@ returns
-- the prefix remaining after @'takeWhileR' p xs@.
--
-- @'dropWhileR' p xs@ is equivalent to @'reverse' ('dropWhileL' p ('reverse' xs))@.
dropWhileR :: (a -> Bool) -> Seq a -> Seq a
dropWhileR p = snd . spanr p

-- | /O(i)/ where /i/ is the prefix length.  'spanl', applied to
-- a predicate @p@ and a sequence @xs@, returns a pair whose first
-- element is the longest prefix (possibly empty) of @xs@ of elements that
-- satisfy @p@ and the second element is the remainder of the sequence.
spanl :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
spanl p = breakl (not . p)

-- | /O(i)/ where /i/ is the suffix length.  'spanr', applied to a
-- predicate @p@ and a sequence @xs@, returns a pair whose /first/ element
-- is the longest /suffix/ (possibly empty) of @xs@ of elements that
-- satisfy @p@ and the second element is the remainder of the sequence.
spanr :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
spanr p = breakr (not . p)

{-# INLINE breakl #-}
-- | /O(i)/ where /i/ is the breakpoint index.  'breakl', applied to a
-- predicate @p@ and a sequence @xs@, returns a pair whose first element
-- is the longest prefix (possibly empty) of @xs@ of elements that
-- /do not satisfy/ @p@ and the second element is the remainder of
-- the sequence.
--
-- @'breakl' p@ is equivalent to @'spanl' (not . p)@.
breakl :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
breakl p xs = foldr (\ i _ -> splitAt i xs) (xs, empty) (findIndicesL p xs)

{-# INLINE breakr #-}
-- | @'breakr' p@ is equivalent to @'spanr' (not . p)@.
breakr :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
breakr p xs = foldr (\ i _ -> flipPair (splitAt (i + 1) xs)) (xs, empty) (findIndicesR p xs)
  where flipPair (x, y) = (y, x)

-- | /O(n)/.  The 'partition' function takes a predicate @p@ and a
-- sequence @xs@ and returns sequences of those elements which do and
-- do not satisfy the predicate.
partition :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
partition p = foldl part (empty, empty)
  where
    part (xs, ys) x
      | p x         = (xs |> x, ys)
      | otherwise   = (xs, ys |> x)

-- | /O(n)/.  The 'filter' function takes a predicate @p@ and a sequence
-- @xs@ and returns a sequence of those elements which satisfy the
-- predicate.
filter :: (a -> Bool) -> Seq a -> Seq a
filter p = foldl (\ xs x -> if p x then xs |> x else xs) empty

-- Indexing sequences

-- | 'elemIndexL' finds the leftmost index of the specified element,
-- if it is present, and otherwise 'Nothing'.
elemIndexL :: Eq a => a -> Seq a -> Maybe Int
elemIndexL x = findIndexL (x ==)

-- | 'elemIndexR' finds the rightmost index of the specified element,
-- if it is present, and otherwise 'Nothing'.
elemIndexR :: Eq a => a -> Seq a -> Maybe Int
elemIndexR x = findIndexR (x ==)

-- | 'elemIndicesL' finds the indices of the specified element, from
-- left to right (i.e. in ascending order).
elemIndicesL :: Eq a => a -> Seq a -> [Int]
elemIndicesL x = findIndicesL (x ==)

-- | 'elemIndicesR' finds the indices of the specified element, from
-- right to left (i.e. in descending order).
elemIndicesR :: Eq a => a -> Seq a -> [Int]
elemIndicesR x = findIndicesR (x ==)

-- | @'findIndexL' p xs@ finds the index of the leftmost element that
-- satisfies @p@, if any exist.
findIndexL :: (a -> Bool) -> Seq a -> Maybe Int
findIndexL p = listToMaybe' . findIndicesL p

-- | @'findIndexR' p xs@ finds the index of the rightmost element that
-- satisfies @p@, if any exist.
findIndexR :: (a -> Bool) -> Seq a -> Maybe Int
findIndexR p = listToMaybe' . findIndicesR p

{-# INLINE findIndicesL #-}
-- | @'findIndicesL' p@ finds all indices of elements that satisfy @p@,
-- in ascending order.
findIndicesL :: (a -> Bool) -> Seq a -> [Int]
#if __GLASGOW_HASKELL__
findIndicesL p xs = build (\ c n -> let g i x z = if p x then c i z else z in
                foldrWithIndex g n xs)
#else
findIndicesL p xs = foldrWithIndex g [] xs
  where g i x is = if p x then i:is else is
#endif

{-# INLINE findIndicesR #-}
-- | @'findIndicesR' p@ finds all indices of elements that satisfy @p@,
-- in descending order.
findIndicesR :: (a -> Bool) -> Seq a -> [Int]
#if __GLASGOW_HASKELL__
findIndicesR p xs = build (\ c n ->
    let g z i x = if p x then c i z else z in foldlWithIndex g n xs)
#else
findIndicesR p xs = foldlWithIndex g [] xs
  where g is i x = if p x then i:is else is
#endif

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

-- | /O(n)/. Create a sequence from a finite list of elements.
-- There is a function 'toList' in the opposite direction for all
-- instances of the 'Foldable' class, including 'Seq'.
fromList        :: [a] -> Seq a
fromList        =  Data.List.foldl' (|>) empty

------------------------------------------------------------------------
-- Reverse
------------------------------------------------------------------------

-- | /O(n)/. The reverse of a sequence.
reverse :: Seq a -> Seq a
reverse (Seq xs) = Seq (reverseTree id xs)

reverseTree :: (a -> a) -> FingerTree a -> FingerTree a
reverseTree _ Empty = Empty
reverseTree f (Single x) = Single (f x)
reverseTree f (Deep s pr m sf) =
    Deep s (reverseDigit f sf)
        (reverseTree (reverseNode f) m)
        (reverseDigit f pr)

{-# INLINE reverseDigit #-}
reverseDigit :: (a -> a) -> Digit a -> Digit a
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)

reverseNode :: (a -> a) -> Node a -> Node a
reverseNode f (Node2 s a b) = Node2 s (f b) (f a)
reverseNode f (Node3 s a b c) = Node3 s (f c) (f b) (f a)

------------------------------------------------------------------------
-- Zipping
------------------------------------------------------------------------

-- | /O(min(n1,n2))/.  'zip' takes two sequences and returns a sequence
-- of corresponding pairs.  If one input is short, excess elements are
-- discarded from the right end of the longer sequence.
zip :: Seq a -> Seq b -> Seq (a, b)
zip = zipWith (,)

-- | /O(min(n1,n2))/.  'zipWith' generalizes 'zip' by zipping with the
-- function given as the first argument, instead of a tupling function.
-- For example, @zipWith (+)@ is applied to two sequences to take the
-- sequence of corresponding sums.
zipWith :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f xs ys
  | length xs <= length ys      = zipWith' f xs ys
  | otherwise                   = zipWith' (flip f) ys xs

-- like 'zipWith', but assumes length xs <= length ys
zipWith' :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith' f xs ys = snd (mapAccumL k ys xs)
  where
    k kys x = case viewl kys of
           (z :< zs) -> (zs, f x z)
           EmptyL    -> error "zipWith': unexpected EmptyL"

-- | /O(min(n1,n2,n3))/.  'zip3' takes three sequences and returns a
-- sequence of triples, analogous to 'zip'.
zip3 :: Seq a -> Seq b -> Seq c -> Seq (a,b,c)
zip3 = zipWith3 (,,)

-- | /O(min(n1,n2,n3))/.  'zipWith3' takes a function which combines
-- three elements, as well as three sequences and returns a sequence of
-- their point-wise combinations, analogous to 'zipWith'.
zipWith3 :: (a -> b -> c -> d) -> Seq a -> Seq b -> Seq c -> Seq d
zipWith3 f s1 s2 s3 = zipWith ($) (zipWith f s1 s2) s3

-- | /O(min(n1,n2,n3,n4))/.  'zip4' takes four sequences and returns a
-- sequence of quadruples, analogous to 'zip'.
zip4 :: Seq a -> Seq b -> Seq c -> Seq d -> Seq (a,b,c,d)
zip4 = zipWith4 (,,,)

-- | /O(min(n1,n2,n3,n4))/.  'zipWith4' takes a function which combines
-- four elements, as well as four sequences and returns a sequence of
-- their point-wise combinations, analogous to 'zipWith'.
zipWith4 :: (a -> b -> c -> d -> e) -> Seq a -> Seq b -> Seq c -> Seq d -> Seq e
zipWith4 f s1 s2 s3 s4 = zipWith ($) (zipWith ($) (zipWith f s1 s2) s3) s4

------------------------------------------------------------------------
-- Sorting
--
-- sort and sortBy are implemented by simple deforestations of
--      \ xs -> fromList2 (length xs) . Data.List.sortBy cmp . toList
-- which does not get deforested automatically, it would appear.
--
-- Unstable sorting is performed by a heap sort implementation based on
-- pairing heaps.  Because the internal structure of sequences is quite
-- varied, it is difficult to get blocks of elements of roughly the same
-- length, which would improve merge sort performance.  Pairing heaps,
-- on the other hand, are relatively resistant to the effects of merging
-- heaps of wildly different sizes, as guaranteed by its amortized
-- constant-time merge operation.  Moreover, extensive use of SpecConstr
-- transformations can be done on pairing heaps, especially when we're
-- only constructing them to immediately be unrolled.
--
-- On purely random sequences of length 50000, with no RTS options,
-- I get the following statistics, in which heapsort is about 42.5%
-- faster:  (all comparisons done with -O2)
--
-- Times (ms)            min      mean    +/-sd    median    max
-- to/from list:       103.802  108.572    7.487  106.436  143.339
-- unstable heapsort:   60.686   62.968    4.275   61.187   79.151
--
-- Heapsort, it would seem, is less of a memory hog than Data.List.sortBy.
-- The gap is narrowed when more memory is available, but heapsort still
-- wins, 15% faster, with +RTS -H128m:
--
-- Times (ms)            min    mean    +/-sd  median    max
-- to/from list:       42.692  45.074   2.596  44.600  56.601
-- unstable heapsort:  37.100  38.344   3.043  37.715  55.526
--
-- In addition, on strictly increasing sequences the gap is even wider
-- than normal; heapsort is 68.5% faster with no RTS options:
-- Times (ms)            min    mean    +/-sd  median    max
-- to/from list:       52.236  53.574   1.987  53.034  62.098
-- unstable heapsort:  16.433  16.919   0.931  16.681  21.622
--
-- This may be attributed to the elegant nature of the pairing heap.
--
-- wasserman.louis@gmail.com, 7/20/09
------------------------------------------------------------------------

-- | /O(n log n)/.  'sort' sorts the specified 'Seq' by the natural
-- ordering of its elements.  The sort is stable.
-- If stability is not required, 'unstableSort' can be considerably
-- faster, and in particular uses less memory.
sort :: Ord a => Seq a -> Seq a
sort = sortBy compare

-- | /O(n log n)/.  'sortBy' sorts the specified 'Seq' according to the
-- specified comparator.  The sort is stable.
-- If stability is not required, 'unstableSortBy' can be considerably
-- faster, and in particular uses less memory.
sortBy :: (a -> a -> Ordering) -> Seq a -> Seq a
sortBy cmp xs = fromList2 (length xs) (Data.List.sortBy cmp (toList xs))

-- | /O(n log n)/.  'unstableSort' sorts the specified 'Seq' by
-- the natural ordering of its elements, but the sort is not stable.
-- This algorithm is frequently faster and uses less memory than 'sort',
-- and performs extremely well -- frequently twice as fast as 'sort' --
-- when the sequence is already nearly sorted.
unstableSort :: Ord a => Seq a -> Seq a
unstableSort = unstableSortBy compare

-- | /O(n log n)/.  A generalization of 'unstableSort', 'unstableSortBy'
-- takes an arbitrary comparator and sorts the specified sequence.
-- The sort is not stable.  This algorithm is frequently faster and
-- uses less memory than 'sortBy', and performs extremely well --
-- frequently twice as fast as 'sortBy' -- when the sequence is already
-- nearly sorted.
unstableSortBy :: (a -> a -> Ordering) -> Seq a -> Seq a
unstableSortBy cmp (Seq xs) =
    fromList2 (size xs) $ maybe [] (unrollPQ cmp) $
        toPQ cmp (\ (Elem x) -> PQueue x Nil) xs

-- | fromList2, given a list and its length, constructs a completely
-- balanced Seq whose elements are that list using the applicativeTree
-- generalization.
fromList2 :: Int -> [a] -> Seq a
fromList2 n = execState (replicateA n (State ht))
  where
    ht (x:xs) = (xs, x)
    ht []     = error "fromList2: short list"

-- | A 'PQueue' is a simple pairing heap.
data PQueue e = PQueue e (PQL e)
data PQL e = Nil | {-# UNPACK #-} !(PQueue e) :& PQL e

infixr 8 :&

#if TESTING

instance Functor PQueue where
    fmap f (PQueue x ts) = PQueue (f x) (fmap f ts)

instance Functor PQL where
    fmap f (q :& qs) = fmap f q :& fmap f qs
    fmap _ Nil = Nil

instance Show e => Show (PQueue e) where
    show = unlines . draw . fmap show

-- borrowed wholesale from Data.Tree, as Data.Tree actually depends
-- on Data.Sequence
draw :: PQueue String -> [String]
draw (PQueue x ts0) = x : drawSubTrees ts0
  where
    drawSubTrees Nil = []
    drawSubTrees (t :& Nil) =
        "|" : shift "`- " "   " (draw t)
    drawSubTrees (t :& ts) =
        "|" : shift "+- " "|  " (draw t) ++ drawSubTrees ts

    shift first other = Data.List.zipWith (++) (first : repeat other)
#endif

-- | 'unrollPQ', given a comparator function, unrolls a 'PQueue' into
-- a sorted list.
unrollPQ :: (e -> e -> Ordering) -> PQueue e -> [e]
unrollPQ cmp = unrollPQ'
  where
    {-# INLINE unrollPQ' #-}
    unrollPQ' (PQueue x ts) = x:mergePQs0 ts
    (<>) = mergePQ cmp
    mergePQs0 Nil = []
    mergePQs0 (t :& Nil) = unrollPQ' t
    mergePQs0 (t1 :& t2 :& ts) = mergePQs (t1 <> t2) ts
    mergePQs t ts = t `seq` case ts of
        Nil             -> unrollPQ' t
        t1 :& Nil       -> unrollPQ' (t <> t1)
        t1 :& t2 :& ts' -> mergePQs (t <> (t1 <> t2)) ts'

-- | 'toPQ', given an ordering function and a mechanism for queueifying
-- elements, converts a 'FingerTree' to a 'PQueue'.
toPQ :: (e -> e -> Ordering) -> (a -> PQueue e) -> FingerTree a -> Maybe (PQueue e)
toPQ _ _ Empty = Nothing
toPQ _ f (Single x) = Just (f x)
toPQ cmp f (Deep _ pr m sf) = Just (maybe (pr' <> sf') ((pr' <> sf') <>) (toPQ cmp fNode m))
  where
    fDigit digit = case fmap f digit of
        One a           -> a
        Two a b         -> a <> b
        Three a b c     -> a <> b <> c
        Four a b c d    -> (a <> b) <> (c <> d)
    (<>) = mergePQ cmp
    fNode = fDigit . nodeToDigit
    pr' = fDigit pr
    sf' = fDigit sf

-- | 'mergePQ' merges two 'PQueue's.
mergePQ :: (a -> a -> Ordering) -> PQueue a -> PQueue a -> PQueue a
mergePQ cmp q1@(PQueue x1 ts1) q2@(PQueue x2 ts2)
  | cmp x1 x2 == GT     = PQueue x2 (q1 :& ts2)
  | otherwise           = PQueue x1 (q2 :& ts1)
