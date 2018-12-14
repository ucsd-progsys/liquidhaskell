module Language.Fixpoint.Utils.Trie 
  ( -- * Datatype
    Trie (..)
  , Branch (..)

    -- * Constructors
  , empty
  , insert
  , fromList

    -- * Visitors 
  , fold 
  , foldM
  ) 
  where 

import qualified Data.List as L 

type Key  = Int
type Path = [Key]

data Trie a 
  = Node ![Branch a]
  deriving (Eq, Show)

data Branch a 
  = Bind !Key !(Trie a)
  | Val a 
  deriving (Eq, Show)

-------------------------------------------------------------------------------
empty :: Trie a 
-------------------------------------------------------------------------------
empty = Node []

-------------------------------------------------------------------------------
insert :: Path -> a -> Trie a -> Trie a 
-------------------------------------------------------------------------------
insert []     v (Node ts) = Node ((Val v) : ts) 
insert (i:is) v (Node ts) = Node (insertKey i is v ts)


-------------------------------------------------------------------------------
fromList :: [(Path, a)] -> Trie a 
-------------------------------------------------------------------------------
fromList = L.foldl' (\t (k, v) -> insert k v t) empty 

-- i=3 
-- 0 1 2 3 4 5 6 
  
insertKey :: Key -> Path -> a -> [Branch a] -> [Branch a]
insertKey i is v bs@((Bind j tj) : bs') 
  | i == j              = Bind i (insert is v tj) : bs' 
  | i <  j              = Bind i (pathTrie is v)  : bs 
insertKey i is v (b:bs) = b : insertKey i is v bs 
insertKey i is v []     = [ Bind i (pathTrie is v) ] 

pathTrie :: Path -> a -> Trie a 
pathTrie []     v = Node [Val v] 
pathTrie (i:is) v = Node [Bind i (pathTrie is v)]

-------------------------------------------------------------------------------
fold :: (acc -> Path -> a -> acc) -> acc -> Trie a -> acc 
-------------------------------------------------------------------------------
fold = undefined

-------------------------------------------------------------------------------
foldM :: (Monad m) => (acc -> Path -> a -> m acc) -> acc -> Trie a -> m acc 
-------------------------------------------------------------------------------
foldM = undefined

{- 

     e1
        <----
 === e2
        <----
 === e3
        <----
   ? e4
..

 -}

-------------------------------------------------------------------------------
-- | Examples
-------------------------------------------------------------------------------
{-
Lets represent

    1,2,3,Z ->
    1,2,3,4 -> A
    1,2,3,5 -> B
    1,6     -> C

    insert [1, 2]    "A"
  . insert [1,2,3,4] "B"
  . insert [1,2,3,5] "C"
  . insert [1,6]     "D"
  $ empty

as the `trie`

     1 -> 2 -----------> A 
           `-> 3 -> 4 -> B
     |         ` -> 5 -> C
     `-> 6 ------------> D

-}

-- >>> _example0 == _example1 
-- True

_example0 :: Trie Char
_example0 = Node [Bind 1 n1]
  where
    n1   = Node [Bind 2 n2, Bind 6 n6]
    n2   = Node [Val 'A'  , Bind 3 n3]
    n3   = Node [Bind 4 n4, Bind 5 n5]
    n4   = Node [Val 'B']
    n5   = Node [Val 'C']
    n6   = Node [Val 'D'] 


_example1 :: Trie Char
_example1 = insert [1, 2]    'A'
         . insert [1,2,3,4] 'B'
         . insert [1,2,3,5] 'C'
         . insert [1,6]     'D'
         $ empty
