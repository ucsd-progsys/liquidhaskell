{-@ LIQUID "--exact-data-cons"   @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
module Foo where
import Prelude hiding (Maybe (..))

-- Heap Parital Order:
--------------------------------------------------------------------------------
type Heap = Map Int (Maybe Double)
data HeapLteProp = HeapLte Heap Heap

-- Maybe
--------
data Maybe a = Just a | Nothing
{-@ reflect join @-}
join (Just (Just x)) = Just x
join _               = Nothing

-- Maps
---------
data Map k v = Empty
         | Record k v (Map k v)
{-@ reflect find @-}
find :: Eq k => k -> Map k v -> Maybe v
find key  Empty          = Nothing
find key (Record k v r)
  | k == key            = Just v
  | otherwise           = find key r

-- step
--------------------------------------------------------------------------------
{-@ reflect step @-}
step :: Int -> Heap -> Heap
step cntr heap = myconst heap (join (find cntr heap))
{-@ reflect myconst @-}
myconst a b = a

-- Theorems
-------------
{-@ measure prop :: a -> b           @-}
{-@ theoremMonotonic :: c:Int -> h:Heap
                     -> h':{v:Heap | v = step c h}
                     -> {v:_ | prop v = ( HeapLte h h' ) }
  @-}
theoremMonotonic :: Int -> Heap -> Heap -> ()
theoremMonotonic = undefined
