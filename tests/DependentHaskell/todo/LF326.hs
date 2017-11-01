#!/usr/bin/env stack
-- stack --resolver lts-9.2 exec liquid --package process --install-ghc

{-@ LIQUID "--higherorder"       @-}
{-@ LIQUID "--exact-data-cons"   @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE GADTs               #-}
module Foo where 

import Prelude hiding (Maybe (..), Either (..))
import System.Process
type Heap = Map Int (Maybe Val)

-- Heap Parital Order:
--------------------------------------------------------------------------------
data HeapLteProp where
  HeapLte :: Heap -> Heap -> HeapLteProp

-- | Partial ordering on the `Heap`. Read as "definedness"
data HeapLte where
  HeapRefl :: Heap -> HeapLte
  HeapTrans :: Heap -> Heap -> Heap
            -> HeapLte -> HeapLte
            -> HeapLte
  HeapAdd :: Heap -> Int -> Maybe Val
          -> HeapLte
{-@ data HeapLte where
    HeapRefl  :: h:Heap -> Prop (HeapLte h h)
  | HeapTrans :: h1:Heap -> h2:Heap -> h3:Heap
              -> Prop (HeapLte h1 h2)
              -> Prop (HeapLte h2 h3)
              -> Prop (HeapLte h1 h3)
  | HeapAdd   :: h:Heap -> k:Int -> val:(Maybe Val)
              -> Prop (HeapLte h (Record k val h))
@-}
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

-- Maybe
--------

{-@ data MyEither a b = Left {selectLeft :: a}  | Right {selectRight :: b}  @-}
data MyEither a b = Left { selectLeft :: a }  | Right { selectRight :: b } 
data Maybe a = Just a | Nothing

{-@ reflect join @-}
join (Just (Just x)) = Just x
join _               = Nothing

{-@ reflect $$ @-}
f $$ x = f x

-- Maps
---------

{-@ data Map [mlen] k v = Empty | Record {mKey :: k, mVal :: v, mRest :: Map k v} @-}
data Map k v = Empty
         | Record k v (Map k v)

{-@ measure mlen @-}
{-@ mlen :: Map k v -> Nat @-}
mlen :: Map k v-> Int
mlen Empty          = 0
mlen (Record k v r) = 1 + mlen r

{-@ reflect update @-}
update :: Map k v -> k -> v -> Map k v
update m k v = Record k v m

{-@ reflect find @-}
find :: Eq k => k -> Map k v -> Maybe v
find key  Empty          = Nothing
find key (Record k v r)
  | k == key            = Just v
  | otherwise           = find key r

{-@ reflect delete @-}
delete :: Eq k => k -> Map k v -> Map k v
delete key Empty          = Empty
delete key (Record k v r)
  | k == key            = delete key r
  | otherwise           = Record k v (delete key r)

{-@ reflect insertWith @-}
insertWith :: Eq k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith _ _ _ Empty  = Empty
insertWith f key val (Record k v r)
  | k == key            = Record k (f v val) r
  | otherwise           = Record k v (insertWith f key val r)

-- List
--------

{-@ reflect app @-}
app :: [a] -> [a] -> [a]
app (x:xs) ys = x:(app xs ys)
app [] ys     = ys

{-@ reflect fmapList @-}
fmapList :: (a -> b) -> [a] -> [b]
fmapList f (x:xs) = f x : fmapList f xs
fmapList _ [] = []

-- step
--------------------------------------------------------------------------------
type Val = Double -- Int

data IVar a = IVar Int

data Trace = Get (IVar Val) (Val -> Trace)
           | Put (IVar Val) Val Trace
           | New (IVar Val -> Trace)
           | Fork Trace Trace
           | Done

data Exn = MultiplePut Val Int Val
         | Deadlock (Map Int [Val -> Trace])
         | HeapExn

instance Eq Exn where
  MultiplePut _ _ _ == MultiplePut _ _ _ = True
  Deadlock _ == Deadlock _ = True
  HeapExn == HeapExn = True
  _ == _ = False

{-@ reflect step @-}
step :: (Trace, [Trace]) -> Map Int [Val -> Trace] -> Int -> Heap
     -> MyEither Exn ([Trace], Map Int [Val -> Trace], Int,  Heap)
step (trc, others) blkd cntr heap =
  case trc of
    Done            -> Right (others, blkd, cntr, heap)
    Fork t1 t2      -> Right (t1 : t2 : others, blkd, cntr, heap)
    New k           -> Right (k (IVar cntr) : others, blkd, cntr + 1, Record cntr Nothing heap)
    Get (IVar ix) k -> case join (find ix heap) of
                         Nothing -> Right (others, insertWith app ix [k] blkd, cntr, heap)
                         Just v  -> Right (k v : others, blkd, cntr, heap)
    Put (IVar ix) v t2 -> let heap' = Record ix (Just v) heap in
                          case join (find ix heap) of
                            Just v0 -> Left (MultiplePut v ix v0)
                            Nothing -> case find ix blkd of
                              Nothing -> Right (t2 : others, blkd, cntr, heap')
                              Just ls -> Right (t2 : app ( fmapList ($$ v) ls ) others, delete ix blkd, cntr, heap')

-- Theorems
-------------

{-@ reflect select4of4 @-}
select4of4 (_,_,_,h) = h


{-@ theoremMonotonic :: a:(Trace,[Trace]) -> b:( Map Int [Val -> Trace]) -> c:Int -> h:Heap
                     -> h':{v:Heap | v = select4of4 (selectRight (step a b c h))}
                     -> Prop ( HeapLte h h' )
  @-}
theoremMonotonic :: (Trace, [Trace]) ->  Map Int [Val -> Trace] -> Int -> Heap -> Heap -> ()
theoremMonotonic x y = undefined
