module DataBase  (


  Table, Dict(..), (+=), P(..), values, empty, 

  emptyTable, singleton, fromList, 

  union, diff, product, project, select, productD

  ) where

import qualified Data.Set as Set 
import Prelude hiding (product, union, filter)
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "totality" @-}

type Table t v = [Dict t v]

data Dict key val = D {ddom :: [key], dfun :: key -> val}  
{-@ ddom :: forall <range :: key -> val -> Prop>. 
           x:Dict <range> key val  -> {v:[key] | v = ddom x}
  @-}

{-@ dfun :: forall <range :: key -> val -> Prop>. 
               x:Dict <range> key val  
            -> i:{v:key | Set_mem v (listElts (ddom x))} -> val<range i> 
  @-}

{-@ data Dict key val <range :: key -> val -> Prop>
  = D ( ddom :: [key])
      ( dfun :: i:{v:key | Set_mem v (listElts ddom)} -> val<range i>)     
  @-} 


instance (Show t, Show v, Eq t) => Show (Dict t v) where
  show (D ks f) = let g k = show k ++ "\t:=\t" ++ show (f k) ++ "\n" 
                  in concatMap g ks 


-- LIQUID : This discards the refinement of the Dict 
-- for example the ddom

{-@ fromList :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>. 
                x:[Dict <range> key val <<p>>] -> {v:[Dict <range> key val <<p>>] | x = v}
  @-} 
fromList :: [Dict key val] -> Table key val 
fromList xs = xs

{-@ singleton :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>. 
                 Dict <range> key val <<p>> -> [Dict <range> key val <<p>>]
  @-} 
singleton :: Dict key val -> Table key val 
singleton d = [d]


{-@ emptyTable :: forall <range :: key -> val -> Prop>.
                   [Dict <range> key val]
  @-}
emptyTable :: Table t v 
emptyTable = []

{-@ union :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>.
              x:[Dict <range> key val <<p>>]  
          ->  y:[Dict <range> key val <<p>>]
          -> {v:[Dict <range> key val <<p>>] | listElts v = Set_cup (listElts x) (listElts y)}
  @-}
{-@ diff :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>.
              x:[Dict <range> key val <<p>>]  
          ->  y:[Dict <range> key val <<p>>]
          -> {v:[Dict <range> key val <<p>>] | listElts v = Set_dif (listElts x) (listElts y)}
  @-}
union, diff :: (Eq key, Eq val) => Table key val -> Table key val -> Table key val
union xs ys = xs ++ ys 
diff  xs ys = xs \\ ys  

{-@ predicate Append XS YS V = 
  ((listElts (ddom v)) = Set_cup (listElts (ddom YS)) (listElts (ddom XS)) ) 
  @-}


{-@ product :: forall <range1  :: key -> val -> Prop,
                       range2  :: key -> val -> Prop,
                       range   :: key -> val -> Prop, 
                       p :: Dict key val -> Prop, 
                       q :: Dict key val -> Prop, 
                       r :: Dict key val -> Prop>.
                       {x::Dict key val <<p>>, y :: Dict key val <<q>> |- {v:Set.Set key |  v = Set_cap (listElts (ddom x)) (listElts (ddom y))}  <: {v:Set.Set key | Set_emp v }}
                       {x::Dict key val <<p>>, y :: Dict key val <<q>> |-  {v:Dict key val | Append x y v} <: Dict key val <<r>>}
                       {x::Dict key val <<p>>, k::{v:key | Set_mem v (listElts (ddom x))} |- val<range1 k> <: val<range k> }
                       {x::Dict key val <<q>>, k::{v:key | Set_mem v (listElts (ddom x))} |- val<range2 k> <: val<range k> }
               xs:[Dict <range1> key val <<p>>] 
            -> ys:[Dict <range2> key val <<q>>] 
            ->    [Dict <range > key val <<r>>] 
  @-}

product :: (Eq key, Eq val) => Table key val -> Table key val -> Table key val
product xs ys = go xs ys 
  where 
    go []     _  = []
    go (x:xs) [] = go xs ys
    go (x:xs) (y:ys) = productD x y : go (x:xs) ys 

instance (Eq key, Eq val) => Eq (Dict key val) where
  (D ks1 f1) == (D ks2 f2) = all (\k -> k `elem` ks2 && f1 k == f2 k) ks1 

{-@ productD :: forall <range1  :: key -> val -> Prop,
                       range2  :: key -> val -> Prop,
                       range   :: key -> val -> Prop, 
                       p :: Dict key val -> Prop, 
                       q :: Dict key val -> Prop>.
                       {x::Dict key val <<p>>, y :: Dict key val <<q>> |- {v:Set.Set key |  v = Set_cap (listElts (ddom x)) (listElts (ddom y))}  <: {v:Set.Set key | Set_emp v }}
                       {x::Dict key val <<p>>, k::{v:key | Set_mem v (listElts (ddom x))} |- val<range1 k> <: val<range k> }
                       {x::Dict key val <<q>>, k::{v:key | Set_mem v (listElts (ddom x))}|- val<range2 k> <: val<range k> }
               x:Dict <range1> key val <<p>>
            -> y:Dict <range2> key val <<q>> 
            -> {v:Dict <range> key val | (listElts (ddom v)) = Set_cup (listElts (ddom x)) (listElts (ddom y))} 
  @-}

productD :: Eq key => Dict key val -> Dict key val -> Dict key val
productD (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    -- ORDERING IN LETS IS IMPORTANT: ks should be in scope for f
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 


{-@ project :: forall <range :: key -> val -> Prop>.
               keys:[key] 
            -> [{v:Dict <range> key val | (Set_sub (listElts keys) (listElts (ddom v)))}] 
            -> [{v:Dict <range> key val  | (listElts (ddom v)) = listElts keys}]
   @-}
project :: Eq t => [t] -> Table t v -> Table t v
project ks [] = []
project ks (x:xs) = projectD ks x : project ks xs


{-@ projectD :: forall <range :: key -> val -> Prop>.
               keys:[key] 
            -> {v:Dict <range> key val | (Set_sub (listElts keys) (listElts (ddom v)))} 
            -> {v:Dict <range> key val  | (listElts (ddom v)) = listElts keys}
   @-}
projectD ks (D _ f) = D ks f

{-@ select :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>.
              (Dict <range> key val <<p>>  -> Bool)
          -> x:[Dict <range> key val <<p>>]  
          -> {v:[Dict <range> key val <<p>>] | Set_sub (listElts v) (listElts x)}
  @-}
select :: (Dict key val -> Bool) -> Table key val -> Table key val 
select prop xs = filter prop xs 

{-@ values :: forall <range :: key -> val -> Prop>. 
  k:key -> [{v:Dict <range> key val | Set_mem k (listElts (ddom v))}]  -> [val<range k>] @-}
values :: key -> [Dict key val]  -> [val]
values k = map go 
  where
    go (D _ f) = f k 


{-@ empty :: {v:Dict <{\k v -> false}> key val | Set_emp (listElts (ddom v))} @-}
empty :: Dict key val
empty = D [] (\x -> liquidError "call empty")   -- TODO: replace error with liquidError?


extend :: Eq key => key -> val -> Dict key val -> Dict key val
{-@ extend :: forall <range :: key -> val -> Prop>.
              k:key-> val<range k> 
           -> x:Dict <range> key val 
           -> {v:Dict <range> key val | (listElts (ddom v)) = (Set_cup (listElts (ddom x)) (Set_sng k))} @-}
extend k v (D ks f) = D (k:ks) (\i -> if i == k then v else f i)



data P k v = k := v
{-@ data P k v <range :: k -> v -> Prop> 
  = (:=) (kkey :: k) (kval :: v<range kkey>)
  @-}
infixr 3 +=

{-@ += :: forall <range :: key -> val -> Prop>.
              pp:P <range> key val 
           -> x:Dict <range> key val 
           -> {v:Dict <range> key val | (listElts (ddom v)) = (Set_cup (listElts (ddom x)) (Set_sng (kkey pp)))} @-}
(+=) :: Eq key => P key val -> Dict key val -> Dict key val

(t := v) += c = extend t v c




-------------------------------------------------------------------------------
-------------------------    HELPERS   ----------------------------------------
-------------------------------------------------------------------------------

{-@ ensuredomain :: forall <p ::a -> Prop>. Eq a => xs:[a<p>] -> x:{v:a | Set_mem v (listElts xs)} -> {v:a<p> | Set_mem v (listElts xs) && v = x} @-}
ensuredomain :: Eq a => [a] -> a -> a
ensuredomain (y:ys) x | x == y    = y 
                      | otherwise = ensuredomain ys x  
ensuredomain _ _                  = liquidError "ensuredomain on empty list"


-- | List functions

{-@ (\\) :: forall<p :: a -> Prop>. xs:[a<p>] -> ys:[a] -> {v:[a<p>] | (listElts v)  = (Set_dif (listElts xs) (listElts ys))} @-}
(\\) :: Eq a => [a] -> [a] -> [a]
[]     \\ _ = []
(x:xs) \\ ys = if x `elem` ys then xs \\ ys else x:(xs \\ ys)


{-@ assume (Prelude.++) :: xs:[a] -> ys:[a] -> {v:[a] | listElts v = Set_cup (listElts xs) (listElts ys)} @-}

{-@ assume Prelude.elem :: x:a -> xs:[a] -> {v:Bool | Prop v <=> Set_mem x (listElts xs)} @-}
{-@ filter :: (a -> Bool) -> xs:[a] -> {v:[a] | Set_sub (listElts v) (listElts xs)} @-}
filter :: (a -> Bool) -> [a] -> [a]
filter _ []   = []
filter f (x:xs) 
  | f x       = x : filter f xs 
  | otherwise = filter f xs


liquidError :: String -> a
{-@ liquidError :: {v:String | false} -> a @-}
liquidError = error


{-@ qual :: xs:[a] -> {v: a | Set_mem v (listElts xs)} @-}
qual :: [a] -> a
qual = undefined

{-@ qual' :: forall <range :: key -> val -> Prop>. k:key -> val<range k> @-}
qual' :: key -> val
qual' = undefined

{-@ qual1 :: ks:[key] -> {v:Dict key val | (listElts (ddom v)) = listElts ks} @-}
qual1 :: [key] -> Dict key val 
qual1 = undefined

