module DataBase  (


  Table, Dict, (+=), P(..), values, empty, 

  emptyTable, singleton, fromList, 

  union, diff, product, project, select,

  ) where

import qualified Data.Set
-- import Data.Maybe (catMaybes)
import Prelude hiding (product, union, filter)
{-@ LIQUID "--no-termination" @-}

type Table t v = [Dict t v]

data Dict key val = D {ddom :: [key], dfun :: key -> val}  
{-@ ddom :: forall <domain :: key -> Prop, range :: key -> val -> Prop>. 
           x:Dict <domain, range> key val  -> {v:[key<domain>] | v = ddom x}
  @-}

{-@ dfun :: forall <domain :: key -> Prop, range :: key -> val -> Prop>. 
               x:Dict <domain, range> key val  
            -> i:{v:key | Set_mem v (listElts (ddom x))} -> val<range i> 
  @-}

{-@ data Dict key val <domain :: key -> Prop, range :: key -> val -> Prop>
  = D ( ddom :: [key<domain>])
      ( dfun :: i:{v:key | Set_mem v (listElts ddom)} -> val<range i>)     
  @-} 


instance (Show t, Show v, Eq t) => Show (Dict t v) where
  show (D ks f) = let f k = show k ++ "\t:=\t" ++ show (f k) ++ "\n" 
                  in concatMap f ks 


{-@ fromList :: forall <dom :: key -> Prop, range :: key -> val -> Prop>. 
                [Dict <dom, range> key val] -> [Dict <dom, range> key val]
  @-} 
fromList :: [Dict key val] -> Table key val 
fromList xs = xs

{-@ singleton :: forall <dom :: key -> Prop, range :: key -> val -> Prop>. 
                 Dict <dom, range> key val -> [Dict <dom, range> key val]
  @-} 
singleton :: Dict key val -> Table key val 
singleton d = [d]


{-@ emptyTable :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
                   [Dict <domain, range> key val]
  @-}
emptyTable :: Table t v 
emptyTable = []

{-@ union :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
             x:[Dict <domain, range> key val]  
          -> y:[Dict <domain, range> key val]
          -> {v:[Dict <domain, range> key val] | listElts v = Set_cup (listElts x) (listElts y)}
  @-}
{-@ diff :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
             x:[Dict <domain, range> key val]  
          -> y:[Dict <domain, range> key val]
          -> {v:[Dict <domain, range> key val] | listElts v = Set_dif (listElts x) (listElts y)}
  @-}
union, diff :: (Eq key, Eq val) => Table key val -> Table key val -> Table key val
union xs ys = xs ++ ys 
diff  xs ys = xs \\ ys  

{-@ product :: forall <domain1 :: key -> Prop, 
                       domain2 :: key -> Prop,
                       domain  :: key -> Prop,
                       range1  :: key -> val -> Prop,
                       range2  :: key -> val -> Prop,
                       range   :: key -> val -> Prop>.
                       {key<domain1> <: key<domain>}
                       {key<domain2> <: key<domain>}
                       {k1:: key<domain1>, k2::key<domain2> |- {v:key | v = k1 && v = k2} <: {v:key | false}}
                       {k::key<domain1> |- val<range1 k> <: val<range k> }
                       {k::key<domain2> |- val<range2 k> <: val<range k> }
               [Dict <domain1, range1> key val] 
            -> [Dict <domain2, range2> key val] 
            -> [Dict <domain,  range > key val] 
  @-}

product :: (Eq key, Eq val) => Table key val -> Table key val -> Table key val
product xs ys = [ productD x y | x <- xs, y <- ys]


instance (Eq key, Eq val) => Eq (Dict key val) where
  (D ks1 f1) == (D ks2 f2) = all (\k -> k `elem` ks2 && f1 k == f2 k) ks1 

{-@ productD :: forall <domain1 :: key -> Prop, 
                       domain2 :: key -> Prop,
                       domain  :: key -> Prop,
                       range1  :: key -> val -> Prop,
                       range2  :: key -> val -> Prop,
                       range   :: key -> val -> Prop>.
                       {key<domain1> <: key<domain>}
                       {key<domain2> <: key<domain>}
                       {k1:: key<domain1>, k2::key<domain2> |- {v:key | v = k1 && v = k2} <: {v:key | false}}
                       {k::key<domain1> |- val<range1 k> <: val<range k> }
                       {k::key<domain2> |- val<range2 k> <: val<range k> }
               Dict <domain1, range1> key val 
            -> Dict <domain2, range2> key val 
            -> Dict <domain,  range > key val 
  @-}

productD :: Eq key => Dict key val -> Dict key val -> Dict key val
productD (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    -- ORDERING IN LETS IS IMPORTANT: ks should be in scope for f
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 

{-@ project :: forall <domain :: key -> Prop, 
                       domain1 :: key -> Prop, 
                       range :: key -> val -> Prop>.
                      {key<domain> <: key<domain1>}
               keys:[key<domain>] 
            -> [{v:Dict <domain1, range> key val | (Set_sub (listElts keys) (listElts (ddom v)))}] 
            -> [{v:Dict <domain, range> key val  | (listElts (ddom v)) = listElts keys}]
   @-}
project :: Eq t => [t] -> Table t v -> Table t v
project ks [] = []
project ks (x:xs) = projectD ks x : project ks xs


{-@ projectD :: forall <domain :: key -> Prop, 
                       domain1 :: key -> Prop, 
                       range :: key -> val -> Prop>.
                      {key<domain> <: key<domain1>}
               keys:[key<domain>] 
            -> {v:Dict <domain1, range> key val | (Set_sub (listElts keys) (listElts (ddom v)))} 
            -> {v:Dict <domain, range> key val  | (listElts (ddom v)) = listElts keys}
   @-}
projectD ks (D _ f) = D ks f


{-@ select :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              (key -> val -> Bool)
          -> x:[Dict <domain, range> key val]  
          -> {v:[Dict <domain, range> key val] | Set_sub (listElts x) (listElts v)}
  @-}
select :: Eq key => (key -> val -> Bool) -> Table key val -> Table key val 
select f = catMaybes . map (selectD f) 
  where
    catMaybes [] = []
    catMaybes (Nothing:xs) = catMaybes xs
    catMaybes (Just x : xs) = x:catMaybes xs

{-@ selectD :: forall<domain :: key -> Prop, range :: key -> val -> Prop>.
              (k:key -> v:val<range k> -> Bool) 
           -> x:Dict <domain, range> key val
           -> Maybe ({v:Dict<domain, range> key val | v = x})
  @-}

selectD :: Eq key => (key -> val -> Bool) -> Dict key val -> Maybe (Dict key val)   
selectD prop x@(D ks f)
  = let g k | k `elem` ks = prop k (f k)
            | otherwise   = True
   in  if all g ks then Just x else Nothing 


{-@ values :: forall <dom:: key -> Prop, range :: key -> val -> Prop>. 
  k:key<dom> -> [{v:Dict <dom, range> key val | Set_mem k (listElts (ddom v))}]  -> [val<range k>] @-}
values :: key -> [Dict key val]  -> [val]
values k = map go 
  where
    go (D _ f) = f k 


{-@ empty :: {v:Dict <{\v -> false}, {\k v -> false}> key val | Set_emp (listElts (ddom v))} @-}
empty :: Dict key val
empty = D [] (\x -> error "call empty")   -- TODO: replace error with liquidError?


extend :: Eq key => key -> val -> Dict key val -> Dict key val
{-@ extend :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              k:key<domain> -> val<range k> 
           -> x:Dict <{v:key<domain> | v != k}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (ddom v)) = (Set_cup (listElts (ddom x)) (Set_sng k))} @-}
extend k v (D ks f) = D (k:ks) (\i -> if i == k then v else f i)



data P k v = k := v
{-@ data P k v <domain :: k -> Prop, range :: k -> v -> Prop> 
  = (:=) (kkey :: k<domain>) (kval :: v<range kkey>)
  @-}
infixr 3 +=

{-@ += :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              pp:P <domain, range> key val 
           -> x:Dict <{v:key<domain> | v != (kkey pp)}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (ddom v)) = (Set_cup (listElts (ddom x)) (Set_sng (kkey pp)))} @-}
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
{-@ filter :: xs:[a] -> ({v:a | Set_mem v (listElts xs)} -> Bool) -> {v:[a] | Set_sub (listElts v) (listElts xs)} @-}
filter :: [a] -> (a -> Bool) -> [a]
filter [] _   = []
filter (x:xs) f 
  | f x       = x : filter xs f 
  | otherwise = filter xs f  


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

