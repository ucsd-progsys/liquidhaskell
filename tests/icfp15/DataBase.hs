module DataBase  (


  Table, Dict, (+=), P(..), values, empty, 

  emptyTable, singleton, fromList, 



  union, diff, product, project, select,

  ) where

import qualified Data.Set
import Data.Maybe (catMaybes)
import Prelude hiding (product, union, filter)


type Table t v = [Dict t v]



fromList xs = xs

singleton :: Dict key val -> Table key val 
singleton d = [d]



emptyTable :: Table t v 
emptyTable = []

union, diff, product :: (Eq key, Eq val) => Table key val -> Table key val -> Table key val
union xs ys =  xs ++ ys 
diff  xs ys = xs \\ ys  
product xs ys = [ productD x y | x <- xs, y <- ys]


instance (Eq key, Eq val) => Eq (Dict key val) where
  (D ks1 f1) == (D ks2 f2) = all (\k -> k `elem` ks2 && f1 k == f2 k) ks1 


productD :: Eq key => Dict key val -> Dict key val -> Dict key val
productD (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    -- ORDERING IN LETS IS IMPORTANT: ks should be in scope for f
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 


project :: Eq t => [t] -> Table t v -> Table t v
project ks = map (projectD ks)
projectD ks (D _ f) = D ks f


select :: Eq key => (key -> val -> Bool) -> Table key val -> Table key val 
select f = catMaybes . map (selectD f)


selectD :: Eq key => (key -> val -> Bool) -> Dict key val -> Maybe (Dict key val)   
selectD prop x@(D ks f)
  = let g k | k `elem` ks = prop k (f k)
            | otherwise   = True
   in  if all g ks then Just x else Nothing 





data Dict key val = D {dom :: [key], dfun :: key -> val}  
 

instance (Show t, Show v) => Show (Dict t v) where
  show (D ks f) = concatMap (\k -> show k ++ "\t:=\t" ++ show (f k) ++ "\n" ) ks 


values :: key -> [Dict key val]  -> [val]
values k = map go 
  where
    go (D _ f) = f k 


{- empty :: {v:Dict <{\v -> false}, {\k v -> false}> key val | Set_emp (listElts (dom v))} @-}
empty :: Dict key val
empty = D [] (\x -> error "call empty")   -- TODO: replace error with liquidError?


extend :: Eq key => key -> val -> Dict key val -> Dict key val
{- extend :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              k:key<domain> -> val<range k> 
           -> x:Dict <{v:key<domain> | v != k}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (dom v)) = (Set_cup (listElts (dom x)) (Set_sng k))} @-}
extend k v (D ks f) = D (k:ks) (\i -> if i == k then v else f i)



data P k v = k := v
{- data P k v <domain :: k -> Prop, range :: k -> v -> Prop> 
  = (:=) (kkey :: k<domain>) (kval :: v<range kkey>)
  @-}
infixr 3 +=

{- += :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              pp:P <domain, range> key val 
           -> x:Dict <{v:key<domain> | v != (kkey pp)}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (dom v)) = (Set_cup (listElts (dom x)) (Set_sng (kkey pp)))} @-}
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

