module DataBase  (

  Dict, empty, extend, 

  union, diff, product, project, select,

  P(..), (+=)

  ) where

import qualified Data.Set

import Prelude hiding (product, union, filter)


data Dict key val = D {dom :: [key], dfun :: key -> val}  
 

instance (Show t, Show v) => Show (Dict t v) where
  show (D ks f) = concatMap (\k -> show k ++ "\t:=\t" ++ show (f k) ++ "\n" ) ks 


{-@ dom :: forall <domain :: key -> Prop, range :: key -> val -> Prop>. 
           x:Dict <domain, range> key val  -> {v:[key<domain>] | v = dom x}
  @-}

{-@ dfun :: forall <domain :: key -> Prop, range :: key -> val -> Prop>. 
               x:Dict <domain, range> key val  
            -> i:{v:key | Set_mem v (listElts (dom x))} -> val<range i> 
  @-}

{-@ data Dict key val <domain :: key -> Prop, range :: key -> val -> Prop>
  = D ( dom  :: [key<domain>])
      ( dfun :: i:{v:key | Set_mem v (listElts dom)} -> val<range i>)     
  @-} 

{-@ empty :: {v:Dict <{\v -> false}, {\k v -> false}> key val | Set_emp (listElts (dom v))} @-}
empty :: Dict key val
empty = D [] (\x -> error "call empty")   -- TODO: replace error with liquidError?


extend :: Eq key => key -> val -> Dict key val -> Dict key val
{-@ extend :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              k:key<domain> -> val<range k> 
           -> x:Dict <{v:key<domain> | v != k}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (dom v)) = (Set_cup (listElts (dom x)) (Set_sng k))} @-}
extend k v (D ks f) = D (k:ks) (\i -> if i == k then v else f i)



data P k v = k := v
{-@ data P k v <domain :: k -> Prop, range :: k -> v -> Prop> 
  = (:=) (kkey :: k<domain>) (kval :: v<range kkey>)
  @-}
infixr 3 +=

{-@ += :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              pp:P <domain, range> key val 
           -> x:Dict <{v:key<domain> | v != (kkey pp)}, range> key val 
           -> {v:Dict <domain, range> key val | (listElts (dom v)) = (Set_cup (listElts (dom x)) (Set_sng (kkey pp)))} @-}
(+=) :: Eq key => P key val -> Dict key val -> Dict key val

(t := v) += c = extend t v c



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
               Dict <domain1, range1> key val 
            -> Dict <domain2, range2> key val 
            -> Dict <domain,  range > key val 
  @-}
product :: Eq key => Dict key val -> Dict key val -> Dict key val
product (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    -- ORDERING IN LETS IS IMPORTANT: ks should be in scope for f
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 

{-@ union :: forall <domain1 :: key -> Prop, 
                       domain2 :: key -> Prop,
                       domain  :: key -> Prop,
                       range1  :: key -> val -> Prop,
                       range2  :: key -> val -> Prop,
                       range   :: key -> val -> Prop>.
                       {key<domain1> <: key<domain>}
                       {key<domain2> <: key<domain>}
                       {k::key<domain1> |- val<range1 k> <: val<range k> }
                       {k::key<domain2> |- val<range2 k> <: val<range k> }
               x1:Dict <domain1, range1> key val 
            -> x2:Dict <domain2, range2> key val 
            -> {v:Dict <domain,  range > key val | (listElts (dom v)) = Set_cup (listElts (dom x1)) (listElts (dom x2))} 
  @-}
union :: Eq key => Dict key val -> Dict key val -> Dict key val
union (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 


{-@ diff :: forall<domain1 :: key -> Prop, domain :: key -> Prop, range :: key -> val -> Prop>.
            {key<domain1> <: key<domain>} 
            xs:Dict <domain1, range> key val 
         -> ys:Dict <{\k -> true}, {\k v -> true}> key val 
         -> {v:Dict <domain, range> key val | (listElts (dom v)) = (Set_dif (listElts (dom xs)) (listElts (dom ys)))}
  @-}
diff :: Eq key => Dict key val -> Dict key val -> Dict key val
diff (D ks1 f1) (D ks2 _)
  = let ks = ks1 \\ ks2 in D ks f1


{-@ project :: forall <domain :: key -> Prop, 
                       domain1 :: key -> Prop, 
                       range :: key -> val -> Prop>.
                      {key<domain> <: key<domain1>}
               keys:[key<domain>] 
            -> {v:Dict <domain1, range> key val | (Set_sub (listElts keys) (listElts (dom v)))} 
            -> {v:Dict <domain, range> key val  | (listElts (dom v)) = listElts keys}
   @-}
project :: Eq key => [key] -> Dict key val -> Dict key val
project ks (D ks' f') = D ks f'

{-@ select0 :: forall <domain :: key -> Prop, 
                       range  :: key -> val -> Prop, 
                       range1 :: key -> Maybe val -> Prop>.
              (k:key -> v:val<range k> -> Bool) 
            -> x:Dict <domain, range> key val 
            -> {v:Dict <domain, range> key val| Set_sub (listElts (dom v)) (listElts (dom x))}
  @-}

select0 :: (key -> val -> Bool) -> Dict key val -> Dict key val
select0 prop (D ks f) 
  = let ks' = filter ks (\k -> prop k (f k)) in D ks' f

{-@ select :: forall<domain :: key -> Prop, range :: key -> val -> Prop>.
              (k:key -> v:val<range k> -> Bool) 
           -> x:Dict <domain, range> key val
           -> Maybe ({v:Dict<domain, range> key val | v = x})

  @-}
select :: Eq key => (key -> val -> Bool) -> Dict key val -> Maybe (Dict key val)   
select prop x@(D ks f)
  = let g k | k `elem` ks = prop k (f k)
            | otherwise   = False
   in  if any g ks then Just x else Nothing 


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
