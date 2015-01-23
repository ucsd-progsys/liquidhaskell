module DataBase  (

  Dict, empty, extend, 

  {-@ product :: forall <domain1 :: key -> Prop, 
                         domain2 :: key -> Prop,
                         domain  :: key -> Prop,
                         range1  :: key -> val -> Prop,
                         range2  :: key -> val -> Prop,
                         range   :: key -> val -> Prop>.
                         {key<domain1> -> key<domain>}
                         {key<domain2> -> key<domain>}
                         {k1: key<domain1> -> k2:key<domain2> -> {v:key | v = k1 && v = k2} -> {v:key | false}}
                         {k:key<domain1> -> val<range1 k> -> val<range k> }
                         {k:key<domain2> -> val<range2 k> -> val<range k> }
               Dict <domain1, range1> key val 
            -> Dict <domain2, range2> key val 
            -> Dict <domain,  range > key val 
  @-}
  product, 

  ) where

import qualified Data.Set

import Prelude hiding (product)


data Dict key val = D {dom :: [key], dfun :: key -> val}  
 
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

{-@ empty :: Dict <{\v -> false}, {\k v -> false}> key val @-}
empty :: Dict key val
empty = D [] (\x -> error "call empty")   -- TODO: replace error with liquidError?


extend :: Eq key => key -> val -> Dict key val -> Dict key val
{-@ extend :: forall <domain :: key -> Prop, range :: key -> val -> Prop>.
              k:key<domain> -> val<range k> 
           -> Dict <{v:key<domain> | v != k}, range> key val 
           -> Dict <domain, range> key val @-}
extend k v (D ks f) = D (k:ks) (\i -> if i == k then v else f i)


{-@ assume (Prelude.++) :: xs:[a] -> ys:[a] -> {v:[a] | listElts v = Set_cup (listElts xs) (listElts ys)} @-}

{-@ assume Prelude.elem :: x:a -> xs:[a] -> {v:Bool | Prop v <=> Set_mem x (listElts xs)} @-}


product :: Eq key => Dict key val -> Dict key val -> Dict key val
product (D ks1 f1) (D ks2 f2) 
  = let ks = ks1 ++ ks2 in 
    -- ORDERING IN LETS IS IMPORTANT: ks should be in scope for f
    let f i = if i `elem` ks1 then f1 (ensuredomain ks1 i) else f2 (ensuredomain ks2 i) in
    D ks f 


{-@ ensuredomain :: forall <p ::a -> Prop>. Eq a => xs:[a<p>] -> x:{v:a | Set_mem v (listElts xs)} -> {v:a<p> | Set_mem v (listElts xs) && v = x} @-}
ensuredomain :: Eq a => [a] -> a -> a
ensuredomain (y:ys) x | x == y    = y 
                      | otherwise = ensuredomain ys x  


-------------------------------------------------------------------------------
-------------------------    HELPERS   ----------------------------------------
-------------------------------------------------------------------------------



{-@ qual :: xs:[a] -> {v: a | Set_mem v (listElts xs)} @-}
qual :: [a] -> a
qual = undefined

{-@ qual' :: forall <range :: key -> val -> Prop>. k:key -> val<range k> @-}
qual' :: key -> val
qual' = undefined
