module DataBase  where

import qualified Data.Set

data Value = VA | VB | VC | VD

data Tag = TA | TB | TC | TD   
         deriving Eq

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



rab :: Dict Tag Value
{-@ rab :: Dict <{\v -> v = TA || v = TB }, {\i v -> (i == TA => v = VA) && (i == TB => v = VB)} > Tag Value @-}
rab = extend TB VB $ extend TA VA empty

rcd :: Dict Tag Value
{-@ rcd :: Dict <{\v -> v = TC || v = TD }, {\i v -> (i == TC => v = VC) && (i == TD => v = VD)} > Tag Value @-}
rcd = extend TC VC $ extend TD VD empty





-------------------------------------------------------------------------------
-------------------------    HELPERS   ----------------------------------------
-------------------------------------------------------------------------------

{-@ measure tagToInt @-}
tagToInt :: Tag -> Int
tagToInt TA = 1
tagToInt TB = 2
tagToInt TC = 3
tagToInt TD = 4


{-@ measure valToInt @-}
valToInt :: Value -> Int
valToInt VA = 1
valToInt VB = 2
valToInt VC = 3
valToInt VD = 4

{-@ qual :: xs:[a] -> {v: a | Set_mem v (listElts xs)} @-}
qual :: [a] -> a
qual = undefined



{-@ quall :: ww:Tag -> {v:Value | ww == TA => v = VA} @-}
quall :: Tag -> Value
quall = undefined





{-@ liquidError :: {v:String | false} -> a @-}
liquidError :: String -> a
liquidError = error