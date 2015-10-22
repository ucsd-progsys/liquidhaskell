
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "totality" @-}

module DataBase (values) where

import qualified Data.Set as Set

{-@ values :: forall <range :: key -> val -> Prop>.
  k:key -> [{v:Dict <range> key val | Set_mem k (listElts (ddom v))}]  -> [val<range k>] @-}
values :: key -> [Dict key val]  -> [val]
values k = map go
  where
    go (D _ f) = f k

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
