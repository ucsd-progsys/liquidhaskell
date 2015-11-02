
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "totality" @-}

module DataBase (values) where

{-@ values :: forall <range :: key -> val -> Prop>.
  k:key -> [Dict <range> key val]  -> [val<range k>] @-}
values :: key -> [Dict key val]  -> [val]
values k = map go
  where
    go (D _ f) = f k

data Dict key val = D {ddom :: [key], dfun :: key -> val}
{-@ ddom :: forall <range :: key -> val -> Prop>.
           x:Dict <range> key val  -> [key]
  @-}

{-@ dfun :: forall <range :: key -> val -> Prop>.
               x:Dict <range> key val
            -> i:key -> val<range i>
  @-}

{-@ data Dict key val <range :: key -> val -> Prop>
  = D ( ddom :: [key])
      ( dfun :: i:key -> val<range i>)
  @-}
