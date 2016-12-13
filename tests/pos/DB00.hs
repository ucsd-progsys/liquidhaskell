
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "totality" @-}

module DataBase (values) where

{-@ values :: forall <rr2 :: key -> val -> Bool>.
  k:key -> [Dict <rr2> key val]  -> [val<rr2 k>] @-}
values :: key -> [Dict key val]  -> [val]
values k = map (go k)
  where
    {-@ go :: forall <rr1 :: k -> v -> Bool>. 
              i:k -> Dict <rr1> k v -> v<rr1 i>  @-}
    go k (D _ f) = f k

data Dict key val = D {ddom :: [key], dfun :: key -> val}

{-@ data Dict key val <rr :: key -> val -> Bool>
  = D ( ddom :: [key])
      ( dfun :: i:key -> val<rr i>)
  @-}
