module Fixme where

-- See Note: Order of constructors
data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

type Size     = Int

{-@ data Map [mlen] k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
         = Bin (sz    :: Size) 
               (key   :: k) 
               (value :: a) 
               (left  :: Map <l, r> (k <l key>) a) 
               (right :: Map <l, r> (k <r key>) a) 
         | Tip 
  @-}

{-@ measure mlen :: (Map k a) -> Int
    mlen(Tip) = 0
    mlen(Bin s k v l r) = 1 + (mlen l) + (mlen r)
  @-}

{-@ invariant {v:Map k a | (mlen v) >= 0} @-}

{-@ type OMap k a = Map <{\root v -> v < root}, {\root v -> v > root}> k a @-}

{-@ insert :: (Ord k) => k -> a -> OMap k a -> OMap k a @-}
insert :: Ord k => k -> a -> Map k a -> Map k a
--insert = insert_go
insert = go
  where
    go :: Ord k => k -> a -> Map k a -> Map k a
    --STRICT_1_OF_3(go)
    go kx x Tip = singleton kx x
    go kx x (Bin sz ky y l r) =
        case compare kx ky of
                  -- Bin ky y (go kx x l) r 
            LT -> balanceL ky y (go kx x l) r
            GT -> balanceR ky y l (go kx x r)
            EQ -> Bin sz kx x l r

{-@ balanceL :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceL :: k -> a -> Map k a -> Map k a -> Map k a
balanceL = undefined

{-@ balanceR :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
balanceR :: k -> a -> Map k a -> Map k a -> Map k a
balanceR = undefined

{-@ singleton :: k -> a -> OMap k a @-}
singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip
