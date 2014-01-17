module Data.Map.Base (Map(..), isRoot, filterLt, filterGt) where

data Map k a  = Bin Size k a (Map k a) (Map k a)
              | Tip

type Size     = Int

data MaybeS a = NothingS | JustS !a

{-@ 
  data Map [mlen] k a <l :: root:k -> k -> Prop, r :: root:k -> k -> Prop>
       = Bin (sz    :: Size) 
             (key   :: k) 
             (value :: a) 
             (left  :: Map <l, r> (k <l key>) a) 
             (right :: Map <l, r> (k <r key>) a) 
       | Tip 
  @-}

{-@ measure mlen :: (Map k a) -> Int 
    mlen(Tip)           = 0
    mlen(Bin s k v l r) = 1 + (mlen l) + (mlen r) 
  @-}

{-@ invariant {v:Map k a | (mlen v) >=0} @-}

{-@ measure isJustS :: forall a. MaybeS a -> Prop 
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
  @-}

{-@ measure fromJustS :: forall a. MaybeS a -> a 
    fromJustS (JustS x) = x 
  @-}

{-@ type OMap k a = Map <{\root v -> v < root}, {\root v -> v > root}> k a @-}

{-@ measure isBin :: Map k a -> Prop
    isBin (Bin sz kx x l r) = true
    isBin (Tip)             = false
  @-}

{-@ measure key :: Map k a -> k 
    key (Bin sz kx x l r) = kx 
  @-}

{-@ isRoot :: t:Map k a -> {v: Bool | (Prop(v) <=> isBin(t))} @-}
isRoot (Bin _ _ _ _ _) = True
isRoot (Tip)           = False

{-@ filterGt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v > fromJustS(x))) } v @-}
filterGt :: Ord k => MaybeS k -> Map k v -> Map k v
filterGt NothingS t = t
filterGt (JustS b) t = filterGt' b t
  
filterGt' _   Tip = Tip
filterGt' b' (Bin _ kx x l r) =
          case compare b' kx of LT -> join kx x (filterGt' b' l) r
                                EQ -> r
                                GT -> filterGt' b' r

{-@ filterLt :: (Ord k) => x:MaybeS k -> OMap k v -> OMap {v:k | ((isJustS(x)) => (v < fromJustS(x))) } v @-}
filterLt :: Ord k => MaybeS k -> Map k v -> Map k v
filterLt NothingS t = t
filterLt (JustS b) t = filterLt' b t
  
filterLt' _   Tip = Tip
filterLt' b' (Bin _ kx x l r) =
  case compare kx b' of LT -> join kx x l (filterLt' b' r)
                        EQ -> l
                        GT -> filterLt' b' l

{-@ join :: kcut:k -> a -> OMap {v:k | v < kcut} a -> OMap {v:k| v > kcut} a -> OMap k a @-}
join :: k -> a -> Map k a -> Map k a -> Map k a
join kx x l r = Bin 1 kx x l r 
