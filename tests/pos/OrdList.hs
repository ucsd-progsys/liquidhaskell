module OrdList (
    OrdList, 
        nilOL, isNilOL, unitOL, appOL, consOL, snocOL, concatOL,
        mapOL, fromOL, toOL, foldrOL, foldlOL
) where

infixl 5  `appOL`
infixl 5  `snocOL`
infixr 5  `consOL`

{-@
data OrdList [olen] a = None
                      | One  (x  :: a)
                      | Many (xs :: ListNE a)
                      | Cons (x  :: a)           (xs :: OrdList a)
                      | Snoc (xs :: OrdList a)   (x  :: a)
                      | Two  (x  :: OrdListNE a) (y  :: OrdListNE a)
@-}

{-@
measure olen :: OrdList a -> Int
olen (None)      = 0
olen (One x)     = 1
olen (Many xs)   = (len xs)
olen (Cons x xs) = 1 + (olen xs)
olen (Snoc xs x) = 1 + (olen xs)
olen (Two x y)   = (olen x) + (olen y)
@-}

{-@ type ListNE    a   = {v:[a]       | (len v)  > 0} @-}
{-@ type OrdListNE a   = {v:OrdList a | (olen v) > 0} @-}
{-@ type OrdListN  a N = {v:OrdList a | (olen v) = N} @-}

{-@ invariant {v:OrdList a | (olen v) >= 0} @-}


data OrdList a
  = None
  | One a
  | Many [a]          -- Invariant: non-empty
  | Cons a (OrdList a)
  | Snoc (OrdList a) a
  | Two (OrdList a) -- Invariant: non-empty
        (OrdList a) -- Invariant: non-empty


{-@ nilOL    :: OrdListN a {0} @-}
{-@ isNilOL  :: xs:OrdList a -> {v:Bool | ((Prop v) <=> ((olen xs) = 0))} @-}

{-@ unitOL   :: a            -> OrdListN a {1} @-}
{-@ snocOL   :: xs:OrdList a -> a            -> OrdListN a {1+(olen xs)} @-}
{-@ consOL   :: a            -> xs:OrdList a -> OrdListN a {1+(olen xs)} @-}
{-@ appOL    :: xs:OrdList a -> ys:OrdList a -> OrdListN a {(olen xs)+(olen ys)} @-}
concatOL :: [OrdList a] -> OrdList a

nilOL        = None
unitOL as    = One as
snocOL as   b    = Snoc as b
consOL a    bs   = Cons a bs
concatOL aas = foldr appOL None aas

isNilOL None = True
isNilOL _    = False

None  `appOL` b     = b
a     `appOL` None  = a
One a `appOL` b     = Cons a b
a     `appOL` One b = Snoc a b
a     `appOL` b     = Two a b

{-@ qualif Go(v:List a, xs:OrdList a, ys:List a): (len v) = (olen xs) + (len ys) @-}

{-@ fromOL :: xs:OrdList a -> {v:[a] | (len v) = (olen xs)} @-}
fromOL :: OrdList a -> [a]
fromOL a = go a []
  where
    go None       acc = acc
    go (One a)    acc = a : acc
    go (Cons a b) acc = a : go b acc
    go (Snoc a b) acc = go a (b:acc)
    go (Two a b)  acc = go a (go b acc)
    go (Many xs)  acc = xs ++ acc

{-@ mapOL :: (a -> b) -> xs:OrdList a -> OrdListN b {(olen xs)} @-}
mapOL :: (a -> b) -> OrdList a -> OrdList b
mapOL _ None = None
mapOL f (One x) = One (f x)
mapOL f (Cons x xs) = Cons (f x) (mapOL f xs)
mapOL f (Snoc xs x) = Snoc (mapOL f xs) (f x)
mapOL f (Two x y) = Two (mapOL f x) (mapOL f y)
mapOL f (Many xs) = Many (map f xs)

instance Functor OrdList where
  fmap = mapOL

foldrOL :: (a->b->b) -> b -> OrdList a -> b
foldrOL _ z None        = z
foldrOL k z (One x)     = k x z
foldrOL k z (Cons x xs) = k x (foldrOL k z xs)
foldrOL k z (Snoc xs x) = foldrOL k (k x z) xs
foldrOL k z (Two b1 b2) = foldrOL k (foldrOL k z b2) b1
foldrOL k z (Many xs)   = foldr k z xs

foldlOL :: (b->a->b) -> b -> OrdList a -> b
foldlOL _ z None        = z
foldlOL k z (One x)     = k z x
foldlOL k z (Cons x xs) = foldlOL k (k z x) xs
foldlOL k z (Snoc xs x) = k (foldlOL k z xs) x
foldlOL k z (Two b1 b2) = foldlOL k (foldlOL k z b1) b2
foldlOL k z (Many xs)   = foldl k z xs

{-@ toOL :: xs:[a] -> OrdListN a {(len xs)} @-}
toOL :: [a] -> OrdList a
toOL [] = None
toOL xs = Many xs
