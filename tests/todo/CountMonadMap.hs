{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--higherorder"       @-}

module Count (sz) where

import Prelude hiding (map)

{-@ measure count :: Count a -> Int @-}

{-@ Count :: x:a -> {v:Count a | v == Count x } @-}
data Count a = Count a

instance Functor Count where
  fmap = undefined

instance Applicative Count where
  pure  = undefined
  (<*>) = undefined

instance Monad Count where
{-@
instance Monad Count where
  >>=    :: forall <r :: Count a -> Bool, p :: Count b -> Bool, q :: Count b -> Bool>.
            {x::Count a <<r>>, y :: Count b <<p>>  |- {v:Count b | count v == count x + count y} <: Count b <<q>>}
            Count a <<r>> -> (a -> Count b<<p>>) -> Count b <<q>> ;
  >>     :: x:Count a -> y:Count b -> {v:Count b | count v == count x + count y};
  return :: a -> {v:Count a | count v == 0 }
@-}
  return x        = let r = Count x in assertCount 0 (Count x)
  (Count x) >>= f = let r = f x in assertCount (getCount (Count x) + getCount r) r
  x >> y = assertCount (getCount x + getCount y) y


{-@ assume assertCount :: i:Int -> x:Count a -> {v:Count a | v == x && count v == i } @-}
assertCount :: Int -> Count a -> Count a
assertCount _ x = x

{-@ assume getCount :: x:Count a -> {v:Int | v == count x } @-}
getCount :: Count a -> Int
getCount _ = 0

{-@ data List [sz] @-}
data List a = Emp | Cons a (List a)

{-@ measure sz @-}
{-@ sz :: List a -> Nat @-}
sz :: List a -> Int
sz Emp         = 0
sz (Cons x xs) = 1 + sz xs

{-@  mapV :: forall <p :: Count b -> Bool, q :: Count (List b) -> Bool>.
               { {v:Count (List b) | count v == 0 } <: (Count (List b) <<q>>)}
               {xs :: List a, y :: Count b <<p>> |- {v:Count [b] | count v == count y * len xs} <: (Count (List b) <<q>>)}
               (a -> Count b <<p>>) -> xs:List a -> (Count (List b) <<q>>)
  @-}

mapV :: (a -> Count b) -> List a -> Count (List b)
mapV f Emp         = return Emp
mapV f (Cons x xs) = do {y <- f x; ys <- mapV f xs; return (Cons y ys)}

-- xs :: List a, m
-- n :: Int
-- ys <- mapV f xs
-- return (y:ys)

{-

mapV :: (a -> Counter t b) -> Vector n a -> Counter (n :* t) (Vector n b)

mapV :: forall <p :: {Count b}, q :: {Count [b]}, l :: {L a}>.
         {xs::[a], y :: p |- {v:Count [b] | count v == count y * (len xs + 1)} <: q }
         (a -> p /\ Count b) -> xs:L a -> q /\ Count {v:[b] | len v == len xs}
{-@ assume incr :: a -> {v:Count a | count v == 1 } @-}
incr :: a -> Count a
incr = Count

{-@ assume unit :: {v:Count () | count v == 0 } @-}
unit = Count ()


type L a = [a]

map :: (a -> Count b) -> [a] -> Count [b]
-- map f []     = return []


{-

y :: Count b
ys :: {c:Count {v:[b] | len v == len xs} | count c == (count y) * (len xs) }

-}

map f (x:xs) =
  let y  = f x
      ys = map f xs          -- count v == len xs * count y
      -- g y ys = return (y:ys) -- count v == 0
      -- h z = ys >>= (g xs y ys z)       -- count v == (len xs * count y) +count y
  in  y >>= (h xs y ys)


{-@ g :: xs:[a] -> y:Count b -> {v:Count [b] | count v == len xs * count y} -> z:b -> zs:[b] -> {v:Count {v:[b] | len v == len zs + 1} | count v == 0 } @-}
g :: [a] -> Count b -> Count [b] -> b -> [b] -> Count [b]
g _ _ _ y ys = return (y:ys)


{-@ h :: xs:[a] -> y:Count b -> ys:{v:Count [b] | count v == len xs * count y} -> z:b -> {v:Count [b] | count v == (len xs) * (count y)} @-}
h :: [a] -> Count b -> Count [b] -> b ->  Count [b]
h xs y ys z = ys >>= (g xs y ys z)


{-
  do y <- f x
     ys <- map f xs
     -- {v: ??? | count v == len xs * count c }
     return (y:ys)

-}

{-
map f (x:xs) =
  let y  = f x
      ys = map f xs
  in y:ys

-}


--             {xs :: L a <<l>>, ys:: {v:[a] | len v == 0 && v == xs}|- {v:Count [b] | count v == 0} <: Count [b] <<q>>}

{-@ map' :: c:Count b -> xs:[a] -> {v:Count [b] | count v == (len xs) * (count c)} @-}
map' :: Count b -> [a] -> Count [b]
map' f []     = return []
map' f (x:xs) =
  do y <- f
     ys <- map' f xs
     return (y:ys)



mapV
  :: (a -> CounterN m b) -> Vector n a -> CounterN (n :* m) (Vector n b)

desugars to
  ::


-}
