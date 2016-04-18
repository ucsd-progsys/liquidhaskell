module Count () where

import Prelude hiding (map)


{-@ measure count :: Count a -> Int @-}

data Count a = Count a

instance Functor Count where
	fmap = undefined
instance Applicative Count where
  pure  = undefined
  (<*>) = undefined

instance Monad Count where
{-@
instance Monad Count where
  >>=    :: forall <r :: Count a -> Prop, p :: Count b -> Prop, q :: Count b -> Prop>.
            {x::Count a <<r>>, y :: Count b <<p>>  |- {v:Count b | count v == count x + count y} <: Count b <<q>>}
            Count a <<r>> -> (a -> Count b<<p>>) -> Count b <<q>> ;
  >>     :: x:Count a -> y:Count b -> {v:Count b | count v == count x + count y};
  return :: a -> {v:Count a | count v == 0 }
@-}
  return x        = let r = Count x in assertCount 0 (Count x)
  (Count x) >>= f = let r = f x in assertCount (getCount (Count x) + getCount r) r
  x >> y = assertCount (getCount x + getCount y) y
  fail          = error



{-@ assume assertCount :: i:Int -> x:Count a -> {v:Count a | v == x && count v == i } @-}
assertCount :: Int -> Count a -> Count a
assertCount _ x = x

{-@ assume getCount :: x:Count a -> {v:Int | v == count x } @-}
getCount :: Count a -> Int
getCount _ = 0


{-@ assume incr :: a -> {v:Count a | count v == 1 } @-}
incr :: a -> Count a
incr = Count

{-@ assume unit :: {v:Count () | count v == 0 } @-}
unit = Count ()


type L a = [a]

{-@  map :: forall <p :: Count b -> Prop, q :: Count [b] -> Prop, l :: L a  -> Prop >.
            {x::a, xs::[a], y :: Count b <<p>>, ys :: {v:Count [b] | count v == len xs * count y} |- {v:Count [b] | count v == count y * (len xs + 1)} <: Count [b] <<q>>}
            (a -> Count b <<p>>) -> xs:L a -> Count {v:[b] | len v == len xs } <<q>>
@-}

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


{-@ foo :: a -> {v:Count a | count v == 0 }  @-}
foo :: a -> Count a
foo y = return y

{-@ test1 :: {v:Count () | count v == 0 } @-}
test1 :: Count ()
test1 = do
  unit
  unit
  unit

{-@ test2 :: {v:Count () | count v == 1 } @-}
test2 = do
  unit
  y <- incr ()
  unit
  foo y
  unit

{-@ test3 :: {v:Count () | count v == 2 } @-}
test3 = do
  unit
  unit
  incr ()
  incr ()
  unit
