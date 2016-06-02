module Count () where

{-@ LIQUID "--no-pattern-inline" @-}

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
