{-@ LIQUID "--reflection" @-}

module HOLaws where 

class HOLaws a where 
    eqLaw :: (t -> a) -> t -> t -> Bool 

{-@ class laws HOLaws a where 
  eqSubstitutivity :: f : (t -> a) -> x:t -> y:t -> { x == y => f x == f y}
  @-}


eqSubstitutivity :: HOLaws a => (t -> a) -> t -> t -> ()
eqSubstitutivity _ _ _ = () 

instance HOLaws Int where 
    eqLaw = intEq 

{-@ instance laws HOLaws Int where 
    eqLaw = intEq 
    eqSubstitutivity = eqSubstitutivityInt
  @-}    

{-@ reflect intEq @-}    
intEq :: (a -> Int) -> a -> a -> Bool 
intEq f x y = f x == f y 

{-@ eqSubstitutivityInt :: f : (t -> Int) -> x:t -> y:t -> { x == y => f x == f y} @-}
eqSubstitutivityInt :: (t -> Int) -> t -> t -> ()
eqSubstitutivityInt _ _ _ = () 