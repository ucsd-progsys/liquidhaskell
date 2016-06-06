module InvariantsTermination where


data Inv  
  = InvZero
  |	InvOne Inv 
  | InvTwo Inv Inv 

{-@ data Inv [isize] @-}

{-@ measure isize @-}
{-@ isize :: Inv -> Nat @-}
isize :: Inv -> Int
isize d = 
  case d of 
  	InvZero      -> 0  
  	InvOne i     -> 1 + isize i 
  	InvTwo i1 i2 -> let s1 = isize i1 
  	                    s2 = isize i2 
  	                in 1 + s1 + s2  

{-
to prove both the invariant 

   {v:Inv | invariant v }

  invariant v <=> 0 <= isize v 

and termination on isize 
the environment is extended with 
 
   forall v. 
      isize v < isize d => invariant v  
   
This is not good enought to prove the InvTwo case: 

  isize i1 < isize d => 0 <= isize i1  
  isize i2 < isize d => 0 <= isize i2 
  isize d = isize i1 + isize i2
  ------------------------------
  0 <= isize i1 < isize d 



  isize i1 < 1 + isize i1 + isize i2 => 0 <= isize i1  
  isize i2 < 1 + isize i1 + isize i2 => 0 <= isize i2 
  ------------------------------
    0 <  1+ isize i1 



-}
