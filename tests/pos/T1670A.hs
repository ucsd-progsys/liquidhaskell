{-# LANGUAGE TypeFamilies #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module T1670A where

data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

{-@ reflect cenabledLWW @-}
cenabledLWW :: Ord t => LWW t a -> LWW t a -> Bool
cenabledLWW (LWW t1 _) (LWW t2 _) = t1 /= t2


{-@ reflect capplyLWW @-}
capplyLWW :: Ord t => LWW t a -> LWW t a -> LWW t a
capplyLWW l1@(LWW t1 _) l2@(LWW t2 _) 
     | t1 > t2   = l1
     | otherwise = l2

{-@ clawCommutativityLWW :: Ord t => x : (LWW t a) -> op1 : LWW t a -> op2 : LWW t a -> {(cenabledLWW x op1 && cenabledLWW x op2  && cenabledLWW (capplyLWW x op1) op2 && cenabledLWW (capplyLWW x op2) op1) => capplyLWW (capplyLWW x op1) op2 == capplyLWW (capplyLWW x op2) op1} @-}
clawCommutativityLWW :: Ord t => LWW t a -> LWW t a -> LWW t a -> ()
clawCommutativityLWW x@(LWW t0 v0) op1@(LWW t1 v1) op2@(LWW t2 v2) = ()
