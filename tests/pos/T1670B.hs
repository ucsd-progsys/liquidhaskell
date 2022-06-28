{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module T1670B where

data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

type family Operation t

type instance Operation (LWW t a) = LWW t a

{-@ reflect cenabledLWW @-}
cenabledLWW :: Ord t => LWW t a -> Operation (LWW t a) -> Bool
cenabledLWW (LWW t1 _) (LWW t2 _) = t1 /= t2


{-@ reflect capplyLWW @-}
capplyLWW :: Ord t => LWW t a -> Operation (LWW t a) -> LWW t a
capplyLWW l1@(LWW t1 _) l2@(LWW t2 _) 
     | t1 > t2   = l1
     | otherwise = l2

{-@ clawCommutativityLWW :: Ord t => x : (LWW t a) -> op1 : Operation (LWW t a) -> op2 : Operation (LWW t a) -> {(cenabledLWW x op1 && cenabledLWW x op2  && cenabledLWW (capplyLWW x op1) op2 && cenabledLWW (capplyLWW x op2) op1) => capplyLWW (capplyLWW x op1) op2 == capplyLWW (capplyLWW x op2) op1} @-}
clawCommutativityLWW :: Ord t => LWW t a -> Operation (LWW t a) -> Operation (LWW t a) -> ()
clawCommutativityLWW x@(LWW t0 v0) op1@(LWW t1 v1) op2@(LWW t2 v2) = ()
