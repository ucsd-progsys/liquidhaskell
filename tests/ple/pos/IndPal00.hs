{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module IndPal00 where

--------------------------------------------------------------------------------
-- | The Prop declaring the Palindrome predicate 
data PalP a = Pal [a] 
  deriving Eq 

-- | The Predicate implementing the Palindrom predicate 
data Pal a where
  Pal0 :: Pal a 
  Pals :: a -> [a] -> Pal a 

{-@ data Pal a where
        Pal0 :: Prop (Pal []) 
        Pals :: x:_ -> xs:_ -> Prop (Pal (x:xs)) 
  @-}


{-@ ple lemma_pal @-}
{-@ lemma_pal :: xs:[a] -> p:{Pal a | prop p == Pal xs} -> { true } @-}

lemma_pal :: Eq a => [a] -> Pal a -> ()
lemma_pal l d = 
  case l of 
    []   -> ()
    xs    -> case d of 
             Pal0       -> error "" -- prop p = Pal xs && prop p = Pal [] 
             (Pals _ _) -> ()

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}


