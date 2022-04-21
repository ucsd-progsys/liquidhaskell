{-@ LIQUID "--no-positivity-check" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-# LANGUAGE GADTs #-}
module GuardedNegative where

data GuardedNegative where  
      NatInduction  :: (Int -> Bool) -> GuardedNegative -> (Int -> GuardedNegative -> GuardedNegative) -> Int -> GuardedNegative
      FromSMT       :: Bool -> GuardedNegative

{-@ data GuardedNegative where 
      NatInduction :: p:(Nat -> Bool)
                   -> Prop {p 0} 
                   -> (n:Nat -> Prop {p (n-1)} -> Prop {p n})      
                   -> n:Nat -> Prop {p n} 
      FromSMT :: b:{Bool | b} -> Prop {b} 
  @-}

{-@ type Prop E = { p:GuardedNegative | E } @-}

trivialUse :: Int -> GuardedNegative 
{-@ trivialUse :: n:Nat -> {v:_ | 0 <= n} @-}
trivialUse = NatInduction p (FromSMT (0 <= 0)) (\n _ -> FromSMT (0 <= n))

{-@ reflect p @-}
{-@ p :: Int -> Bool @-}
p :: Int -> Bool
p i = 0 <= i 
