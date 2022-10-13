module Fixme where 

data Bit = O | I

{-@ data SqMul = SqMul { sq :: Int, mul :: Int, r :: Int } @-}
data SqMul = SqMul { sq :: Int, mul :: Int, r :: Int }

{-@ reflect weight @-}
weight :: [Bit] -> Int
weight []       = 0
weight (O : bs) = weight bs
weight (I : bs) = 1 + weight bs

sam :: Int -> [Bit] -> SqMul
sam _ []       = SqMul 0 0 1
sam x (O : bs) = let (SqMul s m r) = sam x bs in SqMul (1 + s) m (r * r)
sam x (I : bs) =
  let (SqMul s m r) = sam x bs in SqMul (1 + s) (1 + m) (x * r * r)

{-@ relational sam ~ sam :: x1:_ -> p1:_ -> _ ~ x2:_ -> p2:_ -> _
                         ~~ true => len p1 == len p2 => 
                         Fixme.weight p1 - Fixme.weight p2 == 
                           Fixme.mul (r1 x1 p1) - Fixme.mul (r2 x2 p2) 
                           && Fixme.sq (r1 x1 p1) == Fixme.sq (r2 x2 p2) @-}