
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Query where

data Atom  = VarX
           | VarY
           | Const Int

data Query = Le  Atom  Atom
           | And Query Query
           | Or  Query Query

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }


{-@ reflect evalA @-}
evalA :: Blob -> Atom -> Int
evalA b VarX      = xVal b
evalA b VarY      = yVal b
evalA _ (Const n) = n

{-@ reflect evalQ @-}
evalQ :: Blob -> Query -> Bool
evalQ b (Le  a1 a2) = (evalA b a1) <= (evalA b a2)
evalQ b (And q1 q2) = (evalQ b q1) && (evalQ b q2)
evalQ b (Or  q1 q2) = (evalQ b q1) || (evalQ b q2)

{-@ filterQ :: q:Query -> [Blob] -> [{b:Blob | evalQ b q}] @-}
filterQ :: Query -> [Blob] -> [Blob]
filterQ q []     = []
filterQ q (b:bs)
  | evalQ b q    = b : filterQ q bs
  | otherwise    =     filterQ q bs

{-@ test1 :: [Blob] -> [{v: Blob | xVal v <= 5}] @-}
test1   = filterQ q1
  where
  q1    = (VarX `Le` (Const 10))

{-@ test2 :: [Blob] -> [{v: Blob | xVal v <= 10 && yVal v <= 20}] @-}
test2  = filterQ q2
  where
  q2   = (VarX `Le` (Const 10)) `And` (VarY `Le` (Const 20))
