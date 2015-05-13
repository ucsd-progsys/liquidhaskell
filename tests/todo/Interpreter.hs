module Interpreter where 
{-@ LIQUID "--totality" @-}
{-@ LIQUID "--real" @-}

data BinOp a = Plus       | Times
data Exp   a = EConst Int | EBinOp (BinOp a) (Exp a) (Exp a)

data Instr a = IConst Int | IBinOp (BinOp a)

type Prog  = [Instr Int]
type Stack = [Int]

{-@ measure binOpDenote @-}
binOpDenote :: Int -> Int -> BinOp a -> Int
binOpDenote x y Plus  = (x+y)
binOpDenote x y Times = (x*y)

{-@ measure expDenote  @-}
expDenote :: Exp a -> Int 
expDenote (EConst n)       = n
expDenote (EBinOp b e1 e2) = binOpDenote (expDenote e1) (expDenote e2) b

{-@ measure instrDenote @-}
{-@ instrDenote :: s:Stack -> i:{v:Instr a | isbinOp v => len s >= 2 } 
                -> {zz: Maybe {v:Stack | len v = if (isbinOp i) then ((len s) - 1) else ((len s) + 1)} | zz = instrDenote s i }
  @-}
instrDenote :: Stack -> Instr a ->  Maybe Stack
instrDenote s  (IConst n) = Just (n:s)
instrDenote xs (IBinOp b) = Just ((binOpDenote (list_fst xs) (list_snd xs) b):(tail2 xs))
instrDenote _  _          = Nothing


iConst n = IConst n

{-@ measure isbinOp @-}
isbinOp :: Instr a -> Bool 
isbinOp (IBinOp b) = True
isbinOp _ = False

{-@ measure list_fst @-}
{-@ measure list_snd @-}

{-@ list_fst :: xs:{v:[a] | len v > 0} -> {v:a | v == list_fst xs} @-}
list_fst :: [a] -> a
list_fst (x:xs) = x

{-@ list_snd :: xs:{v:[a] | len v > 1} -> {v:a | v == list_snd xs} @-}
list_snd :: [a] -> a
list_snd (x:xs) = list_fst xs

{-@ measure tail1 @-}
{-@ measure tail2 @-}
{-@ tail2 :: xs:{v:[a] | len v > 1} -> {v:[a] | (v == tail2 xs) && (len v) = (len xs) - 2} @-}
tail2 :: [a] -> [a]
tail2 (x:xs) = tail1 xs

{-@ tail1 :: xs:{v:[a] | len v > 0} -> {v:[a] | (v == tail1 xs) && (len v) = (len xs) - 1} @-}
tail1 :: [a] -> [a]
tail1 (x:xs) = xs

{-@ measure binOps @-}
binOps :: Prog -> Int
binOps [] = 0 
binOps (x:xs) = if isbinOp x then 1 + binOps xs else binOps xs



cons x xs= x:xs
{-@ measure progDenote @-}
progDenote :: Stack -> Prog -> Maybe Stack
{-@ progDenote :: s:Stack -> is:{v:Prog | len s >= 2 * (binOps v)} 
               -> Maybe Stack @-}
progDenote s [] = Just s
progDenote s (x:xs)
--   = if (iisJust ms) then Just [2] else Nothing
--   where ms = (instrDenote s x )
  = if (iisJust ms) then (progDenote (ifromJust ms) xs) else Nothing
  where ms = instrDenote s x

{-@ measure iisJust @-}
iisJust (Just x) = True
iisJust _ = False

{-@ measure ifromJust @-}
{-@ ifromJust :: x:{Maybe a | iisJust x} -> {v:a | v = ifromJust x} @-}
ifromJust :: Maybe a -> a
ifromJust (Just x) = x 

{- compile :: e:Exp Int -> {v:Prog | (progDenote [] v) == Just ((expDenote e):[])} @-}
compile :: Exp Int -> Prog
compile (EConst n)       = [IConst n]
compile (EBinOp b e1 e2) = compile e2 ++ compile e1 ++ [IBinOp b] 


-- Termination Annotations
{-@ data Exp [expSize] @-}
{-@ invariant {v:Exp a| expSize v >= 0} @-}
{-@ invariant {v:Prog | binOps v >= 0} @-}

{-@ measure expSize @-}
expSize :: Exp a -> Int
expSize (EConst _) = 0
expSize (EBinOp _ e1 e2) = 1 + (expSize e1) + (expSize e2)

{-@ Decrease progDenote 2 @-}