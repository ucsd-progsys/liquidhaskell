{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module FingerTree where

import Language.Haskell.Liquid.ProofCombinators 

{-@ measure digitSize @-}
digitSize :: Digit a -> Int
digitSize (One {}) = 1
digitSize (Two {}) = 2
digitSize (Three {}) = 3
digitSize (Four {}) = 4

data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a
    deriving (Show)

data Node a = Node2 {a2::a, b2::a} | Node3 {a3::a, b3::a, c3:: a}
    deriving (Show)

data FingerTree a
    = Empty
    | Single a
    | Deep (Digit a) (FingerTree (Node a)) (Digit a)
    deriving Show

{-@ reflect fingerTreeSize @-}
fingerTreeSize :: FingerTree a -> Int
fingerTreeSize t = size to1 t 

{-@ reflect size @-}
size :: (a -> Int) -> FingerTree a -> Int
size _ Empty        = 0
size f (Single a)   = f a
size f (Deep l m r) = digitS f l + size (nodeS f) m + digitS f r

{-@ reflect digitS @-} 
digitS :: (a -> Int) -> Digit a -> Int
digitS f (One a)        = f a
digitS f (Two a b)      = f a + f b
digitS f (Three a b c)  = f a + f b + f c
digitS f (Four a b c d) = f a + f b + f c + f d

{-@ reflect nodeS @-}
nodeS :: (a -> Int) -> Node a -> Int
nodeS f (Node2 a b)   = f a + f b
nodeS f (Node3 a b c) = f a + f b + f c

{-@ reflect consts @-}
consts a b = a

{-@ reflect to1 @-}
to1 :: a -> Int
to1 _ = 1

{-@ n2Int1 :: a:Int -> b:Int -> {n:Node Int | nodeS to1 n == 2} @-}
n2Int1 :: Int -> Int -> Node Int
n2Int1 a b = Node2 a b

-- {-@ n2Int :: a:Int -> b:Int -> {f:(Int -> Int) | f a == 1 && f b == 1} -> {n:Node Int | nodeS f n == 2} @-}
-- n2Int :: Int -> Int -> (Int -> Int) -> Node Int
-- n2Int a b f = Node2 a b

{-@ measure isEmpty @-}
isEmpty Empty      = True
isEmpty (Single _) = False
isEmpty Deep{}     = False

{-@ singleton :: v:Int -> {ft:FingerTree Int | isEmpty ft} @-}
singleton :: Int -> FingerTree Int
singleton a = Empty 

{-@ fromList :: xs:_ -> {t:_ | fingerTreeSize t == len xs} @-}
fromList :: [a] -> FingerTree a
fromList []     = Empty
fromList (x:xs) = add x (fromList xs)

{-@ infix <| @-}
-- | /O(1)/. Add an element to the left end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
{- (<|) :: a -> ft:FingerTree a -> {v : FingerTree a | fingerTreeSize v == fingerTreeSize ft + 1} @-}
{-@ reflect <| @-}
(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty                    =  Single a
a <| Single b                 =  Deep (One a) Empty (One b)
a <| Deep (Four b c d e) m sf = {- m `seq` -} Deep (Two a b) (Node3 c d e <| m) sf
a <| Deep l m r               = Deep (consDigit a l) m r 

{-@ lem_add :: f:_ -> a:_ -> t:_ -> { size f (a <| t) == size f t + f a }  @-}
lem_add :: (a -> Int) -> a -> FingerTree a -> () 

lem_add f _ Empty       
  = () 

lem_add f _ (Single {}) 
  = () 

lem_add f a t@(Deep (Four b c d e) m sf) 
  =   size f t + f a 
  === digitS f (Four b c d e) + size (nodeS f) m + digitS f sf + f a
  === f a + f b + digitS f sf + f c + f d + f e + size (nodeS f) m 
  === f a + f b + digitS f sf + nodeS f (Node3 c d e) + size (nodeS f) m 
      ? lem_add (nodeS f) (Node3 c d e) m
  === f a + f b + digitS f sf + size (nodeS f) ((Node3 c d e) <| m)
  === size f (Deep (Two a b) ((Node3 c d e) <| m) sf)
  === size f (a <| (Deep (Four b c d e) m sf)) 
  === size f (a <| t)
  *** QED  

lem_add f a t@(Deep l m r)  
  = () 

{-@ thm_add :: a:_ -> t:_ -> { fingerTreeSize (a <| t) == 1 + fingerTreeSize t} @-}
thm_add :: a -> FingerTree a -> Proof --  FingerTree a 
thm_add a t 
  =   fingerTreeSize (a <| t) 
  === size to1 (a <| t) 
    ? lem_add to1 a t
  === size to1 t + to1 a 
  === fingerTreeSize t + 1 
  *** QED

{-@ add :: a:_ -> t:_ -> { v: _ | fingerTreeSize v == 1 + fingerTreeSize t} @-}
add :: a -> FingerTree a -> FingerTree a 
add a t = (a <| t) ? thm_add a t 

{-@ measure isFour @-}
isFour :: Digit a -> Bool 
isFour (Four {}) = True 
isFour _         = False 

{-@ reflect consDigit @-}
{-@ consDigit :: _ -> {d:_ | not (isFour d)} -> _ @-}
consDigit :: a -> Digit a -> Digit a
consDigit a (One b)        = Two a b
consDigit a (Two b c)      = Three a b c
consDigit a (Three b c d)  = Four a b c d

{-@ ft1 :: {v:_ | fingerTreeSize v == 10} @-}
ft1 :: FingerTree Int
ft1 = fromList [1,2,3,4,5,6,7,8,9,10]

{-@ ten :: {v:_ | len v = 10} @-}
ten :: [Int]
ten = [1,2,3,4,5,6,7,8,9,10]

ft2 :: FingerTree Int
ft2 = fromList [1..20000]

main :: IO ()
main = do
    print "test"
    print $ fingerTreeSize ft1 -- 10
    print $ fingerTreeSize ft2 -- 20000
