{-@ LIQUID "--higherorder"       @-}
{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--exactdc"           @-}

module BoyerMoore where

import Prelude hiding 
  (foldl, map, fst, snd, scanl, filter, length, compose, endsWith, inits, reverse, take, 
  Bool(..))

import Proves 

target, input :: L Int 
target = C 1 (C 2 (C 3 (C 1 (C 2 N))))

input = C 1 (C 2 N) `append` target `append` (C 3 (C 1 (C 2 N)))


{-@ reflect map @-}
{-@ reflect foldl @-}
{-@ reflect fstV @-}
{-@ reflect sndV @-}
{-@ reflect scanl @-}
{-@ reflect filter @-}
{-@ reflect endsWith @-}
{-@ reflect inits @-}
{-@ reflect reverse @-}
{-@ reflect append @-}
{-@ reflect take @-}
{-@ reflect range @-}
{-@ reflect fork @-}

matches ws = map length `compose` filter (endsWith ws) `compose` inits


-- with map f `compose` filter p == map fst `compose` filter snd `compose` map (fork f p)

-- matches ws = map fst `compose` filter snd `compose` map (fork length (endsWith ws)) `compose` inits

-- with  map (fork length (endsWith ws)) `compose` inits == scanl step (P 0 N)

-- matches ws = map fst `compose` filter snd `compose` scanl step (P 0 N)


matchesBM ws
  =  map fstV 
      `compose`
     filter ((reverse ws `isSubString`) `compose` sndV) 
      `compose`
     scanl step (P 0 N)






-- Prop 16.1

map_filter :: (a -> b) -> (a -> Bool) -> L a -> Proof 
{-@ map_filter :: f:(a -> b) -> p:(a -> Bool) -> xs:L a 
    ->  {map fstV (filter sndV (map (fork f p) xs)) == map f (filter p xs) }
  @-}
map_filter f p N 
  =   map fstV (filter sndV (map (fork f p) N))
  ==. map fstV (filter sndV N)
  ==. map fstV N
  ==. N
  ==. map f N
  ==. map f (filter p N) 
  *** QED 

map_filter f p (C x xs) | p x == True 
  =   map fstV (filter sndV (map (fork f p) (C x xs)))
  ==. map fstV (filter sndV ((fork f p x) `C` map (fork f p) xs))
  ==. map fstV (filter sndV ((P (f x) (p x)) `C` map (fork f p) xs))
       ? (sndV (P (f x) (p x)) ==. p x *** QED )  
  ==. map fstV (P (f x) (p x) `C` filter sndV (map (fork f p) xs))
  ==. fstV (P (f x) (p x)) `C` map fstV (filter sndV (map (fork f p) xs))
  ==. (f x)  `C` map f (filter p xs) ? map_filter f p xs 
  ==. map f (x `C` filter p xs) 
  ==. map f (filter p (C x xs)) 
  *** QED 

map_filter f p (C x xs) 
  =   map fstV (filter sndV (map (fork f p) (C x xs)))
  ==. map fstV (filter sndV ((fork f p x) `C` map (fork f p) xs))
  ==. map fstV (filter sndV ((P (f x) (p x)) `C` map (fork f p) xs))
       ? (sndV (P (f x) (p x)) ==. p x *** QED )  
  ==. map fstV (filter sndV (map (fork f p) xs))
  ==. map f (filter p xs) ? map_filter f p xs 
  ==. map f (filter p (C x xs)) 
  *** QED 




{-@ scan_lemma :: op:(b -> a -> b) -> e:b -> xs:L a 
  -> {map (foldl op e) (inits xs) == scanl op e xs } @-}
scan_lemma :: (b -> a -> b) -> b -> L a -> Proof
scan_lemma op e N  
  =   map (foldl op e) (inits N)
  ==. map (foldl op e) (map (\i -> take i N) (range 0 (length N)))
  ==. map (foldl op e) (map (\i -> take i N) (range 0 0))
  ==. map (foldl op e) (map (\i -> take i N) (C 0 N))
  ==. map (foldl op e) (take 0 N `C` map (\i -> take i N) N)
  ==. map (foldl op e) (N `C` N)
  ==. foldl op e N `C` N
  ==. scanl op e N 
  *** QED 

scan_lemma op e xs  
  =   map (foldl op e) (inits xs)
  ==. scanl op e xs 
  *** QED 

step :: P Int (L a) -> a -> P Int (L a)
step (P n sx) x = P (n+1) (x `C` sx)

-- with reverse xs = foldl (flip C) N xs 


fork :: (a -> b) -> (a -> c) -> a -> P b c 
fork f g x = P (f x) (g x) 

fstV :: P a b -> a 
fstV (P x y) = x 

sndV :: P a b -> b 
sndV (P x y) = y 

isSubString :: L Int -> L Int -> Bool 
isSubString (C x xs) (C y ys)
  | x == y 
  = isSubString xs ys 
  | otherwise 
  = False 
isSubString N _ 
  = True 
isSubString _ _ 
  = False  

compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)


{-@ endsWith :: L Int -> xs:L Int -> Bool / [length xs] @-}
endsWith :: L Int -> L Int -> Bool 
endsWith N        N = True 
endsWith N  (C _ _) = False
endsWith (C _ _)  N = False
endsWith (C x xs) (C y ys)
  | x == y 
  = endsWith xs ys 
  | otherwise 
  = endsWith (C x xs) ys 


foldl :: (b -> a -> b) -> b -> L a -> b 
foldl f b N        = b 
foldl f b (C x xs) = foldl f (f b x) xs


inits :: L a -> L (L a)
inits xs = map f rng -- (`take` xs) (range 0 (length xs))
  where
    {-@ rng :: L {v:Nat | v <= length xs} @-}
    rng = range 0 (length xs)
    {-@ f :: i:{Nat | i <= length xs} -> L a @-}
    f i = take i xs

{-@ range :: i:Nat -> j:{Nat | i <= j} 
          -> L {v:Nat | i <= v && v <= j} / [j - i] 
  @-}
range :: Int -> Int -> L Int 
range i j 
  | i == j 
  = C i N 
  | i <= j 
  = C i (range (i+1) j)
  | otherwise
  = N

{-@ measure length @-}
{-@ length :: L a -> Nat @-} 
length :: L a -> Int 
length N        = 0 
length (C _ xs) = 1 + length xs

{-@ take :: i:Nat -> {v:L a | i <= length v} -> L a @-} 
take :: Int -> L a -> L a 
take i N        = N 
take i (C x xs) = if i == 0 then N else x `C` take (i-1) xs 

filter :: (a -> Bool) -> L a -> L a 
filter _ N = N 
filter p (C x xs)
  | p x == True 
  = x `C` filter p xs 
  | otherwise
  = filter p xs 

reverse :: L a -> L a 
reverse N = N 
reverse (C x xs) = reverse xs `append` C x N 

append :: L a -> L a -> L a 
append N        ys = ys 
append (C x xs) ys = C x (append xs ys)

map :: (a -> b) -> L a -> L b 
map _ N = N 
map f (C x xs) = f x `C` map f xs 


scanl :: (b -> a -> b) -> b -> L a -> L b
scanl f q ls  = q `C` (case ls of
                         N      -> N
                         C x xs -> scanl f (f q x) xs)


{-@ data P a b = P {pFs :: a, pSnd :: b} @-} 

{-@ data Bool = True | False @-} 
data Bool = True | False 
  deriving (Show, Eq)

data P a b = P a b 
  deriving (Show)

{-@ data L [length] a = N | C {lhead :: a, lCons :: (L a)} @-}
data L a = N | C a (L a)
  deriving (Show)