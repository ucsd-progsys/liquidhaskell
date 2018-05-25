-- | http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/ 
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE GADTs #-}
{-@ infixr ++  @-}

module RE where

import Prelude hiding ((++))

-------------------------------------------------------------------
-- | Regular Expressions 
-------------------------------------------------------------------

{-@ data RE [reSize] @-}
data RE a 
  = None 
  | Empty 
  | Char a
  | Cat  (RE a) (RE a) 
  | Alt  (RE a) (RE a) 
  | Star (RE a) 

{-@ measure reSize @-}
{-@ reSize :: RE a -> Nat @-}
reSize :: RE a -> Int 
reSize None        = 0 
reSize Empty       = 0
reSize (Char _)    = 0
reSize (Cat r1 r2) = 1 + reSize r1 + reSize r2 
reSize (Alt r1 r2) = 1 + reSize r1 + reSize r2 
reSize (Star r)    = 1 + reSize r 

-------------------------------------------------------------------
-- | Derivative-based Match 
-------------------------------------------------------------------
dmatch :: (Eq a) => [a] -> RE a -> Bool 
dmatch xs r =  empty (derivs r xs)

{-@ derivs :: _ -> xs:_ -> _ / [len xs] @-}
derivs :: (Eq a) => RE a -> [a] -> RE a 
derivs r []     = r 
derivs r (x:xs) = derivs (r // x) xs

-------------------------------------------------------------------
-- | Derivative 
-------------------------------------------------------------------

deriv :: (Eq a) => RE a -> a -> RE a 
deriv None        _ = None 
deriv Empty       _ = None 
deriv (Char y)    x 
  | x == y          = Empty 
  | otherwise       = None 
deriv (Alt r1 r2) x = Alt r1' r2' 
  where 
    r1'             = deriv r1 x 
    r2'             = deriv r2 x
deriv (Star r)    x = Cat r' (Star r)
  where 
    r'              = deriv r x
deriv (Cat r1 r2) x 
  | empty r1        = Alt (Cat r1' r2) r2'  
  | otherwise       =     (Cat r1' r2) 
  where 
    r1'             = deriv r1 x 
    r2'             = deriv r2 x

{- 
   lem1A :: c:_ -> cs:_  -> r:_ 
           -> Prop (Match (c:cs) r) 
           -> Prop (Match cs (r // c))
  
   lem1B :: cs:_ -> r:_ 
           -> Prop (Match cs r) 
           -> Prop (Match [] (derivs cr s)) 

   lem2A :: c:_ -> cs:_  -> r:_ 
          -> Prop (Match cs (r // c))
          -> Prop (Match (c:cs) r) 
 
   lem2B ::  cs:_  -> r:_ 
          -> Prop (Match cs r) 
          -> Prop (Match [] (derivs r cs))

   lem3A :: r:_ 
           -> Prop (Match [] r)
           -> { empty r }

   lem3B :: r:_ 
           -> { empty r }
           -> Prop (Match [] r)
                    
   thmA    :: cs:_ -> r:_ 
           -> Prop (Match cs r)
           -> { dmatch cs r } 

   thmB    :: cs:_ -> r:_ 
           -> { dmatch cs r } 
           -> Prop (Match cs r)
                  
 -}

(//) :: (Eq a) => RE a -> a -> RE a 
None        // _  = None 
Empty       // _  = None 
Char y      // x 
  | x == y        = Empty 
  | otherwise     = None 
(Alt r1 r2) // x  = Alt (r1 // x) (r2 // x) 
(Star r)    // x  = Cat (r // x)  (Star r)
(Cat r1 r2) // x 
  | empty r1      = Alt (Cat (r1 // x) r2) (r2 // x)
  | otherwise     =     (Cat (r1 // x) r2) 

empty :: RE a -> Bool 
empty None        = False 
empty (Char _)    = False 
empty Empty       = True 
empty (Star _)    = True 
empty (Cat r1 r2) = empty r1 && empty r2
empty (Alt r1 r2) = empty r1 || empty r2 

-------------------------------------------------------------------------------
-- thm1 :: r:RE a -> s:[a] -> Prop (Match r s) -> { dmatch r s } 
-- thm2 :: r:RE a -> s:[a] -> { dmatch r s } -> Prop (Match r s) 
-------------------------------------------------------------------------------

data MatchP a where
  Match :: [a] -> RE a -> MatchP a
   
data Match a where
  MEmpty :: Match a
  MChar  :: a    -> Match a
  MCat   :: [a]  -> RE a -> [a] -> RE a -> Match a -> Match a -> Match a
  MAltL  :: [a]  -> RE a -> RE a -> Match a -> Match a
  MAltR  :: [a]  -> RE a -> RE a -> Match a -> Match a
  MStar0 :: RE a -> Match a
  MStar1 :: [a]  -> [a] -> RE a -> Match a -> Match a -> Match a
   
{-@ data Match a where
      MEmpty :: Prop (Match [] Empty)
    | MChar  :: x:_ -> Prop (Match (single x) (Char x))
    | MCat   :: s1:_ -> r1:_ -> s2:_ -> r2:_ ->
                Prop (Match s1 r1) ->
                Prop (Match s2 r2) ->
                Prop (Match {s1 ++ s2} (Cat r1 r2))
    | MAltL  :: s:_ -> r1:_ -> r2:_ ->
                Prop (Match s r1) ->
                Prop (Match s (Alt r1 r2))
    | MAltR  :: s:_ -> r1:_ -> r2:_ ->
                Prop (Match s r2) ->
                Prop (Match s (Alt r1 r2))
    | MStar0 :: r:_  ->
                Prop (Match [] (Star r))
    | MStar1 :: s1:_ -> s2:_ -> r:_ ->
                Prop (Match s1 r) ->
                Prop (Match s2 (Star r)) ->
                Prop (Match {s1 ++ s2} (Star r))
  @-}
    

--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-@ reflect single @-}
single x = [x]
