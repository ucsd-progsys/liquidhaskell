-- | http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/ 

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

{-# LANGUAGE GADTs #-}

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
-- | Kwangkeun Yi's Match 
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/educational-pearl-proof-directed-debugging-revisited-for-a-first-order-version/F7CC0A759398A52C35F21F13236C0E00
-------------------------------------------------------------------
{-@ kmatch :: cs:_ -> r:_ -> _ / [len cs, reSize r] @-}
kmatch :: (Eq a) => [a] -> RE a -> Bool 
kmatch _      None        = False 
kmatch []     r           = empty r 
kmatch cs     (Char c)    = cs == [c] 
kmatch cs     (Alt r1 r2) = kmatch cs r1 || kmatch cs r2  
kmatch (c:cs) (Star r)    = kmatch cs (Cat (deriv r c) r) 
kmatch (c:cs) r           = kmatch cs (deriv r c) 
  
-------------------------------------------------------------------
-- | Derivative-based Regular Expression Matching 
-------------------------------------------------------------------
{-@ reflect dmatch @-}
dmatch :: (Eq a) => [a] -> RE a -> Bool 
dmatch xs r =  empty (derivs r xs)

{-@ reflect derivs @-}
{-@ derivs :: _ -> xs:_ -> _ / [len xs] @-}
derivs :: (Eq a) => RE a -> [a] -> RE a 
derivs r []     = r 
derivs r (c:cs) = derivs (deriv r c) cs

-------------------------------------------------------------------
-- | Derivative 
-------------------------------------------------------------------
{-@ reflect deriv @-}
deriv :: (Eq a) => RE a -> a -> RE a 
deriv None        _  = None 
deriv Empty       _  = None 
deriv (Char y)    x 
  | x == y           = Empty 
  | otherwise        = None 
deriv (Alt r1 r2) x  = Alt (deriv r1 x) (deriv r2 x) 
deriv (Star r)    x  = Cat (deriv r x) (Star r)
deriv (Cat r1 r2) x 
  | empty r1         = Alt (Cat (deriv r1 x) r2) (deriv r2 x)
  | otherwise        =     (Cat (deriv r1 x) r2) 

{-@ reflect empty @-}
empty :: RE a -> Bool 
empty None        = False 
empty (Char _)    = False 
empty Empty       = True 
empty (Star _)    = True 
empty (Cat r1 r2) = empty r1 && empty r2
empty (Alt r1 r2) = empty r1 || empty r2 

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
-- | Theorem: Derivative Matching Equivalence 
--------------------------------------------------------------------------------

{-@ thm :: cs:_ -> r:_ -> Prop (Match cs r) -> { dmatch cs r } @-} 
thm :: (Eq a) => [a] -> RE a -> Match a -> () 
thm cs r cs_match_r = lemEmp r_cs emp_match_r_cs 
  where
    r_cs            = derivs r cs 
    emp_match_r_cs  = lem1s cs r cs_match_r      

{-@ thm' :: cs:_ -> r:{ dmatch cs r } -> Prop (Match cs r) @-}
thm' :: (Eq a) => [a] -> RE a -> Match a
thm' cs r          = lem1s' cs r emp_match_r_cs
  where 
    r_cs           = derivs r cs 
    emp_match_r_cs = lemEmp' r_cs 

--------------------------------------------------------------------------------
-- | Lemma: One-char Equivalence 
--------------------------------------------------------------------------------

{-@ lem1 :: c:_ -> cs:_  -> r:_ 
         -> Prop (Match (cons c cs) r) 
         -> Prop (Match cs (deriv r c))
  @-}
lem1 :: (Eq a) => a -> [a] -> RE a -> Match a -> Match a 
lem1 _ _  None     MEmpty    = MEmpty 
lem1 c cs Empty    MEmpty    = cons_nil c cs `seq` MEmpty
-- lem1 c cs (Char _) (MChar _) = MEmpty 
lem1 _ _  _    _             = undefined -- HARD

{-@ lem1s :: cs:_ -> r:_ 
          -> Prop (Match cs r) 
          -> Prop (Match [] (derivs r cs)) 
  @-}
lem1s :: (Eq a) => [a] -> RE a -> Match a -> Match a
lem1s []     _ m = m 
lem1s (x:xs) r m = lem1s xs  (deriv r x) (lem1 x xs r m) 

{-@ lem1' :: c:_ -> cs:_  -> r:_ 
          -> Prop (Match cs (deriv r c))
          -> Prop (Match (cons c cs) r) 
  @-}
lem1' :: (Eq a) => a -> [a] -> RE a -> Match a -> Match a 
lem1' = undefined -- HARD

{-@ lem1s' ::  cs:_  -> r:_ 
           -> Prop (Match [] (derivs r cs))
           -> Prop (Match cs r) 
  @-}
lem1s' :: (Eq a) => [a] -> RE a -> Match a -> Match a 
lem1s' []     r m = m 
lem1s' (x:xs) r m = lem1' x xs r (lem1s' xs (deriv r x) m)

{-@ lemEmp :: r:_ -> Prop (Match [] r) -> {empty r} @-}
lemEmp :: (Eq a) => RE a -> Match a -> () 
lemEmp None     MEmpty                    = ()
lemEmp Empty    _                         = ()
lemEmp (Star _) _                         = ()
lemEmp (Cat r1 r2) (MCat s1 _ s2 _ e1 e2) = app_nil_nil s1 s2 `seq` 
                                            lemEmp r1 e1      `seq` 
                                            lemEmp r2 e2
lemEmp (Alt r1 r2) (MAltL _ _ _ e1)       = lemEmp r1 e1 
lemEmp (Alt r1 r2) (MAltR _ _ _ e2)       = lemEmp r2 e2 
lemEmp (Char c) (MChar _)                 = cons_nil c [] `seq` ()

{-@ lemEmp' :: r:{empty r} -> Prop (Match [] r) @-}
lemEmp' :: RE a -> Match a 
lemEmp' Empty       = MEmpty 
lemEmp' (Star r)    = MStar0 r 
lemEmp' (Cat r1 r2) = MCat [] r1 [] r2 (lemEmp' r1) (lemEmp' r2) 
lemEmp' (Alt r1 r2) 
  | empty r1        = MAltL [] r1 r2 (lemEmp' r1) 
  | empty r2        = MAltR [] r1 r2 (lemEmp' r2) 
                   
--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

{-@ inline single @-}
single :: a -> [a]
single x = [x]

{-@ inline cons @-}
cons :: a -> [a] -> [a]
cons x xs = x : xs


(&&&) = seq


--------------------------------------------------------------------------------
-- Because GHC Lists are not encoded as ADT for some reason.
--------------------------------------------------------------------------------
{-@ single_nil :: c:_ -> { single c /= [] } @-}
single_nil :: a -> () 
single_nil _ = ()

{-@ cons_nil :: c:_ -> cs:_ -> { cons c cs /= [] } @-}
cons_nil :: a -> [a] -> () 
cons_nil _ _ = undefined

{-@ app_nil_nil :: s1:_ -> s2:{ s1 ++ s2 == [] } 
                -> { s1 == [] && s2 == [] } 
  @-} 
app_nil_nil :: [a] -> [a] -> () 
app_nil_nil [] [] = () 

