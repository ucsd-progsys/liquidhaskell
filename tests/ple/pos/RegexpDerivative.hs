-- | http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++             @-}

{-# LANGUAGE GADTs #-}

module RegexpDerivative where

import Language.Haskell.Liquid.ProofCombinators (pleUnfold)
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
{-@ reflect dmatch @-}
dmatch :: (Eq a) => List a -> RE a -> Bool
dmatch xs r =  empty (derivs r xs)

{-@ reflect derivs @-}
{-@ derivs :: _ -> xs:_ -> _ / [size xs] @-}
derivs :: (Eq a) => RE a -> List a -> RE a
derivs r Nil         = r
derivs r (Cons c cs) = derivs (deriv r c) cs

-------------------------------------------------------------------
-- | Derivative
-------------------------------------------------------------------
{-@ reflect deriv @-}
deriv :: (Eq a) => RE a -> a -> RE a
deriv None        _  = None
deriv Empty       _  = None
deriv (Char y)    x  =
    pleUnfold -- simplifies the proof in lem1a by avoiding to break
              -- verification in cases according to x==y.
      (if x == y then Empty else None)
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
  Match :: List a -> RE a -> MatchP a

data Match a where
  MEmpty :: Match a
  MChar  :: a    -> Match a
  MCat   :: List a  -> RE a -> List a -> RE a -> Match a -> Match a -> Match a
  MAltL  :: List a  -> RE a -> RE a -> Match a -> Match a
  MAltR  :: List a  -> RE a -> RE a -> Match a -> Match a
  MStar0 :: RE a -> Match a
  MStar1 :: List a  -> List a -> RE a -> Match a -> Match a -> Match a

{-@ data Match [msize] a where
        MEmpty :: Prop (Match Nil Empty)
        MChar  :: x:_ -> Prop (Match (single x) (Char x))
        MCat   :: s1:_ -> r1:_ -> s2:_ -> r2:_ ->
                  Prop (Match s1 r1) ->
                  Prop (Match s2 r2) ->
                  Prop (Match {s1 ++ s2} (Cat r1 r2))
        MAltL  :: s:_ -> r1:_ -> r2:_ ->
                  Prop (Match s r1) ->
                  Prop (Match s (Alt r1 r2))
        MAltR  :: s:_ -> r1:_ -> r2:_ ->
                  Prop (Match s r2) ->
                  Prop (Match s (Alt r1 r2))
        MStar0 :: r:_  ->
                  Prop (Match Nil (Star r))
        MStar1 :: s1:{0 < size s1} -> s2:_ -> r:_ ->
                  Prop (Match s1 r) ->
                  Prop (Match s2 (Star r)) ->
                  Prop (Match {s1 ++ s2} (Star r))
  @-}

{-@ measure msize           @-}
{-@ msize :: Match a -> Nat @-}
msize :: Match a -> Int
msize (MEmpty {})          = 0
msize (MChar {})           = 0
msize (MStar0 _)           = 0
msize (MCat _ _ _ _ m1 m2) = 1 + msize m1 + msize m2
msize (MAltL _ _ _ m1)     = 1 + msize m1
msize (MAltR _ _ _ m2)     = 1 + msize m2
msize (MStar1 _ _ _ m1 m2) = 1 + msize m1 + msize m2

--------------------------------------------------------------------------------
-- | Theorem: Derivative Matching Equivalence
--------------------------------------------------------------------------------

{-@ thm :: cs:_ -> r:_ -> Prop (Match cs r) -> { dmatch cs r } @-}
thm :: (Eq a) => List a -> RE a -> Match a -> ()
thm cs r cs_match_r = lemEmp r_cs emp_match_r_cs
  where
    r_cs            = derivs r cs
    emp_match_r_cs  = lem1s cs r cs_match_r

{-@ thm' :: cs:_ -> r:{ dmatch cs r } -> Prop (Match cs r) @-}
thm' :: (Eq a) => List a -> RE a -> Match a
thm' cs r          = lem1s' cs r emp_match_r_cs
  where
    r_cs           = derivs r cs
    emp_match_r_cs = lemEmp' r_cs

--------------------------------------------------------------------------------
-- | Lemma: One-char Equivalence
--------------------------------------------------------------------------------

{-@ lem1 :: c:_ -> cs:_  -> r:_
         -> pf: Prop (Match (Cons c cs) r)
         -> Prop (Match cs (deriv r c)) / [msize pf]
  @-}
lem1 :: (Eq a) => a -> List a -> RE a -> Match a -> Match a
lem1 _ _  None      MEmpty
  = MEmpty
lem1 _ _  Empty     MEmpty
  = MEmpty
lem1 _ _  (Char _)  (MChar _)
  = MEmpty
lem1 c cs (Alt r1 r2) (MAltL _ _ _ m1)
  = MAltL cs (deriv r1 c) (deriv r2 c) (lem1 c cs r1 m1)
lem1 c cs (Alt r1 r2) (MAltR _ _ _ m2)
  = MAltR cs (deriv r1 c) (deriv r2 c) (lem1 c cs r2 m2)
lem1 c cs (Cat r1 r2) (MCat Nil _ s2 _ m1 m2)
  = lemEmp r1 m1 & MAltR cs (Cat (deriv r1 c) r2) (deriv r2 c) (lem1 c cs r2 m2)
lem1 c cs (Cat r1 r2) (MCat (Cons _ s1) _ s2 _ m1 m2)
  | empty r1
  = MAltL (s1 ++ s2) (Cat r1c r2) (deriv r2 c) m      -- :: Match (s1 ++ s2) (deriv r c)
  | otherwise
  = m
  where
    r1c    = deriv r1 c
    m      = MCat s1 r1c s2 r2 (lem1 c s1 r1 m1) m2  -- :: Match (s1 ++ s2) (Cat r1c r2)
lem1 _ _  (Star _) (MStar0 _)
  = MEmpty
lem1 c cs (Star r) (MStar1 (Cons _ s0) s _ m0 m)
  = MCat s0 r' s (Star r) m0' m        -- :: Match (s0 ++ s) (Cat r' (Star r))
  where
    m0'  = lem1 c s0 r m0              -- :: Match s0 r'
    r'   = deriv r c
  -- m0                                   :: Match (Cons c s0) r
  -- m                                    :: Match s (Star r)
  --                                      :: { cs   == s0 ++ s }

{-@ lem1s :: cs:_ -> r:_ -> Prop (Match cs r) -> Prop (Match Nil (derivs r cs)) @-}
lem1s :: (Eq a) => List a -> RE a -> Match a -> Match a
lem1s Nil         _ m = m
lem1s (Cons x xs) r m = lem1s xs  (deriv r x) (lem1 x xs r m)

{-@ lem1a :: c:_ -> cs:_  -> r:_
          -> m: Prop (Match cs (deriv r c))
          -> Prop (Match (Cons c cs) r) / [msize m, 1]
  @-}
lem1a :: (Eq a) => a -> List a -> RE a -> Match a -> Match a
lem1a _ _  None  MEmpty    = MEmpty
lem1a _ _  Empty MEmpty    = MEmpty
lem1a c _  (Char _) MEmpty = MChar c

lem1a c cs (Alt r1 r2) (MAltL _ _ _ m1')
  = MAltL (Cons c cs) r1 r2 (lem1a c cs r1 m1')
                             -- :: Match (Cons c cs) r1
lem1a c cs (Alt r1 r2) (MAltR _ _ _ m2')
  = MAltR (Cons c cs) r1 r2 (lem1a c cs r2 m2')
                             -- :: Match (Cons c cs) r2
lem1a c cs (Star r) (MCat s0 _ s _ m0' m)
  = MStar1 (Cons c s0) s r (lem1a c s0 r m0') m
                             -- :: Match (Cons c s0) r
lem1a c cs (Cat r1 r2) pf
  | empty r1
  = case pf of
      MAltL _ r1c_r2 r2c m_r1c_r2 -> lemCat c cs r1 r2 m_r1c_r2
      MAltR _ r1c_r2 r2c m_r2c    -> MCat Nil r1 (Cons c cs) r2
                                        (lemEmp' r1)           -- :: Match Nil r1
                                        (lem1a c cs r2 m_r2c)  -- :: Match (Cons c cs) r2
  | otherwise
  = lemCat c cs r1 r2 pf

{-@ lemCat :: c:_ -> cs:_ -> r1:_ -> r2:_
           -> pf:Prop (Match cs (Cat (deriv r1 c) r2))
           -> Prop (Match (Cons c cs) (Cat r1 r2)) / [msize pf, 0]
  @-}
lemCat :: (Eq a) => a -> List a -> RE a -> RE a -> Match a -> Match a
lemCat c cs r1 r2 (MCat s1 _ s2 _ m1' m2)
  = MCat (Cons c s1) r1 s2 r2 (lem1a c s1 r1 m1') m2
                               -- :: Match (Cons c s1) r1

{-@ lem1s' ::  cs:_  -> r:_ -> Prop (Match Nil (derivs r cs)) -> Prop (Match cs r) @-}
lem1s' :: (Eq a) => List a -> RE a -> Match a -> Match a
lem1s' Nil     r m     = m
lem1s' (Cons x xs) r m = lem1a x xs r (lem1s' xs (deriv r x) m)

{-@ lemEmp :: r:_ -> Prop (Match Nil r) -> {empty r} @-}
lemEmp :: (Eq a) => RE a -> Match a -> ()
lemEmp None     MEmpty                    = ()
lemEmp Empty    _                         = ()
lemEmp (Star _) _                         = ()
lemEmp (Char c) (MChar _)                 = ()
lemEmp (Cat r1 r2) (MCat s1 _ s2 _ e1 e2) = app_nil_nil s1 s2 & lemEmp r1 e1 & lemEmp r2 e2
lemEmp (Alt r1 r2) (MAltL _ _ _ e1)       = lemEmp r1 e1
lemEmp (Alt r1 r2) (MAltR _ _ _ e2)       = lemEmp r2 e2

{-@ lemEmp' :: r:{empty r} -> Prop (Match Nil r) @-}
lemEmp' :: RE a -> Match a
lemEmp' Empty       = MEmpty
lemEmp' (Star r)    = MStar0 r
lemEmp' (Cat r1 r2) = MCat Nil r1 Nil r2 (lemEmp' r1) (lemEmp' r2)
lemEmp' (Alt r1 r2)
  | empty r1        = MAltL Nil r1 r2 (lemEmp' r1)
  | empty r2        = MAltR Nil r1 r2 (lemEmp' r2)

--------------------------------------------------------------------------------
-- | Lists
--------------------------------------------------------------------------------
{-@ data List [size] @-}
data List a
  = Nil
  | Cons a (List a)
  deriving (Eq)

{-@ measure size @-}
{-@ size :: List a -> Nat @-}
size :: List a -> Int
size Nil         = 0
size (Cons _ xs) = 1 + size xs

{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
Nil         ++ ys = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys)

{-@ reflect single @-}
single :: a -> List a
single x = Cons x Nil

{-@ app_nil_nil :: s1:_ -> s2:{s1 ++ s2 == Nil} -> {s1 == Nil && s2 == Nil} @-}
app_nil_nil :: List a -> List a -> ()
app_nil_nil Nil Nil = ()

--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

(&) = seq

-------------------------------------------------------------------
-- | Kwangkeun Yi's Match
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/educational-pearl-proof-directed-debugging-revisited-for-a-first-order-version/F7CC0A759398A52C35F21F13236C0E00
-------------------------------------------------------------------
{-@ kmatch :: cs:_ -> r:_ -> _ / [size cs, reSize r] @-}
kmatch :: (Eq a) => List a -> RE a -> Bool
kmatch _           None        = False
kmatch Nil         r           = empty r
kmatch cs          (Char c)    = cs == Cons c Nil
kmatch cs          (Alt r1 r2) = kmatch cs r1 || kmatch cs r2
kmatch (Cons c cs) (Star r)    = kmatch cs (Cat (deriv r c) r)
kmatch (Cons c cs) r           = kmatch cs (deriv r c)
