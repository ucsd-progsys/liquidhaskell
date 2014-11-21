{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff" @-}

module LinSpace (dotPV, sameSpace, enumCVP) where

import Language.Haskell.Liquid.Prelude (liquidAssert, liquidError)
import Prelude hiding (zipWith)

data PVector = PVector { 
    vec       :: [Integer]      -- vector coordinates
  , muCoeff   :: [Integer]      -- <vec,bn*>det^2(b[1..n-1]) : ... 
  , orthSpace :: Space PVector  -- lattice basis
  } deriving (Show, Eq)

-- | Orthogonalized vector bn* and squared lattice determinant 
data Space a = Null | Real a Integer
  deriving (Show, Eq)

{-@ data PVector = PVector { 
      vec_  :: [Integer]   
    , mu_   :: [Integer] 
    , orth_ :: {v: (Space (PVectorN (len vec_))) | dim v = (len mu_)}
    } 
  @-}

{-@ measure dim     :: (Space PVector) -> Int 
    dim (Null)      = 0
    dim (Real pv n) = 1 + (dim (orthSpace pv))
  @-}

{-@ measure spaceVec     :: (Space PVector) -> PVector
    spaceVec (Real pv n) = pv
  @-}

{-@ measure vec :: PVector -> [Integer]
    vec (PVector v m o) = v 
  @-}

{-@ measure muCoeff :: PVector -> [Integer]
    muCoeff (PVector v m o) = m 
  @-}

{-@ measure orthSpace :: PVector -> (Space PVector)
    orthSpace (PVector p m o) = o
  @-}

{-@ invariant {v: PVector | (Inv v) }    @-}
{-@ invariant {v: Space PVector | (dim v) >= 0 } @-}

-- RJ: Helpers for defining properties

{-@ predicate Inv V        = (dim (orthSpace V)) = (len (muCoeff V)) @-}
{-@ predicate SameLen  X Y = ((len (vec X))  = (len (vec Y)))  @-}
{-@ predicate SameOrth X Y = ((orthSpace X) = (orthSpace Y)) @-}

-- RJ: Useful type aliases for specs

{-@ type SameSpace X       = {v:PVector | ((Inv v) && (SameLen X v) && (SameOrth X v))} @-}
{-@ type PVectorN N        = {v: PVector | (len (vec v)) = N}   @-} 
{-@ type PVectorP P        = {v: PVector | (SameLen v P)}       @-} 

--------------------

{-@ dim         :: s:(Space PVector) -> {v:Int | v = (dim s)} @-}
dim Null        = (0 :: Int)
dim (Real pv _) = 1 + dim (orthSpace_ pv)

sameSpace         :: PVector -> PVector -> Bool
sameSpace pv1 pv2 = (length (vec pv1) == length (vec pv2)) && (orthSpace pv1 == orthSpace pv2)


{-@ muCoeff_   :: p:PVector -> {v:[Integer] | v = (muCoeff p) }            @-}
muCoeff_ (PVector v m o) = m

{-@ orthSpace_ :: p:PVector -> {v:(Space (PVectorP p)) | v = (orthSpace p)} @-} 
orthSpace_ (PVector v m o) = o

{-@ vec_       :: p:PVector -> {v:[Integer] | v = (vec p)}                  @-}
vec_     (PVector v m o) = v

--------------------

-- squared determinant of orthSpace
detPV :: PVector -> Integer 
detPV (PVector _ _ Null)       = 1
detPV (PVector _ _ (Real _ n)) = n


{-@ liftPV :: pv:PVector -> {v:(PVectorP pv) | ((orthSpace v) = (orthSpace (spaceVec (orthSpace pv))) && ((dim (orthSpace v)) = (dim (orthSpace pv)) - 1))} @-}
liftPV (PVector v (m:mu) (Real pv _)) = PVector v mu (orthSpace_ pv)

{-@ dot :: (Num a) => xs:[a] -> {v:[a] | (len v) = (len xs)} -> a @-}
dot xs ys = sum (zipWith (*) xs ys)

-- scaled dot product of two projected vectors: output is <v*,w*>det^2(orthSpace) 
{-@ dotPV :: pv1:PVector -> pv2:(SameSpace pv1) -> Integer @-}
dotPV (PVector v1 [] _) (PVector v2 [] _) 
  = dot v1 v2
dotPV pv1@(PVector _ mu1 _) pv2@(PVector _ mu2 _) 
  = liquidAssert (length mu1 == length mu2) q
  where
    dd          = dotPV (liftPV pv1) (liftPV pv2)
    Real pv0 rr = orthSpace_ pv1       -- same as orthSpace v2
    x           = dd * rr - (head mu1) * (head mu2)
    (q, 0)      = divMod x (detPV pv0) -- check remainder is 0

-- ASSERT: (x .+. y) ==> sameSpace x y
{-@ (.+.) :: x:PVector -> (SameSpace x) -> (SameSpace x) @-}
(PVector v1 m1 o) .+. (PVector v2 m2 _) = PVector (zipWith  (+) v1 v2) (zipWith (+) m1 m2) o

-- ASSERT: (x .-. y) ==> sameSpace x y
{-@ (.-.) :: x:PVector -> (SameSpace x) -> (SameSpace x) @-}
(PVector v1 m1 o) .-. (PVector v2 m2 _) = PVector (zipWith  (-) v1 v2) (zipWith (-) m1 m2) o

{-@ (*.) :: Integer -> x:PVector -> (SameSpace x) @-}
(*.) :: Integer -> PVector -> PVector
x *. (PVector v m o) = PVector (map (x *)  v) (map (x *) m) o

-- Some auxiliary functions

{-@ space2vec :: n:Int -> s:(Space (PVectorN n)) -> {v: (PVectorN n) | (orthSpace v) = s} @-}
space2vec (n :: Int) sp@(Real bn r) = PVector (vec_ bn) (r : muCoeff_ bn) sp

{-@ makeSpace :: p:PVector -> (Space (PVectorP p)) @-}
makeSpace pvec = Real pvec (dotPV pvec pvec)

{-@ makePVector :: vs:[Integer] -> s:(Space (PVectorN (len vs))) -> {v: (PVectorN (len vs)) | (orthSpace v) = s} @-}
makePVector :: [Integer] -> Space PVector -> PVector
makePVector v s@Null = PVector v [] s 
makePVector v s@(Real s1 _) = 
  let v1 = makePVector v (orthSpace_ s1) 
  in PVector v (dotPV v1 s1 : muCoeff_ v1)  s

{-@ gramSchmidt :: n:Nat -> [(List Integer n)] -> (Space (PVectorN n)) @-}
gramSchmidt (n :: Int) = foldl (\sp v -> makeSpace (makePVector v sp)) Null 

{-@ getBasis :: n:Nat -> Space (PVectorN n) -> [(List Integer n)] @-}
getBasis (n::Int) s = worker s [] 
  where
    worker Null bs = bs
    worker (Real pv _) bs = worker (orthSpace_ pv) (vec pv : bs)

{-@ qualif EqMu(v:PVector, x:PVector): (len (muCoeff v)) = (len (muCoeff x)) @-}

sizeReduce1 :: PVector -> PVector
sizeReduce1 pv@(PVector v (m:_) sn@(Real _ r)) = 
  let c  = div (2*m + r) (2*r) -- division with rounded remainder
      n  = length v    
  in  pv  .-.  (c *. (space2vec n sn))

-- ASSERT: sameSpace (sizeReduce x) x
{-@ sizeReduce :: x:PVector -> (SameSpace x) @-}
sizeReduce pv@(PVector v [] Null) = pv
sizeReduce pv@(PVector _ _ sp@(Real _ _)) = 
  let pv1 = sizeReduce1 pv
      (PVector v mu _) = sizeReduce (liftPV pv1)
  in PVector v (head (muCoeff_ pv1) : mu) sp

-- Two example algorithms using the library: enumCVP and lll

enumCVP :: PVector -> Integer -> Maybe [Integer]
enumCVP (PVector v mu Null) r 
  | dot v v < r = Just v 
  | otherwise   = Nothing 
enumCVP t@(PVector _ (_:_) (Real bn _)) r = 
  let t0 = sizeReduce1  t
      cs = if (head (muCoeff_ t0) < 0) 
           then 0 : concat [[x,negate x] | x <- [1,2..]]
           else 0 : concat [[negate x,x] | x <- [1,2..]]
      branch :: (Integer, Maybe [Integer]) -> [PVector] -> (Integer, Maybe [Integer])
      branch (r,v) (t:ts) = 
        if (dotPV t t >= r * detPV t) then (r,v)
        else case enumCVP t r of
          Nothing -> branch (r,v) ts
          Just w  -> branch (dot w w, Just w) ts
  in snd $ branch (r,Nothing) [liftPV t0 .+. (c *. bn) | c <- cs]

-- make this parametric on n
{- Fraction free LLL Algorithm with exact arithmetic and delta=99/100 -}
{-@ lll :: n:Nat -> [(List Integer n)] -> [(List Integer n)] @-}
lll :: Int -> [[Integer]] -> [[Integer]]
lll n = getBasis n . lll_worker n Null Nothing

{-@ lll_worker :: n:Nat -> (Space (PVectorN n)) -> (Maybe (PVectorN n)) -> [(List Integer n)] -> (Space (PVectorN n)) @-}
lll_worker (n :: Int) bs Nothing [] = bs
lll_worker n bs Nothing (v:vs)      = lll_worker n bs (Just (makePVector v bs)) vs
lll_worker n Null (Just pv) vs      = lll_worker n (makeSpace pv) Nothing vs
lll_worker n (Real bn r) (Just pv) vs = 
    let pv1 = sizeReduce pv
        pv2 = liftPV pv1
    in if (100*(dotPV pv2 pv2) < 99*r)
       then lll_worker n (orthSpace_ bn) (Just pv2) (vec bn : vs)
       else lll_worker n (makeSpace pv1) Nothing vs

------------------------------------------------------------------------------------
-- RJ: Included for illustration...
------------------------------------------------------------------------------------

{-@ type List a N = {v : [a] | (len v) = N} @-}

{-@ zipWith :: (a -> b -> c) -> xs:[a] -> (List b (len xs)) -> (List c (len xs)) @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ (_:_) []      = liquidError "Dead Code"
zipWith _ [] (_:_)      = liquidError "Dead Code"
