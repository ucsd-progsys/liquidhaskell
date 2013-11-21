module LinSpace where

{-@ measure orthDim :: PVector -> Int 
    orthDim (PVector v o z) = (dim o)
  @-}

{-@ measure tail :: [a] -> [a]
    tail (x:xs)  = xs
  @-}

{-@ measure dim :: Space -> Int 
    dim (Null) = 0
    dim (Real pv n) = 1 + (dim (orthSp pv))
  @-}

{-@ measure orthSp :: PVector -> Space
    orthSp (PVector v m o) = o
  @-}

{-@ measure pvlen :: PVector -> Int
    pvlen (PVector v m o) = (len v)
  @-}

{-@ predicate SameLen  X Y = ((pvlen X)  = (pvlen Y))  @-}
{-@ predicate SameOrth X Y = ((orthSp X) = (orthSp Y)) @-}
{-@ type SameSpace X       = {v:PVector | ((SameLen X v) && (SameOrth X v))} @-}

{-@ measure isReal :: Space -> Prop
    isReal (Null)       = false
    isReal (Rreal pv n) = true
  @-}

{-@ measure spaceVec :: Space -> PVector
    spaceVec (Real pv n) = pv
  @-}

-- ASSERT: length muCoeff == dim orthSpace
-- ASSERT: maybe True (\(v,_) -> length vec == length (vec v)) orthSpace 

{-@ predicate OrthMu  Orth Mu  = (dim Orth) = (len Mu) @-}

{-@ predicate OrthVec Orth Vec = ((isReal Orth) => (len Vec) = (pvlen (spaceVec Orth))) @-}

{-@ data PVector = PVector { 
      vec  :: [Integer]   
    , mu   :: [Integer] 
    , orth :: {v: Space | ((OrthMu v mu) && (OrthVec v vec))}
    } 
  @-}

--------------------
-- "dim" and "sameSpace" are only used in the ASSERTs
dim             :: Space -> Int 
dim Null        = 0
dim (Real pv _) = 1 + dim (orthSpace pv)

sameSpace :: PVector -> PVector -> Bool
sameSpace pv1 pv2 = 
  (length (vec pv1) == length (vec pv2)) && (orthSpace pv1 == orthSpace pv2)
--------------------

data PVector = PVector { 
    vec       :: [Integer]    -- vector coordinates
  , muCoeff   :: [Integer]    -- <vec,bn*>det^2(b[1..n-1]) : ... 
  , orthSpace :: Space        -- lattice basis
  } deriving (Show, Eq)

-- Orthogonalized vector bn* and squared lattice determinant 
-- type Space = Maybe (PVector, Integer) 

data Space = Null | Real PVector Integer
  deriving (Show, Eq)

-- squared determinant of orthSpace
detPV :: PVector -> Integer 
-- detPV = maybe 1 snd . orthSpace
detPV (PVector _ _ Null)       = 1
detPV (PVector _ _ (Real _ n)) = n

-- peel off last layer of projection from PVector
-- ASSERT: dim (orthSpace (liftPV v)) == dim (orthSpace v) - 1
{-@ liftPV :: pv:PVector -> {v:PVector | ((orthSp v) = (tail (orthSp pv)) && ((orthDim v) = (orthDim pv) - 1))} @-}
liftPV (PVector v (m:mu) (Real pv _)) = PVector v mu (orthSpace pv)

-- dot product of two vectors
-- ASSERT: length xs == length ys
{-@ dot :: (Num a) => xs:[a] -> {v:[a] | (len v) = (len xs)} -> a @-}
dot xs ys = sum (zipWith (*) xs ys)

-- scaled dot product of two projected vectors: output is <v*,w*>det^2(orthSpace) 
{-@ dotPV :: x:PVector -> (SameSpace x) -> Integer @-}
-- ASSERT: (dotPV x y) ==> sameSpace x y
dotPV (PVector v1 [] Null) (PVector v2 [] Null) = dot v1 v2
dotPV pv1 pv2 = q 
  where
    -- RJ: ASSUME: orthSp x = orthSp y => tail (orthSp x) = tail (orthSp y)
    dd          = dotPV (liftPV pv1) (liftPV pv2)
    Real pv0 rr = orthSpace pv1 -- same as orthSpace v2
    x           = dd * rr - (head (muCoeff pv1)) * (head (muCoeff pv2))
    (q, 0)      = divMod x (detPV pv0) -- check remainder is 0

{-@ (.+.) :: x:PVector -> (SameSpace x) -> PVector @-}
-- ASSERT: (x .+. y) ==> sameSpace x y
(PVector v1 m1 o) .+. (PVector v2 m2 _) = PVector (zipWith (+) v1 v2) (zipWith (+) m1 m2) o

{-@ (.-.) :: x:PVector -> (SameSpace x) -> PVector @-}
-- ASSERT: (x .-. y) ==> sameSpace x y
(PVector v1 m1 o) .-. (PVector v2 m2 _) = PVector (zipWith (-) v1 v2) (zipWith (-) m1 m2) o

(*.) :: Integer -> PVector -> PVector
x *. (PVector v m o) = PVector (map (x *) v) (map (x *) m) o

-- Some auxiliary functions

space2vec :: Space -> PVector
space2vec sp@(Real bn r) = PVector (vec bn) (r : muCoeff bn) sp

makeSpace :: PVector -> Space
makeSpace pvec = Real pvec (dotPV pvec pvec)

makePVector :: Space -> [Integer] -> PVector
makePVector Null v = PVector v [] Null 
makePVector s@(Real s1 _) v = 
  let v1 = makePVector (orthSpace s1) v
  in PVector v (dotPV v1 s1 : muCoeff v1) s

gramSchmidt :: [[Integer]] -> Space
gramSchmidt = foldl (\sp v -> makeSpace (makePVector sp v)) Null 

getBasis :: Space -> [[Integer]]
getBasis s = worker s [] where
  worker Null bs = bs
  worker (Real pv _) bs = worker (orthSpace pv) (vec pv : bs)


sizeReduce1 :: PVector -> PVector
sizeReduce1 pv@(PVector _ (m:_) sn@(Real _ r)) = 
  let c  = div (2*m + r) (2*r) -- division with rounded remainder
  in pv .-. (c *. space2vec sn)

-- RJ: don't see why this holds without som properties of (.-.) 
{-@ sizeReduce :: x:PVector -> (SameSpace x) @-}
sizeReduce pv@(PVector v [] Null) = pv
-- ASSERT: sameSpace (sizeReduce x) x
sizeReduce pv@(PVector _ _ sp@(Real _ _)) = 
  let pv1 = sizeReduce1 pv
      (PVector v mu _) = sizeReduce (liftPV pv1)
  in PVector v (head (muCoeff pv1) : mu) sp

-- Two example algorithms using the library: enumCVP and lll

enumCVP :: PVector -> Integer -> Maybe [Integer]
enumCVP (PVector v mu Null) r 
  | dot v v < r = Just v 
  | otherwise   = Nothing 
enumCVP t@(PVector _ _ (Real bn _)) r = 
  let t0 = sizeReduce1 t
      cs = if (head (muCoeff t0) < 0) 
           then 0 : concat [[x,negate x] | x <- [1,2..]]
           else 0 : concat [[negate x,x] | x <- [1,2..]]
      branch :: (Integer, Maybe [Integer]) -> [PVector] -> (Integer, Maybe [Integer])
      branch (r,v) (t:ts) = 
        if (dotPV t t >= r * detPV t) then (r,v)
        else case enumCVP t r of
          Nothing -> branch (r,v) ts
          Just w  -> branch (dot w w, Just w) ts
  in snd $ branch (r,Nothing) [liftPV t0 .+. (c *. bn) | c <- cs]

{- Fraction free LLL Algorithm with exact arithmetic and delta=99/100 -}
lll :: [[Integer]] -> [[Integer]]
lll = getBasis . worker Null Nothing where
  worker :: Space -> Maybe PVector -> [[Integer]] -> Space
  worker bs Nothing [] = bs
  worker bs Nothing (v:vs) = worker bs (Just (makePVector bs v)) vs
  worker Null (Just pv) vs = worker (makeSpace pv) Nothing vs
  worker (Real bn r) (Just pv) vs = 
    let pv1 = sizeReduce pv
        pv2 = liftPV pv1
    in if (100*(dotPV pv2 pv2) < 99*r)
       then worker (orthSpace bn) (Just pv2) (vec bn : vs)
       else worker (makeSpace pv1) Nothing vs

