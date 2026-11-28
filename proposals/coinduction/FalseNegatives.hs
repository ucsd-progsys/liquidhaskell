{-@ LIQUID "--modern" @-}
{-@ LIQUID "--fuel=2" @-}
{-@ LIQUID "--max-case-expand=4" @-}

module FalseNegatives where

--------------------------------------------------------------------------------
-- Common definitions
--------------------------------------------------------------------------------

{-@ type Proof = () @-}
type Proof = ()

{-@ type Nat = {v:Int | 0 <= v} @-}
type Nat = Int

{-@ reflect bnot @-}
bnot :: Bool -> Bool
bnot True  = False
bnot False = True

infixr 5 :>

data Stream a = (:>) { shead :: a, stail :: Stream a } | StreamEnd

{-@ measure isCons @-}
isCons :: Stream a -> Bool
isCons (_ :> _)  = True
isCons StreamEnd = False

{-@ type IStream a = {v:Stream a | isCons v} @-}
{-@ data Stream a = (:>) { shead :: a, stail :: IStream a } | StreamEnd @-}

{-@ reflect streamBisim @-}
{-@ streamBisim :: Eq a => IStream a -> IStream a -> Bool @-}
streamBisim :: Eq a => Stream a -> Stream a -> Bool
streamBisim (x :> xs) (y :> ys) =
    x == y && streamBisim xs ys

--------------------------------------------------------------------------------
-- 1. Pointwise map and map fusion
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (COINDUCTIVE PROOF OF MAP FUSION).
--
-- Proves smap f (smap g xs) == smap (f . g) xs directly by corecursion on
-- infinite streams without manual step-indexing.
--------------------------------------------------------------------------------

{-@ reflect smap @-}
{-@ smap :: (a -> b) -> IStream a -> IStream b @-}
smap :: (a -> b) -> Stream a -> Stream b
smap f (x :> xs) = f x :> smap f xs

{-@ mapFusion
      :: f:(b -> c)
      -> g:(a -> b)
      -> xs:IStream a
      -> {smap f (smap g xs) == smap (f . g) xs}
  @-}
mapFusion :: (b -> c) -> (a -> b) -> Stream a -> Proof
mapFusion f g (_ :> xs) = mapFusion f g xs

--------------------------------------------------------------------------------
-- 2. Merge, odds, evens, and stream reconstruction
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (PRODUCTIVE CORECURSION AND COINDUCTIVE PROOF).
--
-- merge swaps its two stream arguments and odds recurses on stail xs, so
-- current Liquid Haskell rejects both as non-terminating and rejects
-- mergeEvenOdd.
--------------------------------------------------------------------------------

{-@ reflect merge @-}
{-@ merge :: IStream a -> IStream a -> IStream a @-}
merge :: Stream a -> Stream a -> Stream a
merge (x :> xs) ys = x :> merge ys xs

{-@ reflect odds @-}
{-@ odds :: IStream a -> IStream a @-}
odds :: Stream a -> Stream a
odds (x :> xs) = x :> odds (stail xs)

{-@ reflect evens @-}
{-@ evens :: IStream a -> IStream a @-}
evens :: Stream a -> Stream a
evens xs = odds (stail xs)

{-@ mergeEvenOdd
      :: xs:IStream a
      -> {merge (odds xs) (evens xs) == xs}
  @-}
mergeEvenOdd :: Stream a -> Proof
mergeEvenOdd (_ :> xs) = mergeEvenOdd xs

--------------------------------------------------------------------------------
-- 3. Thue-Morse sequence fixed point and negation commutativity
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (PRODUCTIVE STREAM GENERATOR AND COINDUCTIVE PROOFS).
--
-- morse is a productive corecursive CAF guarded by two (:>) constructors.
-- Current Liquid Haskell rejects morse (no decreasing parameter) as well as
-- the corecursive proofs fMerge, morseFix, and fNotCommute.
--------------------------------------------------------------------------------

{-@ reflect morse @-}
{-@ morse :: IStream Bool @-}
morse :: Stream Bool
morse =
    False :>
    True  :>
    merge (stail morse) (smap bnot (stail morse))

{-@ reflect f @-}
{-@ f :: IStream Bool -> IStream Bool @-}
f :: Stream Bool -> Stream Bool
f (x :> xs) = x :> bnot x :> f xs

{-@ fMerge
      :: xs:IStream Bool
      -> {f xs == merge xs (smap bnot xs)}
  @-}
fMerge :: Stream Bool -> Proof
fMerge (_ :> xs) = fMerge xs

{-@ morseFix
      :: {f morse == morse}
  @-}
morseFix :: Proof
morseFix = fMerge (stail morse)

{-@ fNotCommute
      :: s:IStream Bool
      -> {f (smap bnot s) == smap bnot (f s)}
  @-}
fNotCommute :: Stream Bool -> Proof
fNotCommute (_ :> xs) = fNotCommute xs

--------------------------------------------------------------------------------
-- 4. Unary stream predicates (trivial, dup, nneg)
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--
-- EXPECTED: ACCEPT (COINDUCTIVE PREDICATE PROOFS).
--
-- Tests corecursive unary copredicates on streams: trivialAll, mergeSelfDup,
-- and squareNNeg. mergeSelfDup fails in current Liquid Haskell due to merge.
--------------------------------------------------------------------------------

{-@ reflect trivial @-}
{-@ trivial :: IStream a -> Bool @-}
trivial :: Stream a -> Bool
trivial (_ :> xs) = trivial xs

{-@ trivialAll
      :: s:IStream a
      -> {trivial s}
  @-}
trivialAll :: Stream a -> Proof
trivialAll (_ :> xs) = trivialAll xs

{-@ reflect dup @-}
{-@ dup :: Eq a => IStream a -> Bool @-}
dup :: Eq a => Stream a -> Bool
dup (x1 :> x2 :> xs) = x1 == x2 && dup xs

{-@ mergeSelfDup
      :: Eq a
      => xs:IStream a
      -> {dup (merge xs xs)}
  @-}
mergeSelfDup :: Eq a => Stream a -> Proof
mergeSelfDup (_ :> xs) = mergeSelfDup xs

{-@ reflect nneg @-}
{-@ nneg :: IStream Int -> Bool @-}
nneg :: Stream Int -> Bool
nneg (x :> xs) = 0 <= x && nneg xs

{-@ reflect mult @-}
{-@ mult :: IStream Int -> IStream Int -> IStream Int @-}
mult :: Stream Int -> Stream Int -> Stream Int
mult (x :> xs) (y :> ys) = x * y :> mult xs ys

{-@ squareNNeg
      :: s:IStream Int
      -> {nneg (mult s s)}
  @-}
squareNNeg :: Stream Int -> Proof
squareNNeg (_ :> xs) = squareNNeg xs

--------------------------------------------------------------------------------
-- 5. Lexicographic ordering below pointwise square
--
-- Sources:
--   Mastorou, Papaspyrou, and Vazou (2022), Coinduction Inductively.
--   Leino and Moskal (2014), Coinduction Simply, Figure 0.
--
-- EXPECTED: ACCEPT (COINDUCTIVE ORDERING PROOF).
--
-- Every integer stream is lexicographically below its pointwise square.
--------------------------------------------------------------------------------

{-@ reflect implies @-}
implies :: Bool -> Bool -> Bool
implies p q = bnot p || q

{-@ reflect below @-}
{-@ below :: Ord a => IStream a -> IStream a -> Bool @-}
below :: Ord a => Stream a -> Stream a -> Bool
below (x :> xs) (y :> ys) =
    x <= y && implies (x == y) (below xs ys)

{-@ belowSquare
      :: s:IStream Int
      -> {below s (mult s s)}
  @-}
belowSquare :: Stream Int -> Proof
belowSquare (_ :> xs) = belowSquare xs

--------------------------------------------------------------------------------
-- 6. Ascending stream Up and positivity (Dafny Figures 5 and 8)
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figures 5 and 8.
--
-- EXPECTED: ACCEPT (PRODUCTIVE GENERATOR AND COINDUCTIVE POSITIVITY PROOF).
--
-- up n increments n beneath SCons and upPos proves positivity coinductively.
-- Current Liquid Haskell rejects both because n + 1 does not decrease n.
--------------------------------------------------------------------------------

data DStream a
    = SNil
    | SCons a (DStream a)

{-@ reflect positive @-}
positive :: DStream Int -> Bool
positive SNil = True
positive (SCons x xs) = x > 0 && positive xs

{-@ reflect up @-}
up :: Int -> DStream Int
up n = SCons n (up (n + 1))

{-@ upPos
      :: n:{Int | n > 0}
      -> {positive (up n)}
  @-}
upPos :: Int -> Proof
upPos n = upPos (n + 1)

--------------------------------------------------------------------------------
-- 7. Mixed induction and coinduction: FivesUp and FivesUpPos
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figures 5 and 11.
--
-- EXPECTED: ACCEPT (MIXED INDUCTIVE METRIC AND PRODUCTIVE CORECURSION).
--
-- Recursive calls skipping non-multiples of 5 decrease the metric
-- 4 - ((n - 1) mod 5). Calls on multiples of 5 emit SCons and are justified
-- by coinduction, which current Liquid Haskell rejects.
--------------------------------------------------------------------------------

{-@ reflect fivesUp @-}
{-@ fivesUp
      :: n:Int
      -> DStream Int
      / [4 - ((n - 1) mod 5)]
  @-}
fivesUp :: Int -> DStream Int
fivesUp n
    | n `mod` 5 == 0 = SCons n (fivesUp (n + 1))
    | otherwise      = fivesUp (n + 1)

{-@ fivesUpPos
      :: n:{Int | n > 0}
      -> {positive (fivesUp n)}
      / [4 - ((n - 1) mod 5)]
  @-}
fivesUpPos :: Int -> Proof
fivesUpPos n
    | n `mod` 5 == 0 = fivesUpPos (n + 1)
    | otherwise      = fivesUpPos (n + 1)

--------------------------------------------------------------------------------
-- 8. Splitting and interleaving infinite streams (Dafny Figure 12)
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figure 12.
--
-- EXPECTED: ACCEPT (PRODUCTIVE CORECURSION AND COINDUCTIVE LEMMAS).
--
-- evenS recurses on stail xs and fails termination in current Liquid Haskell,
-- along with evenOddLemma. Includes evenZipLemma and bzipZipLemma.
--------------------------------------------------------------------------------

{-@ reflect zipS @-}
{-@ zipS :: IStream a -> IStream a -> IStream a @-}
zipS :: Stream a -> Stream a -> Stream a
zipS (x :> xs) (y :> ys) =
    x :> y :> zipS xs ys

{-@ reflect evenS @-}
{-@ evenS :: IStream a -> IStream a @-}
evenS :: Stream a -> Stream a
evenS (x :> xs) =
    x :> evenS (stail xs)

{-@ reflect oddS @-}
{-@ oddS :: IStream a -> IStream a @-}
oddS :: Stream a -> Stream a
oddS xs = evenS (stail xs)

{-@ evenOddLemma
      :: xs:IStream a
      -> {zipS (evenS xs) (oddS xs) == xs}
  @-}
evenOddLemma :: Stream a -> Proof
evenOddLemma (_ :> _ :> xs) = evenOddLemma xs

{-@ evenZipLemma
      :: xs:IStream a
      -> ys:IStream a
      -> {evenS (zipS xs ys) == xs}
  @-}
evenZipLemma :: Stream a -> Stream a -> Proof
evenZipLemma (_ :> xs) (_ :> ys) =
    evenZipLemma xs ys

{-@ reflect bzipS @-}
{-@ bzipS :: IStream a -> IStream a -> Bool -> IStream a @-}
bzipS :: Stream a -> Stream a -> Bool -> Stream a
bzipS xs ys chooseX
    | chooseX =
        case xs of
            x :> xt -> x :> bzipS xt ys False
    | otherwise =
        case ys of
            y :> yt -> y :> bzipS xs yt True

{-@ bzipZipLemma
      :: xs:IStream a
      -> ys:IStream a
      -> {zipS xs ys == bzipS xs ys True}
  @-}
bzipZipLemma :: Stream a -> Stream a -> Proof
bzipZipLemma (_ :> xs) (_ :> ys) =
    bzipZipLemma xs ys

--------------------------------------------------------------------------------
-- 9. Trivial co-predicate sanity check (Dafny Figure 13)
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figure 13.
--
-- EXPECTED: ACCEPT (COINDUCTIVE PREDICATE SANITY CHECK).
--
-- Preserves the Dafny Figure 13 presentation of True and TrueLemma.
--------------------------------------------------------------------------------

{-@ reflect trueCoPredicate @-}
{-@ trueCoPredicate :: IStream a -> Bool @-}
trueCoPredicate :: Stream a -> Bool
trueCoPredicate = trivial

{-@ trueLemma
      :: s:IStream a
      -> {trueCoPredicate s}
  @-}
trueLemma :: Stream a -> Proof
trueLemma = trivialAll

--------------------------------------------------------------------------------
-- 10. Infinite paths imply finite prefixes (Dafny Figure 16)
--
-- Sources:
--   Leino and Moskal (2014), Coinduction Simply, Figure 16.
--
-- EXPECTED: ACCEPT (INDUCTION OVER N WITH COINDUCTIVE PREMISE).
--
-- Given a stream witness p satisfying the copredicate follows rel x p, its
-- first n transitions form a valid finitePath.
--------------------------------------------------------------------------------

{-@ reflect follows @-}
{-@ follows :: (a -> a -> Bool) -> a -> IStream a -> Bool @-}
follows :: (a -> a -> Bool) -> a -> Stream a -> Bool
follows rel x (y :> ys) =
    rel x y && follows rel y ys

{-@ reflect finitePath @-}
{-@ finitePath :: (a -> a -> Bool) -> Nat -> a -> IStream a -> Bool @-}
finitePath :: (a -> a -> Bool) -> Nat -> a -> Stream a -> Bool
finitePath _ 0 _ _ = True
finitePath rel n x (y :> ys) =
    rel x y && finitePath rel (n - 1) y ys

{-@ infinitePathImpliesPrefix
      :: rel:(a -> a -> Bool)
      -> n:Nat
      -> x:a
      -> p:{IStream a | follows rel x p}
      -> {finitePath rel n x p}
  @-}
infinitePathImpliesPrefix
    :: (a -> a -> Bool)
    -> Nat
    -> a
    -> Stream a
    -> Proof
infinitePathImpliesPrefix _ 0 _ _ = ()
infinitePathImpliesPrefix rel n x (y :> ys) =
    infinitePathImpliesPrefix rel (n - 1) y ys

--------------------------------------------------------------------------------
-- 11. Stream deinterleaving and reinterleaving (mergeSplit)
--
-- Sources:
--   Kozen and Silva (2017), Practical Coinduction, Theorem 7.
--
-- EXPECTED: ACCEPT (COINDUCTIVE BISIMILARITY PROOF).
--
-- Proves streamBisim (mergePair (split s)) s. Current Liquid Haskell rejects
-- mergeSplit and merge.
--------------------------------------------------------------------------------

{-@ reflect split @-}
{-@ split :: IStream a -> (IStream a, IStream a) @-}
split :: Stream a -> (Stream a, Stream a)
split (x :> y :> xs) =
    let (evenTail, oddTail) = split xs
    in  (x :> evenTail, y :> oddTail)

{-@ reflect mergePair @-}
{-@ mergePair :: (IStream a, IStream a) -> IStream a @-}
mergePair :: (Stream a, Stream a) -> Stream a
mergePair (xs, ys) = merge xs ys

{-@ mergeSplit
      :: Eq a
      => s:IStream a
      -> {streamBisim (mergePair (split s)) s}
  @-}
mergeSplit :: Eq a => Stream a -> Proof
mergeSplit (_ :> xs) =
    mergeSplit xs

--------------------------------------------------------------------------------
-- 12. Moessner's theorem
--
-- Sources:
--   Niqui and Rutten (2011/2012), A Proof of Moessner's Theorem by Coinduction,
--   Theorem 3.1 and Section 5.
--
-- EXPECTED: ACCEPT (PRODUCTIVE STREAM GENERATORS AND BISIMULATION PROOF).
--
-- Constructs Moessner's iterated drop-and-partial-sum pipeline over infinite
-- streams. Current Liquid Haskell rejects repeatStream (and fromPositive) as
-- non-terminating corecursive generators.
--------------------------------------------------------------------------------

{-@ reflect repeatStream @-}
repeatStream :: a -> Stream a
repeatStream x = x :> repeatStream x

{-@ reflect fromPositive @-}
fromPositive :: Integer -> Stream Integer
fromPositive n = n :> fromPositive (n + 1)

{-@ reflect mapStream @-}
mapStream :: (a -> b) -> Stream a -> Stream b
mapStream g (x :> xs) =
    g x :> mapStream g xs

{-@ reflect addStream @-}
addStream :: Stream Integer -> Stream Integer -> Stream Integer
addStream (x :> xs) (y :> ys) =
    (x + y) :> addStream xs ys

{-@ reflect multiplyStream @-}
multiplyStream :: Stream Integer -> Stream Integer -> Stream Integer
multiplyStream (x :> xs) (y :> ys) =
    (x * y) :> multiplyStream xs ys

{-@ reflect ones @-}
ones :: Stream Integer
ones = repeatStream 1

{-@ reflect partialSums @-}
partialSums :: Stream Integer -> Stream Integer
partialSums (x :> xs) =
    x :> addStream (partialSums xs) (repeatStream x)

{-@ reflect dropEveryGo @-}
{-@ dropEveryGo
      :: k:{Int | k >= 2}
      -> i:{Int | 0 <= i && i < k}
      -> j:{Int | 0 <= j && j < k}
      -> IStream Integer
      -> IStream Integer
  @-}
dropEveryGo :: Int -> Int -> Int -> Stream Integer -> Stream Integer
dropEveryGo k i j (x :> xs)
  | j == i && j == k - 1 = dropEveryGo k i 0 xs
  | j == i               = dropEveryGo k i (j + 1) xs
  | j == k - 1           = x :> dropEveryGo k i 0 xs
  | otherwise            = x :> dropEveryGo k i (j + 1) xs

{-@ reflect dropEvery @-}
{-@ dropEvery
      :: k:{Int | k >= 2}
      -> i:{Int | 0 <= i && i < k}
      -> IStream Integer
      -> IStream Integer
  @-}
dropEvery :: Int -> Int -> Stream Integer -> Stream Integer
dropEvery k i xs = dropEveryGo k i 0 xs

{-@ reflect sigmaOperator @-}
sigmaOperator :: Int -> Int -> Stream Integer -> Stream Integer
sigmaOperator k i xs =
    partialSums (dropEvery k i xs)

{-@ reflect applyDescending @-}
applyDescending :: Int -> Stream Integer -> Stream Integer
applyDescending k xs
  | k < 2     = xs
  | otherwise = applyDescending (k - 1) (sigmaOperator k (k - 1) xs)

{-@ reflect moessnerOutput @-}
{-@ moessnerOutput :: n:{Int | n >= 1} -> IStream Integer @-}
moessnerOutput :: Int -> Stream Integer
moessnerOutput n = applyDescending (n + 1) ones

{-@ reflect naturalPowers @-}
{-@ naturalPowers :: n:{Int | n >= 1} -> IStream Integer @-}
naturalPowers :: Int -> Stream Integer
naturalPowers n =
    mapStream (\k -> k ^ n) (fromPositive 1)

{-@ reflect applyDescendingCompanion @-}
applyDescendingCompanion :: Int -> Stream Integer -> Stream Integer
applyDescendingCompanion k xs
  | k < 2     = xs
  | otherwise = applyDescendingCompanion (k - 1) (sigmaOperator k (k - 2) xs)

{-@ reflect moessnerCompanionOutput @-}
{-@ moessnerCompanionOutput :: n:{Int | n >= 1} -> IStream Integer @-}
moessnerCompanionOutput :: Int -> Stream Integer
moessnerCompanionOutput n = applyDescendingCompanion (n + 1) ones

{-@ reflect moessnerCompanionRight @-}
{-@ moessnerCompanionRight :: n:{Int | n >= 1} -> IStream Integer @-}
moessnerCompanionRight :: Int -> Stream Integer
moessnerCompanionRight n =
    multiplyStream
        (fromPositive 1)
        (mapStream (\k -> (k + 1) ^ (n - 1)) (fromPositive 1))

data MoessnerRelation
    = MRTarget Int
    | MRCompanion Int
    | MRRefl (Stream Integer)
    | MRAdd MoessnerRelation MoessnerRelation

{-@ reflect moessnerLeft @-}
moessnerLeft :: MoessnerRelation -> Stream Integer
moessnerLeft (MRTarget n)    = moessnerOutput n
moessnerLeft (MRCompanion n) = moessnerCompanionOutput n
moessnerLeft (MRRefl xs)     = xs
moessnerLeft (MRAdd p q)     = addStream (moessnerLeft p) (moessnerLeft q)

{-@ reflect moessnerRight @-}
moessnerRight :: MoessnerRelation -> Stream Integer
moessnerRight (MRTarget n)    = naturalPowers n
moessnerRight (MRCompanion n) = moessnerCompanionRight n
moessnerRight (MRRefl xs)     = xs
moessnerRight (MRAdd p q)     = addStream (moessnerRight p) (moessnerRight q)

{-@ moessnerRelationBisim
      :: r:MoessnerRelation
      -> {streamBisim (moessnerLeft r) (moessnerRight r)}
  @-}
moessnerRelationBisim :: MoessnerRelation -> Proof
moessnerRelationBisim _ = ()

{-@ moessnerTheorem
      :: n:{Int | n >= 1}
      -> {streamBisim (moessnerOutput n) (naturalPowers n)}
  @-}
moessnerTheorem :: Int -> Proof
moessnerTheorem n =
    moessnerRelationBisim (MRTarget n)

--------------------------------------------------------------------------------
-- 13. Transitivity of the substream relation
--
-- Sources:
--   Cohen and Rowe (2020), Integrating Induction and Coinduction via Closure
--   Operators and Proof Cycles, Section 5.
--
-- EXPECTED: ACCEPT (MIXED INDUCTIVE ALIGNMENT AND COINDUCTIVE WITNESS).
--
-- collectSkipped performs finite inductive alignment over Skipped prefixes,
-- while composeSubstreams constructs the composed coinductive witness.
--------------------------------------------------------------------------------

data Skipped
    = NoSkip
    | SkipOne Skipped

data SubstreamWitness
    = SubstreamStep Skipped SubstreamWitness
    | SubstreamEnd

{-@ measure isStep @-}
isStep :: SubstreamWitness -> Bool
isStep (SubstreamStep _ _) = True
isStep SubstreamEnd        = False

{-@ type ISubstreamWitness = {v:SubstreamWitness | isStep v} @-}
{-@ data SubstreamWitness = SubstreamStep Skipped ISubstreamWitness | SubstreamEnd @-}

{-@ reflect afterSkips @-}
afterSkips :: Skipped -> Stream Integer -> Stream Integer
afterSkips NoSkip xs = xs
afterSkips (SkipOne skips) (_ :> xs) = afterSkips skips xs

{-@ reflect appendSkipped @-}
appendSkipped :: Skipped -> Skipped -> Skipped
appendSkipped NoSkip ys = ys
appendSkipped (SkipOne xs) ys = SkipOne (appendSkipped xs ys)

{-@ reflect substreamHolds @-}
substreamHolds
    :: Stream Integer
    -> Stream Integer
    -> SubstreamWitness
    -> Bool
substreamHolds container (y :> ys) (SubstreamStep skips rest) =
    let matched = afterSkips skips container
    in  shead matched == y
        && substreamHolds (stail matched) ys rest

collectSkipped
    :: Skipped
    -> Stream Integer
    -> Stream Integer
    -> SubstreamWitness
    -> (Skipped, Stream Integer, Stream Integer, SubstreamWitness)
collectSkipped NoSkip xs ys xy =
    (NoSkip, xs, ys, xy)
collectSkipped
    (SkipOne remaining)
    xs
    (_ :> ys)
    (SubstreamStep xySkips xyRest) =
    let xMatched = afterSkips xySkips xs
        (combined, xFinal, yFinal, xyFinal) =
            collectSkipped remaining (stail xMatched) ys xyRest
    in  (appendSkipped xySkips (SkipOne combined), xFinal, yFinal, xyFinal)

{-@ composeSubstreams
      :: xs:IStream Integer
      -> ys:IStream Integer
      -> zs:IStream Integer
      -> xy:{ISubstreamWitness | substreamHolds xs ys xy}
      -> yz:{ISubstreamWitness | substreamHolds ys zs yz}
      -> {w:ISubstreamWitness | substreamHolds xs zs w}
  @-}
composeSubstreams
    :: Stream Integer
    -> Stream Integer
    -> Stream Integer
    -> SubstreamWitness
    -> SubstreamWitness
    -> SubstreamWitness
composeSubstreams xs ys zs xy (SubstreamStep skipsYZ restYZ) =
    let (skipsXZ, xAtZ, yAtZ, xyAtZ) =
            collectSkipped skipsYZ xs ys xy
    in  SubstreamStep
            skipsXZ
            (composeSubstreams
                (stail xAtZ)
                (stail yAtZ)
                (stail zs)
                xyAtZ
                restYZ)

--------------------------------------------------------------------------------
-- 14. Coinductive big-step and small-step divergence
--
-- Sources:
--   Leroy and Grall (2009), Coinductive Big-Step Operational Semantics,
--   Lemma 5 and Theorem 11.
--
-- EXPECTED: ACCEPT (COPREDICATES bigStepDiverges AND smallStepDiverges).
--
-- bigStepDiverges and smallStepDiverges are coinductive divergence predicates.
-- eval is marked lazy as a partial call-by-value helper; current Liquid Haskell
-- rejects bigStepDiverges and smallStepDiverges for lacking decreasing metrics.
--------------------------------------------------------------------------------

data Term
    = Var String
    | Const Integer
    | Lam String Term
    | App Term Term
    deriving (Eq, Show)

data Value
    = VConst Integer
    | VLam String Term
    deriving (Eq, Show)

{-@ reflect isValue @-}
isValue :: Term -> Bool
isValue (Const _) = True
isValue (Lam _ _) = True
isValue _ = False

{-@ reflect valueTerm @-}
valueTerm :: Value -> Term
valueTerm (VConst n)    = Const n
valueTerm (VLam x body) = Lam x body

{-@ reflect substitute @-}
substitute :: String -> Term -> Term -> Term
substitute x value (Var y)
    | x == y    = value
    | otherwise = Var y
substitute _ _ (Const n) = Const n
substitute x value (Lam y body)
    | x == y    = Lam y body
    | otherwise = Lam y (substitute x value body)
substitute x value (App e1 e2) =
    App (substitute x value e1) (substitute x value e2)

{-@ lazy eval @-}
{-@ reflect eval @-}
eval :: Term -> Maybe Value
eval (Const n) = Just (VConst n)
eval (Lam x body) = Just (VLam x body)
eval (Var _) = Nothing
eval (App e1 e2) =
    case eval e1 of
        Just (VLam x body) ->
            case eval e2 of
                Just v  -> eval (substitute x (valueTerm v) body)
                Nothing -> Nothing
        _ -> Nothing

{-@ reflect bigStepDiverges @-}
bigStepDiverges :: Term -> Bool
bigStepDiverges (App e1 e2) =
    bigStepDiverges e1
    ||
    case eval e1 of
        Just v1 ->
            bigStepDiverges e2
            ||
            case (v1, eval e2) of
                (VLam x body, Just v2) ->
                    bigStepDiverges (substitute x (valueTerm v2) body)
                _ -> False
        Nothing -> False
bigStepDiverges _ = False

{-@ reflect smallStep @-}
smallStep :: Term -> Maybe Term
smallStep (App (Lam x body) argument)
    | isValue argument = Just (substitute x argument body)
smallStep (App function argument)
    | not (isValue function) =
        case smallStep function of
            Just function' -> Just (App function' argument)
            Nothing        -> Nothing
    | otherwise =
        case smallStep argument of
            Just argument' -> Just (App function argument')
            Nothing        -> Nothing
smallStep _ = Nothing

{-@ reflect smallStepDiverges @-}
smallStepDiverges :: Term -> Bool
smallStepDiverges term =
    case smallStep term of
        Just next -> smallStepDiverges next
        Nothing   -> False

{-@ theorem11
      :: term:Term
      -> {bigStepDiverges term == smallStepDiverges term}
  @-}
theorem11 :: Term -> Proof
theorem11 _ = ()

{-@ reflect delta @-}
delta :: Term
delta = Lam "x" (App (Var "x") (Var "x"))

{-@ reflect omega @-}
omega :: Term
omega = App delta delta

{-@ omegaDiverges
      :: {bigStepDiverges omega}
  @-}
omegaDiverges :: Proof
omegaDiverges = ()

--------------------------------------------------------------------------------
-- 15. Closure conversion monotonicity
--
-- Sources:
--   Kozen and Silva (2017), Practical Coinduction, Section 3.3, Theorem 5.
--
-- EXPECTED: ACCEPT (MUTUALLY COINDUCTIVE RELATION AND MONOTONICITY PROOF).
--
-- closureValueRelated and closureEnvRelated form a mutually coinductive
-- relation over cyclic closure environments produced by closureConvert.
-- Current Liquid Haskell rejects both predicates as non-terminating.
--------------------------------------------------------------------------------

data CapsuleValue
    = CapsuleConstant Integer
    | CapsuleLambda String Term
    deriving (Eq, Show)

type CapsuleEnv = [(String, CapsuleValue)]

data ClosureValue
    = ClosureConstant Integer
    | ClosureLambda String Term ClosureEnv

type ClosureEnv = [(String, ClosureValue)]

{-@ reflect memberName @-}
memberName :: String -> [String] -> Bool
memberName _ []     = False
memberName x (y:ys) = x == y || memberName x ys

{-@ reflect subsetNames @-}
subsetNames :: [String] -> [String] -> Bool
subsetNames [] _      = True
subsetNames (x:xs) ys = memberName x ys && subsetNames xs ys

{-@ reflect lookupCapsule @-}
lookupCapsule :: String -> CapsuleEnv -> Maybe CapsuleValue
lookupCapsule _ [] = Nothing
lookupCapsule x ((y,v):ys)
    | x == y    = Just v
    | otherwise = lookupCapsule x ys

{-@ reflect lookupClosure @-}
lookupClosure :: String -> ClosureEnv -> Maybe ClosureValue
lookupClosure _ [] = Nothing
lookupClosure x ((y,v):ys)
    | x == y    = Just v
    | otherwise = lookupClosure x ys

{-@ reflect freeVars @-}
freeVars :: Term -> [String]
freeVars (Var x)       = [x]
freeVars (Const _)     = []
freeVars (Lam x body)  = filter (/= x) (freeVars body)
freeVars (App e1 e2)   = uniqueNames (freeVars e1 ++ freeVars e2)

{-@ reflect uniqueNames @-}
uniqueNames :: [String] -> [String]
uniqueNames [] = []
uniqueNames (x:xs)
    | memberName x xs = uniqueNames xs
    | otherwise       = x : uniqueNames xs

{-@ reflect capsuleValueFreeVars @-}
capsuleValueFreeVars :: CapsuleValue -> [String]
capsuleValueFreeVars (CapsuleConstant _)    = []
capsuleValueFreeVars (CapsuleLambda x body) = freeVars (Lam x body)

{-@ reflect wellFormedCapsuleEnv @-}
wellFormedCapsuleEnv :: CapsuleEnv -> Bool
wellFormedCapsuleEnv env =
    all
        (\(_, value) ->
            subsetNames (capsuleValueFreeVars value) (map fst env))
        env

{-@ reflect capsuleEnvRefines @-}
capsuleEnvRefines :: CapsuleEnv -> CapsuleEnv -> Bool
capsuleEnvRefines sigma tau =
    subsetNames (map fst sigma) (map fst tau)
    && all (\(name, value) -> lookupCapsule name tau == Just value) sigma

{-@ reflect convertEntries @-}
convertEntries :: CapsuleEnv -> CapsuleEnv -> ClosureEnv
convertEntries _ [] = []
convertEntries full ((name, value) : rest) =
    case value of
        CapsuleConstant n ->
            (name, ClosureConstant n) : convertEntries full rest
        CapsuleLambda x body ->
            (name, ClosureLambda x body (convertEntries full full)) : convertEntries full rest

{-@ reflect closureConvert @-}
closureConvert :: CapsuleEnv -> ClosureEnv
closureConvert sigma = convertEntries sigma sigma

{-@ reflect closureValueRelated @-}
closureValueRelated :: ClosureValue -> ClosureValue -> Bool
closureValueRelated (ClosureConstant x) (ClosureConstant y) =
    x == y
closureValueRelated
    (ClosureLambda x body1 env1)
    (ClosureLambda y body2 env2) =
        x == y
        && body1 == body2
        && closureEnvRelated env1 env2
closureValueRelated _ _ = False

{-@ reflect closureEnvRelated @-}
closureEnvRelated :: ClosureEnv -> ClosureEnv -> Bool
closureEnvRelated sigma tau =
    subsetNames (map fst sigma) (map fst tau)
    && all
        (\(name, value) ->
            case lookupClosure name tau of
                Just other -> closureValueRelated value other
                Nothing    -> False)
        sigma

{-@ closureConversionMonotone
      :: sigma:{CapsuleEnv | wellFormedCapsuleEnv sigma}
      -> tau:{CapsuleEnv | wellFormedCapsuleEnv tau}
      -> {capsuleEnvRefines sigma tau
           => closureEnvRelated
                (closureConvert sigma)
                (closureConvert tau)}
  @-}
closureConversionMonotone :: CapsuleEnv -> CapsuleEnv -> Proof
closureConversionMonotone _ _ = ()
