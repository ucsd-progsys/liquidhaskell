{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE FlexibleInstances  #-}
module Language.Fixpoint.Horn.Transformations (
    uniq
  , flatten
  , elim
  , elimPis
  -- , elimKs
  , solveEbs
  , cstrToExpr
) where

import           Language.Fixpoint.Horn.Types
import           Language.Fixpoint.Horn.Info
import qualified Language.Fixpoint.Types      as F
import           Language.Fixpoint.Graph      as FG
import qualified Data.HashMap.Strict          as M
-- import           Control.Monad.Identity
import           Data.String                  (IsString (..))
import           Data.Either                  (partitionEithers)
import qualified Data.Set                     as S
import qualified Data.Graph                   as DG
import           Control.Monad.State
import           Data.Bifunctor               (second)
import           Data.Maybe                   (catMaybes, fromJust, mapMaybe)
import           Language.Fixpoint.Types.Visitor as V
import           System.Console.CmdArgs.Verbosity

-- import Debug.Trace

-- $setup
-- >>> :l src/Language/Fixpoint/Horn/Transformations.hs src/Language/Fixpoint/Horn/Parse.hs
-- >>> :m + *Language.Fixpoint.Horn.Parse
-- >>> import Language.Fixpoint.Parse
-- >>> :set -XOverloadedStrings

{- | flatten removes redundant `and`s and empty conjuncts.

For example:
>>> :{
flatten $ doParse' hCstrP "" "(forall ((VV##15 int) (VV##15 == anf##3)) \
            \      ((and (and \
            \        ($k13 VV##15 anf##3 moo##5) \
            \        (true)))))"
:}
(forall ((VV##15 int) (VV##15 == anf##3)) ((k13 VV##15 anf##3 moo##5)))
-}

class Flatten a where
  flatten :: a -> a

instance Flatten (Cstr a) where
  flatten (CAnd cs) = case flatten cs of
                        [c] -> c
                        cs -> CAnd cs
  flatten (Head p a) = Head (flatten p) a
  flatten (All (Bind x t p) c) = All (Bind x t (flatten p)) (flatten c)
  flatten (Any (Bind x t p) c) = Any (Bind x t (flatten p)) (flatten c)

instance Flatten [Cstr a] where
  flatten (CAnd cs : xs) = flatten cs ++ flatten xs
  flatten (x:xs)
    | Head (Reft p) _ <- fx
    , F.isTautoPred p            = flatten xs
    | otherwise                  = fx:flatten xs
    where fx = flatten x
  flatten [] = []

instance Flatten Pred where
  flatten (PAnd ps) = case flatten ps of
                        [p] -> p
                        ps  -> PAnd ps
  flatten p = p

instance Flatten [Pred] where
  flatten (PAnd ps' : ps) = flatten ps' ++ flatten ps
  flatten (p : ps)
    | Reft e <- fp
    , F.isTautoPred e     = flatten ps
    | otherwise           = fp : flatten ps
    where fp = flatten p
  flatten []              = []

instance Flatten F.Expr where
  flatten (F.PAnd ps) = case flatten ps of
                         [p] -> p
                         ps  -> F.PAnd ps
  flatten p = p

instance Flatten [F.Expr] where
  flatten (F.PAnd ps' : ps) = flatten ps' ++ flatten ps
  flatten (p : ps)
    | F.isTautoPred fp    = flatten ps
    | otherwise           = fp : flatten ps
    where fp = flatten p
  flatten []              = []

type KVEdges = [(FG.CVertex, FG.CVertex, [FG.CVertex])]

-- type Sol a = M.HashMap F.Symbol (Either (Either [[Bind]] (Cstr a)) F.Expr)
------------------------------------------------------------------------------
-- | solveEbs has some preconditions
-- - pi -> k -> pi structure. That is, there are no cycles, and while ks
-- can depend on other ks, pis cannot directly depend on other pis
-- - predicate for exists binder is `true`. This doesn't seem hard to lift,
-- but I just haven't tested it/thought too hard about what the correct
-- behavior in this case is.
-- - There is at least one ebind
solveEbs :: (F.PPrint a) => Query a -> IO (Query a)
------------------------------------------------------------------------------
solveEbs query@(Query _qs _vs c _cons _dist) = if isNNF c then pure query else do
  let normalizedC = simplify $ hornify c
  whenLoud $ putStrLn "Normalized EHC:"
  whenLoud $ putStrLn $ F.showpp normalizedC

  let (Just noExists, _) = split normalizedC -- TODO: fix this and remove pivars from edges below
  let kEdges = buildKvarEdges query noExists
  let acyclicKs = findAcyclicKVars kEdges
  whenLoud $ putStrLn "acyclic kvars:"
  whenLoud $ putStrLn $ F.showpp acyclicKs

  let kvars = boundKvars normalizedC
  let poked = pokec normalizedC
  whenLoud $ putStrLn "Horn pokec:"
  whenLoud $ putStrLn $ F.showpp poked

  let (Just horn, Just side) = split poked
  whenLoud $ putStrLn "Horn split:"
  whenLoud $ putStrLn $ F.showpp (horn, side)

  let pivars = boundKvars poked `S.difference` kvars
  let piSols = M.fromList $ fmap (\pivar -> (pivar, piDefConstr pivar horn)) (S.toList pivars)
  whenLoud $ putStrLn "pi defining constraints:"
  whenLoud $ putStrLn $ F.showpp piSols

  if (S.fromList acyclicKs) /= kvars then error $ show (kvars, acyclicKs, kvars `S.difference` S.fromList acyclicKs) else pure ()

  let (horn', side', piSols') = elimKs' acyclicKs (horn, side, piSols)
  whenLoud $ putStrLn "solved acyclic kvars:"
  whenLoud $ putStrLn $ F.showpp horn'
  whenLoud $ putStrLn $ F.showpp side'
  whenLoud $ putStrLn $ F.showpp piSols'

  let solvedPiCstrs = solPis piSols'
  whenLoud $ putStrLn "solved pis:"
  whenLoud $ putStrLn $ F.showpp solvedPiCstrs

  -- This whole business depends on Stringly-typed invariant that an ebind
  -- n corresponds to a pivar πn. That's pretty bad but I can't think of
  -- a better way to do this.

  -- find solutions to the pivars, put them on the Left of the map
  -- let ns = fst <$> ebs c
  -- let l0 = cLabel horn
  -- let pisols = M.fromList [(piSym n, Left $ Right $ nSol) | n <- ns, Just nSol <- [defs n horn]] -- :: Sol a
  -- whenLoud $ putStrLn "Pisols:"
  -- whenLoud $ putStrLn $ F.showpp $ pisols

  -- find solutions to the kvars, put them on the Right of the map
  -- let ksols = M.fromList [(k, Left $ Left $ sol1 k (scope k horn)) | k <- hvName <$> vs] -- :: Sol

  error "WIP"
  -- let sol = evalState (mapM (lookupSol l0 M.empty . piVar) ns) (ksols <> pisols)
  -- whenLoud $ putStrLn "QE sols:"
  -- let elimSol = M.fromList $ zip (piSym <$> ns) [Head (Reft $ flatten p) l0 | p <- sol]
  -- whenLoud $ putStrLn $ F.showpp elimSol
  -- let kSol = M.mapMaybe (either (either Just (const Nothing)) (const Nothing)) ksols
  -- whenLoud $ putStrLn "kSol:"
  -- whenLoud $ putStrLn $ F.showpp kSol

  -- let hornFinal = hornify $ M.foldrWithKey applyPi horn elimSol
  -- whenLoud $ putStrLn "Final Horn:"
  -- whenLoud $ putStrLn $ F.showpp hornFinal

  -- let sideCstr = M.foldrWithKey applyPi (M.foldrWithKey doelim' side kSol) elimSol
  -- whenLoud $ putStrLn "PreElim Side:"
  -- whenLoud $ putStrLn $ F.showpp sideCstr
  -- let sideEE = hornify $ traceShowId $ elimE undefined sideCstr
  -- whenLoud $ putStrLn "Final Side:"
  -- whenLoud $ putStrLn $ F.showpp sideEE

  -- pure $ (Query qs vs (CAnd [ hornFinal, sideEE ]) cons dist)

-- | Collects the defining constraint for π AKA c in forall n.π => c
-- additionally collects the variable name n
piDefConstr :: F.Symbol -> Cstr a -> ([F.Symbol], Cstr a)
piDefConstr k c = fromJust $ go c
  where
    go (CAnd cs) =
      case mapMaybe go cs of
        [c'] -> Just c'
        _ -> Nothing
    go (All (Bind _ _ (Var k' xs)) c')
      | k == k' = Just (xs, c')
      | otherwise = go c'
    go (All _ c') = go c'
    go _ = Nothing

solPis :: M.HashMap F.Symbol ([F.Symbol], Cstr a) -> M.HashMap F.Symbol Pred
solPis piSols = M.map fromRight $ go (M.toList piSols) (Left <$> piSols)
  where
    go ((pi, (xs, c)):pis) piSols = go pis $ M.insert pi (Right solved) piSols
      where solved = qe xs $ solPi (S.singleton pi) piSols c
    go [] piSols = piSols

    fromRight (Right x) = x
    fromRight _ = error "fromRight failed"

solPi :: S.Set F.Symbol -> M.HashMap F.Symbol (Either ([F.Symbol], Cstr a) Pred) -> Cstr a -> Cstr a
solPi _ _ c@Head{} = c
solPi visited piSols (CAnd cs) = CAnd $ solPi visited piSols <$> cs
solPi visited piSols (All (Bind x t (Var pi _)) c)
  | S.member pi visited = solPi visited piSols c
  | otherwise = All (Bind x t p) (solPi visited piSols c)
      where p = case (piSols M.! pi) of
                  Left (n, defC) -> qe n $ solPi (S.insert pi visited) piSols defC
                  Right defP -> defP
solPi visited piSols (All b c) = All b (solPi visited piSols c)
solPi _ _ Any{} = error "exists should not be present in piSols"

-- elimE :: Sol a -> Cstr a -> Cstr a
-- elimE m (All b c) = All b (elimE m c)
-- elimE m (CAnd cs) = CAnd (elimE m <$> cs)
-- elimE _m p@Head{} = p
-- -- need to QE inside here first
-- elimE _m (Any (Bind x _ _) (Head p l)) = Head (F.subst1 p (x,e)) l
--     where e = fromMaybe F.PTrue $ findSolP x p
-- elimE _m (Any _ _) = error "oops"

hornify :: Cstr a -> Cstr a
hornify (Head (PAnd ps) a) = CAnd (flip Head a <$> ps')
  where ps' = let (ks, qs) = split [] [] (flatten ps) in PAnd qs : ks

        split kacc pacc ((Var x xs):qs) = split ((Var x xs):kacc) pacc qs
        split kacc pacc (q:qs) = split kacc (q:pacc) qs
        split kacc pacc [] = (kacc, pacc)
hornify (Head (Reft r) a) = CAnd (flip Head a <$> ((Reft $ F.PAnd ps):(Reft <$> ks)))
  where (ks, ps) = split [] [] $ F.splitPAnd r
        split kacc pacc (r@F.PKVar{}:rs) = split (r:kacc) pacc rs
        split kacc pacc (r:rs) = split kacc (r:pacc) rs
        split kacc pacc [] = (kacc,pacc)
hornify (Head h a) = Head h a
hornify (All b c) = All b $ hornify c
hornify (Any b c) = Any b $ hornify c
hornify (CAnd cs) = CAnd $ hornify <$> cs

instance F.Subable Bind where
    syms = undefined
    substa = undefined
    substf = undefined
    subst su (Bind x t p) = (Bind x t (F.subst su p))

-- instance F.Subable Pred where
--    syms = undefined
--    substa = undefined
--    substf = undefined
--    subst su p = substP su p

{- move to FP! -}
instance F.Subable Pred where
  syms (Reft e)   = F.syms e
  syms (Var _ xs) = xs
  syms (PAnd ps)  = concatMap F.syms ps

  substa f (Reft e)   = Reft  (F.substa f      e)
  substa f (Var k xs) = Var k (F.substa f <$> xs)
  substa f (PAnd ps)  = PAnd  (F.substa f <$> ps)

  subst su (Reft  e)  = Reft  (F.subst su      e)
  subst su (PAnd  ps) = PAnd  (F.subst su <$> ps)
  subst su (Var k xs) = Var k (F.subst su <$> xs)

  substf f (Reft  e)  = Reft  (F.substf f      e)
  substf f (PAnd  ps) = PAnd  (F.substf f <$> ps)
  substf f (Var k xs) = Var k (F.substf f <$> xs)

  subst1 (Reft  e)  su = Reft  (F.subst1 e su)
  subst1 (PAnd  ps) su = PAnd  [F.subst1 p su | p <- ps]
  subst1 (Var k xs) su = Var k [F.subst1 x su | x <- xs]

-- substP :: F.Subst -> Pred -> Pred
-- substP su (Reft e)   = Reft (F.subst su e)
-- substP su (PAnd ps)  = PAnd (substP su <$> ps)
-- substP su (Var k xs) = Var k (F.subst su xs)

------------------------------------------------------------------------------
{- |
>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind01.smt2"
>>> F.pprint $ pokec (qCstr q)
(and
 (forall ((m int) (true))
  (and
   (forall ((x1 int) (πx1 x1))
    (and
     (forall ((v int) (v == m + 1))
      (((v == x1))))
     (forall ((v int) (v == x1 + 1))
      (((v == 2 + m))))))
   (exists ((x1 int) (true))
    ((πx1 x1))))))

>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
>>> F.pprint $ pokec (qCstr q)
(and
 (forall ((m int) (true))
  (forall ((z int) (z == m - 1))
   (and
    (forall ((v1 int) (v1 == z + 2))
     ((k v1)))
    (and
     (forall ((x1 int) (πx1 x1))
      (and
       (forall ((v2 int) (k v2))
        (((v2 == x1))))
       (forall ((v3 int) (v3 == x1 + 1))
        (((v3 == m + 2))))))
     (exists ((x1 int) (true))
      ((πx1 x1))))))))

>>> let c = doParse' hCstrP "" "(forall ((a Int) (p a)) (exists ((b Int) (q b)) (and (($k a)) (($k b)))))"
>>> F.pprint $ pokec c
(forall ((a int) (p a))
 (and
  (forall ((b int) (πb b))
   (and
    ((k a))
    ((k b))))
  (exists ((b int) (q b))
   ((πb b)))))
-}

-- ebs :: Cstr a -> [(F.Symbol, F.Sort)]
-- ebs (Head _ _) = []
-- ebs (CAnd cs) = ebs =<< cs
-- ebs (All _ c) = ebs c
-- ebs (Any (Bind x t _) c) = (x,t) : ebs c

pokec :: Cstr a -> Cstr a
pokec = go mempty
  where
    go _ (Head c l) = Head c l
    go xs (CAnd c)   = CAnd (go xs <$> c)
    go xs (All b c2) = All b $ go ((bSym b):xs) c2
    go xs (Any b@(Bind x t p) c2) = CAnd [All b' $ CAnd [Head p l, go (x:xs) c2], Any b (Head pi l)]
      -- TODO: actually use the renamer?
      where
        b' = Bind x t pi
        pi = piVar x xs
        l  = cLabel c2

piVar :: F.Symbol -> [F.Symbol] -> Pred
piVar x xs = Var (piSym x) (x:xs)

piSym :: F.Symbol -> F.Symbol
piSym s = fromString $ "π" ++ F.symbolString s

------------------------------------------------------------------------------
-- Now split the poked constraint into the side conditions and the meat of
-- the constraint

{-|
>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind01.smt2"
>>> F.pprint $ qCstr q
(and
 (forall ((m int) (true))
  (exists ((x1 int) (true))
   (and
    (forall ((v int) (v == m + 1))
     (((v == x1))))
    (forall ((v int) (v == x1 + 1))
     (((v == 2 + m))))))))

>>> let (Just noside, Just side) = split $ pokec $ qCstr q
>>> F.pprint side
(forall ((m int) (true))
 (exists ((x1 int) (true))
  ((πx1 x1))))
>>> F.pprint noside
(forall ((m int) (true))
 (forall ((x1 int) (πx1 x1))
  (and
   (forall ((v int) (v == m + 1))
    (((v == x1))))
   (forall ((v int) (v == x1 + 1))
    (((v == 2 + m)))))))


>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
>>> F.pprint $ qCstr q
(and
 (forall ((m int) (true))
  (forall ((z int) (z == m - 1))
   (and
    (forall ((v1 int) (v1 == z + 2))
     ((k v1)))
    (exists ((x1 int) (true))
     (and
      (forall ((v2 int) (k v2))
       (((v2 == x1))))
      (forall ((v3 int) (v3 == x1 + 1))
       (((v3 == m + 2))))))))))

>>> let (Just noside, Just side) = split $ pokec $ qCstr q
>>> F.pprint side
(forall ((m int) (true))
 (forall ((z int) (z == m - 1))
  (exists ((x1 int) (true))
   ((πx1 x1)))))
>>> F.pprint noside
(forall ((m int) (true))
 (forall ((z int) (z == m - 1))
  (and
   (forall ((v1 int) (v1 == z + 2))
    ((k v1)))
   (forall ((x1 int) (πx1 x1))
    (and
     (forall ((v2 int) (k v2))
      (((v2 == x1))))
     (forall ((v3 int) (v3 == x1 + 1))
      (((v3 == m + 2)))))))))
-}

split :: Cstr a -> (Maybe (Cstr a), Maybe (Cstr a))
split (CAnd cs) = (andMaybes nosides, andMaybes sides)
  where (nosides, sides) = unzip $ split <$> cs
split (All b c) = (All b <$> c', All b <$> c'')
    where (c',c'') = split c
split c@Any{} = (Nothing, Just c)
split c@Head{} = (Just c, Nothing)

andMaybes :: [Maybe (Cstr a)] -> Maybe (Cstr a)
andMaybes cs = case catMaybes cs of
                 [] -> Nothing
                 [c] -> Just c
                 cs -> Just $ CAnd cs
------------------------------------------------------------------------------
{- |
>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind01.smt2"
>>> let (Just noside, Just side) = split $ pokec $ qCstr q
>>> F.pprint $ elimPis ["x1"] (noside, side )
(forall ((m int) (true))
 (forall ((x1 int) (forall [v : int]
  . v == m + 1 => v == x1
&& forall [v : int]
     . v == x1 + 1 => v == 2 + m))
  (and
   (forall ((v int) (v == m + 1))
    (((v == x1))))
   (forall ((v int) (v == x1 + 1))
    (((v == 2 + m))))))) : (forall ((m int) (true))
                            (exists ((x1 int) (true))
                             ((forall [v : int]
                                 . v == m + 1 => v == x1
                               && forall [v : int]
                                    . v == x1 + 1 => v == 2 + m))))

>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
>>> let (Just noside, Just side) = split $ pokec $ qCstr q
>>> F.pprint $ elimPis ["x1"] (noside, side )
(forall ((m int) (true))
 (forall ((z int) (z == m - 1))
  (and
   (forall ((v1 int) (v1 == z + 2))
    ((k v1)))
   (forall ((x1 int) (forall [v2 : int]
  . $k[fix$36$$954$arg$36$k$35$1:=v2] => v2 == x1
&& forall [v3 : int]
     . v3 == x1 + 1 => v3 == m + 2))
    (and
     (forall ((v2 int) (k v2))
      (((v2 == x1))))
     (forall ((v3 int) (v3 == x1 + 1))
      (((v3 == m + 2))))))))) : (forall ((m int) (true))
                                 (forall ((z int) (z == m - 1))
                                  (exists ((x1 int) (true))
                                   ((forall [v2 : int]
                                       . $k[fix$36$$954$arg$36$k$35$1:=v2] => v2 == x1
                                     && forall [v3 : int]
                                          . v3 == x1 + 1 => v3 == m + 2)))))

-}

elimPis :: [F.Symbol] -> (Cstr a, Cstr a) -> (Cstr a, Cstr a)
elimPis [] cc = cc
elimPis (n:ns) (horn, side) = elimPis ns (apply horn, apply side)
-- TODO: handle this error?
  where Just nSol = defs n horn
        apply = applyPi (piSym n) nSol

-- TODO: PAnd may be a problem
applyPi :: F.Symbol -> Cstr a -> Cstr a -> Cstr a
applyPi k defs (All (Bind x t (Var k' _xs)) c)
  | k == k'
  = All (Bind x t (Reft $ cstrToExpr defs)) c
applyPi k bp (CAnd cs)
  = CAnd $ applyPi k bp <$> cs
applyPi k bp (All b c)
  = All b (applyPi k bp c)
applyPi k bp (Any b c)
  = Any b (applyPi k bp c)
applyPi k defs (Head (Var k' _xs) a)
  | k == k'
  -- what happens when pi's appear inside the defs for other pis?
  -- this shouldn't happen because there should be a strict
  --  pi -> k -> pi structure
  -- but that comes from the typing rules, not this format, so let's make
  -- it an invariant of solveEbs above
  = Head (Reft $ cstrToExpr defs) a
applyPi _ _ (Head p a) = Head p a

-- | The defining constraints for a pivar
--
-- The defining constraints are those that bound the value of pi_x.
--
-- We're looking to lower-bound the greatest solution to pi_x.
-- If we eliminate pivars before we eliminate kvars (and then apply the kvar
-- solutions to the side conditions to solve out the pis), then we know
-- that the only constraints that mention pi in the noside case are those
-- under the corresponding pivar binder. A greatest solution for this pivar
-- can be obtained as the _weakest precondition_ of the constraints under
-- the binder
--
-- The greatest Pi that implies the constraint under it is simply that
-- constraint itself. We can leave off constraints that don't mention n,
-- see https://photos.app.goo.gl/6TorPprC3GpzV8PL7
--
-- Actually, we can really just throw away any constraints we can't QE,
-- can't we?

{- |
>>> :{
let c = doParse' hCstrP "" "\
\(forall ((m int) (true))                  \
\ (forall ((x1 int) (and (true) (πx1 x1))) \
\  (and                                    \
\   (forall ((v int) (v == m + 1))         \
\    (((v == x1))))                        \
\   (forall ((v int) (v == x1 + 1))        \
\    (((v == 2 + m)))))))"
:}

>>> F.pprint $ defs "x1" c
Just (and
      (forall ((v int) (v == m + 1))
       ((v == x1)))
      (forall ((v int) (v == x1 + 1))
       ((v == 2 + m))))

>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
>>> let (Just noside, _) = split $ pokec $ qCstr q
>>> F.pprint $ defs "x1" noside
Just (and
      (forall ((v2 int) (k v2))
       ((v2 == x1)))
      (forall ((v3 int) (v3 == x1 + 1))
       ((v3 == m + 2))))

-}

defs :: F.Symbol -> Cstr a -> Maybe (Cstr a)
defs x (CAnd cs) = andMaybes $ defs x <$> cs
defs x (All (Bind x' _ _) c)
  | x' == x
  = pure c
defs x (All _ c) = defs x c
defs _ (Head _ _) = Nothing
defs _ (Any _ _) =  error "defs should be run only after noside and poke"

cstrToExpr :: Cstr a -> F.Expr
cstrToExpr (Head p _) = predToExpr p
cstrToExpr (CAnd cs) = F.PAnd $ cstrToExpr <$> cs
cstrToExpr (All (Bind x t p) c) = F.PAll [(x,t)] $ F.PImp (predToExpr p) $ cstrToExpr c
cstrToExpr (Any (Bind x t p) c) = F.PExist [(x,t)] $ F.PImp (predToExpr p) $ cstrToExpr c

predToExpr :: Pred -> F.Expr
predToExpr (Reft e) = e
predToExpr (Var k xs) = F.PKVar (F.KV k) (F.Su $ M.fromList su)
  where su = zip (kargs k) (F.EVar <$> xs)
predToExpr (PAnd ps) = F.PAnd $ predToExpr <$> ps

------------------------------------------------------------------------------
{- |
>>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
>>> let (Just noside, Just side) = split $ pokec $ qCstr q
>>> F.pprint $ elimKs ["k"] $ elimPis ["x1"] (noside, side)
(forall ((m int) (true))
 (forall ((z int) (z == m - 1))
  (and
   (forall ((v1 int) (v1 == z + 2))
    ((true)))
   (forall ((x1 int) (forall [v2 : int]
  . exists [v1 : int]
      . (v2 == v1)
        && v1 == z + 2 => v2 == x1
&& forall [v3 : int]
     . v3 == x1 + 1 => v3 == m + 2))
    (and
     (forall ((v1 int) (v1 == z + 2))
      (forall ((v2 int) (v2 == v1))
       (((v2 == x1)))))
     (forall ((v3 int) (v3 == x1 + 1))
      (((v3 == m + 2))))))))) : (forall ((m int) (true))
                                 (forall ((z int) (z == m - 1))
                                  (exists ((x1 int) (true))
                                   ((forall [v2 : int]
                                       . exists [v1 : int]
                                           . (v2 == v1)
                                             && v1 == z + 2 => v2 == x1
                                     && forall [v3 : int]
                                          . v3 == x1 + 1 => v3 == m + 2)))))
-}
-- elimKs :: [F.Symbol] -> (Cstr a, Cstr a) -> (Cstr a, Cstr a)
-- elimKs [] cc = cc
-- elimKs (k:ks) (horn, side) = elimKs ks (horn', side')
--   where sol = sol1 k (scope k horn)
--         -- Eliminate Kvars inside Cstr inside horn, and in Expr (under
--         -- quantifiers waiting to be eliminated) in both.
--         horn' = doelim' k sol . doelim k sol $ horn
--         side' = doelim' k sol $ side

-- TODO: make this elimKs and update tests for elimKs
-- | Takes noside, side, piSols and solves a set of kvars in them
elimKs' :: [F.Symbol]
        -> (Cstr a, Cstr a, M.HashMap F.Symbol ([F.Symbol], Cstr a))
        -> (Cstr a, Cstr a, M.HashMap F.Symbol ([F.Symbol], Cstr a))
elimKs' [] cstrs = cstrs
elimKs' (k:ks) (noside, side, piSols) = elimKs' ks (noside', side', piSols')
  where
    sol = sol1 k (scope k noside)
    noside' = simplify $ doelim k sol noside
    side' = simplify $ doelim k sol side
    piSols' = (second $ simplify . (doelim k sol)) <$> piSols


-- doelim' :: F.Symbol -> [[Bind]] -> Cstr a -> Cstr a
-- doelim' k bss (CAnd cs) = CAnd $ doelim' k bss <$> cs
-- doelim' k bss (Head p a) = Head (tx k bss p) a
-- doelim' k bss (All (Bind x t p) c) = All (Bind x t $ tx k bss p) (doelim' k bss c)
-- doelim' k bss (Any (Bind x t p) c) = Any (Bind x t $ tx k bss p) (doelim' k bss c)

-- [NOTE-elimK-positivity]:
--
-- uh-oh I suspect this traversal is WRONG. We can build an
-- existentialPackage as a solution to a K in a negative position, but in
-- the *positive* position, the K should be solved to FALSE.
--
-- Well, this may be fine --- semantically, this is all the same, but the
-- exists in the positive positions (which will stay exists when we go to
-- prenex) may give us a lot of trouble during _quantifier elimination_
-- tx :: F.Symbol -> [[Bind]] -> Pred -> Pred
-- tx k bss = trans (defaultVisitor { txExpr = existentialPackage, ctxExpr = ctxKV }) M.empty ()
--   where
--   splitBinds xs = unzip $ (\(Bind x t p) -> ((x,t),p)) <$> xs
--   cubeSol su (Bind _ _ (Reft eqs):xs)
--     | (xts, es) <- splitBinds xs
--     = F.PExist xts $ F.PAnd (F.subst su eqs : map predToExpr es)
--   cubeSol _ _ = error "cubeSol in doelim'"
--   -- This case is a HACK. In actuality, we need some notion of
--   -- positivity...
--   existentialPackage _ (F.PAll _ (F.PImp _ (F.PKVar (F.KV k') _)))
--     | k' == k
--     = F.PTrue
--   existentialPackage m (F.PKVar (F.KV k') su)
--     | k' == k
--     , M.lookupDefault 0 k m < 2
--     = F.PAnd $ cubeSol su . reverse <$> bss
--   existentialPackage _ e = e
--   ctxKV m (F.PKVar (F.KV k) _) = M.insertWith (+) k 1 m
--   ctxKV m _ = m

-- Visitor only visit Exprs in Pred!
instance V.Visitable Pred where
  visit v c (PAnd ps) = PAnd <$> mapM (visit v c) ps
  visit v c (Reft e) = Reft <$> visit v c e
  visit _ _ var      = pure var

instance V.Visitable (Cstr a) where
  visit v c (CAnd cs) = CAnd <$> mapM (visit v c) cs
  visit v c (Head p a) = Head <$> visit v c p <*> pure a
  visit v ctx (All (Bind x t p) c) = All <$> (Bind x t <$> visit v ctx p) <*> visit v ctx c
  visit v ctx (Any (Bind x t p) c) = All <$> (Bind x t <$> visit v ctx p) <*> visit v ctx c

------------------------------------------------------------------------------
-- | Quantifier elimination for use with implicit solver
-- qe :: Cstr a -> Cstr a
------------------------------------------------------------------------------
-- Initially this QE seemed straightforward, and does seem so in the body:
--
--    \-/ v . v = t -> r
--    ------------------
--          r[t/v]
--
-- And this works. However, the mixed quantifiers get pretty bad in the
-- side condition, which generally looks like
--    forall a1 ... an . exists n . forall v1 . ( exists karg . p ) => q
--

-- NEW STRATEGY: look under each FORALL, bottom up, compile a list of all equalities that
-- are negative, and apply some relevant one to the whole thinger.
--
-- we do first need to make the foralls from exists... so instead let's
-- just start out with foralls in doElim. They're in the wrong polarity,
-- but that's not visible from the other side of QE, so that's fine.
------------------------------------------------------------------------------
-- Now, we go through each pivar, and try to do QE in it. If there's
-- a Pi or a kvar under it, then we need to go and get the solution.
-- Since we're doing this SEPARATELY from the AD search, we can memoize.
-- In fact, we have to, because at the end of the day, we do want a
-- fully solved map.
--
-- QE:
--   (given some constraint c from an unsolved pi, we want to squash it into an expr)
--   if it's head -> if head is a kvar then lookup the kvarsol for these args and QE that
--                -> if head is a pred return that expr
--                -> if head is a pand recursive and conjunct
--   if it's any --> throw an error?
--   if it's forall equality => pred         (how do we actually find the
--     QE in pred, then apply the equality   equalities?)
--   if it's forall kvar => pred
--     lookup and then QE
--   if it's And
--      recurse and then conjunct
--
-- lookup recursively:
--   (when I want the solution for some k or pivar `x`)
--   lookup the Cstr that solves it
--   if it's an unsolved pi
--     run QE on the cstr
--     store it
--   return it

-- | Users of qe must ensure well-formedness
qe :: [F.Symbol] -> Cstr a -> Pred
qe ns c = PAnd $ ps
  where
    xs = (S.fromList ns) `S.union` (boundVars c)
    eqs = collectEqualities xs c
    ps = rewriteWithEqualities xs eqs ns (dropGuards c)

dropGuards :: Cstr a -> [Pred]
dropGuards (Head p _) = [p]
dropGuards (CAnd cs) = mconcat $ dropGuards <$> cs
dropGuards (All _ c) = dropGuards c
dropGuards Any{} = error "not allowed"

rewriteWithEqualities :: S.Set F.Symbol -> [(F.Symbol, F.Expr)] -> [F.Symbol] -> [Pred] -> [Pred]
rewriteWithEqualities xs equalities ns ps = argEqualities <> (F.subst su <$> ps)
  where
    argEqualities = map (\n -> Reft (F.PAtom F.Eq (F.EVar n) (F.subst su (F.EVar n)))) ns
    su = F.mkSubst $ buildSubst eqs

    eqGraph = equalityGraph xs equalities
    eqs = concatMap (\case
                        DG.AcyclicSCC eq -> [eq]
                        DG.CyclicSCC eqs -> eqs) eqGraph

    buildSubst [] = []
    buildSubst ((x, e):eqs) = (x, e):(buildSubst eqs')
      where
        eqs' = foldr (\(x', e') eqs' -> rewriteEq x e x' e' <> eqs') [] eqs

    rewriteEq x e x' e' = case (left, right) of
      (F.EVar y, e) | y == x', e == e' -> [(x', e')]
      _ -> extractEquality xs left right
      where
        left = F.subst1 (F.EVar x') (x, e)
        right = F.subst1 e' (x, e)

equalityGraph :: S.Set F.Symbol -> [(F.Symbol, F.Expr)] -> [DG.SCC (F.Symbol, F.Expr)]
equalityGraph xs eqs = DG.stronglyConnComp (go eqs)
  where
    go [] = []
    go ((x, F.EVar y):eqs)
      | S.member y xs = ((x, F.EVar y), x, [y]):(go eqs)
    go ((x, e):eqs) = ((x, e), x, []):(go eqs)

collectEqualities :: S.Set F.Symbol -> Cstr a -> [(F.Symbol, F.Expr)]
collectEqualities xs c = go c
  where
    go (Head p _) = goP p
    go (CAnd cs) = mconcat $ go <$> cs
    go (All (Bind _ _ p) c) = goP p <> go c
    go Any{} = error "existentials shouldn't be present"

    goP (Reft e) = goE e
    goP (PAnd ps) = mconcat $ goP <$> ps
    goP _ = mempty

    goE (F.PAtom F.Eq left right) = extractEquality xs left right
    goE (F.PAnd es) = mconcat $ goE <$> es
    goE _ = mempty

extractEquality :: S.Set F.Symbol -> F.Expr -> F.Expr -> [(F.Symbol, F.Expr)]
extractEquality xs left right
  | F.EVar x <- left, F.EVar y <- right, x == y = []
  | F.EVar x <- left, F.EVar y <- right
  , S.member x xs, S.member y xs = [(x, right), (y, left)]
  | F.EVar x <- left
  , S.member x xs = [(x, right)]
  | F.EVar x <- right
  , S.member x xs = [(x, left)]
  | otherwise = mempty

-- qe' :: S.Set F.Symbol -> [(F.Symbol, F.Expr)] -> Cstr a -> Pred
-- qe :: M.HashMap F.Symbol Integer -> Cstr a -> State (Sol a) F.Expr
-- qe m c = do
--  c' <- qe' m c
--  pure $ trace (show c ++ " =[qe]=>  " ++ show c') c'

-- qe' :: M.HashMap F.Symbol Integer -> Cstr a -> State (Sol a) F.Expr
-- qe' m (Head p l)           = lookupSol l m p
-- qe' m (CAnd cs)            = F.PAnd <$> mapM (qe m) cs
-- qe' m (All (Bind x _ p) c) = forallElim x <$> lookupSol (cLabel c) m p <*> qe m c
-- qe' _ Any{}                = error "QE for Any????"

-- forallElim :: (F.Subable t, Visitable t) => F.Symbol -> t -> F.Expr -> F.Expr
-- forallElim x p e = forallElim' x eqs p e
--   where
--   eqs = fold eqVis () [] p
--   eqVis             = (defaultVisitor :: Visitor F.Expr t) { accExpr = kv' }
--   kv' _ e@(F.PAtom F.Eq a b)
--     | F.EVar x == a || F.EVar x == b
--     = [e]
--   kv' _ _                    = []

-- forallElim' :: F.Subable a => F.Symbol -> [F.Expr] -> a -> F.Expr -> F.Expr
-- forallElim' x (F.PAtom F.Eq a b : _) _ e
--   | F.EVar x == a
--   = F.subst1 e (x,b)
--   | F.EVar x == b
--   = F.subst1 e (x,a)
-- forallElim' x _ p e
--   | x `notElem` F.syms p && x `notElem` F.syms e  = e
-- forallElim' x _ _ e = runIdentity $ flip mapMExpr e $ \case
--     p@F.PAtom{} -> if x `notElem` F.syms p then pure p else pure F.PTrue
--    -- TODO: where else might this appear? App, KVar?
--     p -> pure p

-- lookupSol :: a -> M.HashMap F.Symbol Integer -> Pred -> State (Sol a) F.Expr
-- lookupSol l m c = do
--  c' <- lookupSol' l m c
--  pure $ trace (show m ++ show c ++ " =[l]=> " ++ show c')  c'

-- lookupSol' :: a -> M.HashMap F.Symbol Integer -> Pred -> State (Sol a) F.Expr
-- lookupSol' l m (Var x xs) =
--   let n = M.lookupDefault 0 x m in
--   if n > 0 then pure $ predToExpr (Var x xs) else
--   let m' = M.insert x (n+1) m in gets (M.lookup x) >>= \case
--     -- Memoize only the solutions to Pivars, because they don't depend on args
--     (Just (Left (Right sol))) -> do
--       sol <- qe m' sol
--       -- modify $ M.insert x $ Right $ sol
--       pure sol
--     (Just (Left (Left sol))) ->
--       qe m' $ doelim2 l sol (Var x xs)

--     (Just (Right sol)) -> pure sol
--     Nothing -> error $ "no soution to Var " ++ F.symbolString x

-- lookupSol' _ _ (Reft e) = pure e
-- lookupSol' l m (PAnd ps) = F.PAnd <$> mapM (lookupSol l m) ps

-- findSolP :: F.Symbol -> Pred -> Maybe F.Expr
-- findSolP x (Reft e) = findSolE x e
-- findSolP x (PAnd (p:ps)) = findSolP x p <> findSolP x (PAnd ps)
-- findSolP _ _ = error "findSolP KVar"

-- findSolE :: F.Symbol -> F.Expr -> Maybe F.Expr
-- findSolE x (F.PAtom F.Eq (F.EVar y) e) | x == y = Just e
-- findSolE x (F.PAtom F.Eq e (F.EVar y)) | x == y = Just e
-- findSolE x (F.PAnd (e:es)) = findSolE x e <> findSolE x (F.PAnd es)
-- findSolE _ _ = Nothing

-- This solution is "wrong" ... forall should be exists and implies should
-- be and, but it's fine because that doesn't matter to QE above
-- doelim2 :: a -> [[Bind]] -> Pred -> Cstr a
-- doelim2 l bss (Var k xs)
--   = mkAnd $ cubeSol . reverse <$> bss
--   where su = F.Su $ M.fromList $ zip (kargs k) (F.EVar <$> xs)
--         mkAnd [c] = c
--         mkAnd cs = CAnd cs
--         cubeSol ((Bind _ _ (Reft eqs)):xs) =
--           foldl (flip All) (Head (Reft $ F.subst su eqs) l) xs
--         cubeSol _ = error "internal error"
-- doelim2 l _ p = Head p l

------------------------------------------------------------------------------
-- | uniq makes sure each binder has a unique name
------------------------------------------------------------------------------
type RenameMap = M.HashMap F.Symbol Integer

uniq :: Cstr a -> Cstr a
uniq c = evalState (uniq' c) M.empty

uniq' :: Cstr a -> State RenameMap (Cstr a)
uniq' (Head c a) = Head <$> gets (rename c) <*> pure a
uniq' (CAnd c) = CAnd <$> mapM uniq' c
uniq' (All b c2) = do
    b' <- uBind b
    All b' <$> uniq' c2
uniq' (Any b c2) = do
    b' <- uBind b
    Any b' <$> uniq' c2

uBind :: Bind -> State RenameMap Bind
uBind (Bind x t p) = do
   x' <- uVariable x
   Bind x' t <$> gets (rename p)

uVariable :: IsString a => F.Symbol -> State RenameMap a
uVariable x = do
   i <- gets (M.lookupDefault (-1) x)
   modify (M.insert x (i+1))
   pure $ numSym x (i+1)

rename :: Pred -> RenameMap -> Pred
rename e m = substPred (M.mapWithKey numSym m) e

numSym :: IsString a => F.Symbol -> Integer -> a
numSym s 0 = fromString $ F.symbolString s
numSym s i = fromString $ F.symbolString s ++ "#" ++ show i

substPred :: M.HashMap F.Symbol F.Symbol -> Pred -> Pred
substPred su (Reft e) = Reft $ F.subst (F.Su $ F.EVar <$> su) e
substPred su (PAnd ps) = PAnd $ substPred su <$> ps
substPred su (Var k xs) = Var k $ upd <$> xs
  where upd x = M.lookupDefault x x su

------------------------------------------------------------------------------
-- | elim solves all of the KVars in a Cstr (assuming no cycles...)
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- (and (forall ((x int) (x > 0)) (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0))))))
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- (and (forall ((x int) (x > 0)) (and (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0)))) (forall ((z int) (z > 100)) (forall ((v int) (v == x + z)) ((v > 100)))))))
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- (and (forall ((x int) (x > 0)) (and (forall ((y int) (y > x + 100)) (forall ((v int) (v == x + y)) ((true)))) (forall ((y int) (y > x + 100)) (forall ((v int) (v == x + y)) (forall ((z int) (z == v)) (forall ((v int) (v == x + z)) ((v > 100)))))))))
------------------------------------------------------------------------------
elim :: Cstr a -> Cstr a
------------------------------------------------------------------------------
elim c = if S.null $ boundKvars res then res else error "called elim on cyclic constraint"
  where
  res = S.foldl elim1 c (boundKvars c)

elim1 :: Cstr a -> F.Symbol -> Cstr a
-- Find a `sol1` solution to a kvar `k`, and then subsitute in the solution for
-- each rhs occurrence of k.
elim1 c k = simplify $ doelim k sol c
  where sol = sol1 k (scope k c)

-- |
-- >>> sc <- scope "k0" . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sc
-- (forall ((x ... (and (forall ((y ... (forall ((v ... ((k0 v)))) (forall ((z ...

-- scope prunes out branches that don't have k
-- and removes assumptions that appear over every instance of k in guard position
scope :: F.Symbol -> Cstr a -> Cstr a
scope k cstr = go $ fromJust (prune k cstr) -- TODO: is it safe to fail if k doesn't appear in the head?
  where
    go (All _ c') = c'
    go c = c

prune :: F.Symbol -> Cstr a -> Maybe (Cstr a)
prune k (CAnd cs) = if null cs' then Nothing else Just $ CAnd cs'
  where cs' = mapMaybe (prune k) cs
prune k c@(Head (Var k' _) _)
  | k == k' = Just c
  | otherwise = Nothing
prune _ Head{} = Nothing
prune k (All b c) = do
  c' <- prune k c
  pure (All b c')
prune _ Any{} = error "existential binders should not be around during kvar elim"

-- | A solution is a Hyp of binders (including one anonymous binder
-- that I've singled out here).
-- (What does Hyp stand for? Hypercube? but the dims don't line up...)
--
-- >>> c <- qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sol1 ("k0") (scope "k0" c)
-- [[((y int) (y > x + 100)),((v int) (v == x + y)),((_ bool) (κarg$k0#1 == v))]]
-- >>> c <- qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test03.smt2"
-- >>> sol1 ("k0") (scope "k0" c)
-- [[((x int) (x > 0)),((v int) (v == x)),((_ bool) (κarg$k0#1 == v))],[((y int) (k0 y)),((v int) (v == y + 1)),((_ bool) (κarg$k0#1 == v))]]
-- >>> let c = doParse' hCstrP "" "(forall ((a Int) (p a)) (forall ((b Int) (q b)) (and (($k a)) (($k b)))))"
-- >>> sol1 "k" c
-- [[((a int) (p a)),((b int) (q b)),((_ bool) (κarg$k#1 == a))],[((a int) (p a)),((b int) (q b)),((_ bool) (κarg$k#1 == b))]]

-- Naming conventions:
--  - `b` is a binder `forall . x:t .p =>`
--  - `bs` is a list of binders, or a "cube" that tracks all of the
--     information on the rhs of a given constraint
--  - `bss` is a Hyp, that tells us the solution to a Var, that is,
--     a collection of cubes that we'll want to disjunct

sol1 :: F.Symbol -> Cstr a -> [([Bind], [F.Expr])]
sol1 k (CAnd cs) = sol1 k =<< cs
sol1 k (All b c) = (\(bs, eqs) -> (b:bs, eqs)) <$> sol1 k c
sol1 k (Head (Var k' ys) _) | k == k'
  = [([], zipWith (F.PAtom F.Eq) (F.EVar <$> xs) (F.EVar <$> ys))]
  where xs = zipWith const (kargs k) ys
sol1 _ (Head _ _) = []
sol1 _ (Any _ _) =  error "ebinds don't work with old elim"

kargs :: F.Symbol -> [F.Symbol]
kargs k = fromString . (("κarg$" ++ F.symbolString k ++ "#") ++) . show <$> [1..]

-- |
-- >>> LET c = doParse' hCstrP "" "(forall ((z Int) ($k0 z)) ((z = x)))"
-- >>> doelim "k0" [[Bind "v" F.boolSort (Reft $ F.EVar "v"), Bind "_" F.boolSort (Reft $ F.EVar "donkey")]]  c
-- (forall ((v bool) (v)) (forall ((z int) (donkey)) ((z == x))))

doelim :: F.Symbol -> [([Bind], [F.Expr])] -> Cstr a -> Cstr a
doelim k bp (CAnd cs)
  = CAnd $ doelim k bp <$> cs
doelim k bss (All (Bind x t p) c) =
  case findKVarInGuard k p of
    Right _ -> All (Bind x t p) (doelim k bss c)
    Left (kvars, preds) -> demorgan x t kvars preds (doelim k bss c) bss
  where
    demorgan :: F.Symbol -> F.Sort -> [(F.Symbol, [F.Symbol])] -> [Pred] -> Cstr a -> [([Bind], [F.Expr])] -> Cstr a
    demorgan x t kvars preds c bss = mkAnd $ cubeSol <$> bss
      where su = F.Su $ M.fromList $ concat $ map (\(k, xs) -> zip (kargs k) (F.EVar <$> xs)) kvars
            mkAnd [c] = c
            mkAnd cs = CAnd cs
            cubeSol ((b:bs), eqs) = All b $ cubeSol (bs, eqs)
            cubeSol ([], eqs) = All (Bind x t (PAnd $ (Reft <$> F.subst su eqs) ++ (F.subst su <$> preds))) c
doelim k _ (Head (Var k' _) a)
  | k == k'
  = Head (Reft F.PTrue) a
doelim _ _ (Head p a) = Head p a

doelim k bss (Any (Bind x t p) c) =
  case findKVarInGuard k p of
    Right _ -> Any (Bind x t p) (doelim k bss c)
    Left (_, rights) -> Any (Bind x t (PAnd rights)) (doelim k bss c) -- TODO: for now we set the kvar to true. not sure if this is correct

-- If k is in the guard then returns a Left list of that k and the remaining preds in the guard
-- If k is not in the guard returns a Right of the pred
findKVarInGuard :: F.Symbol -> Pred -> Either ([(F.Symbol, [F.Symbol])], [Pred]) Pred
findKVarInGuard k (PAnd ps) =
  if null lefts
    then Right (PAnd ps) -- kvar not found
    else Left $ (newLefts, newRights)
  where findResults = findKVarInGuard k <$> ps
        (lefts, rights) = partitionEithers findResults
        newLefts = concat $ map fst lefts
        newRights = concat (snd <$> lefts) ++ rights
findKVarInGuard k p@(Var k' xs)
  | k == k' = Left ([(k', xs)], [])
  | otherwise = Right p
findKVarInGuard _ p = Right p

-- | Returns a list of KVars with their arguments that are present as
--
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind01.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind02.smt2"
-- ... ["k"]
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- ... []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- ... ["k0"]
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test03.smt2"
-- ... ["k0"]

boundVars :: Cstr a -> S.Set F.Symbol
boundVars Head{} = mempty
boundVars (CAnd cs) = mconcat $ boundVars <$> cs
boundVars (All (Bind x _ _) c) = S.singleton x <> boundVars c
boundVars (Any (Bind x _ _) c) = S.singleton x <> boundVars c

boundKvars :: Cstr a -> S.Set F.Symbol
boundKvars (Head p _)           = pKVars p
boundKvars (CAnd c)             = mconcat $ boundKvars <$> c
boundKvars (All (Bind _ _ p) c) = pKVars p <> boundKvars c
boundKvars (Any (Bind _ _ p) c) = pKVars p <> boundKvars c

pKVars :: Pred -> S.Set F.Symbol
pKVars (Var k _) = S.singleton k
pKVars (PAnd ps) = mconcat $ pKVars <$> ps
pKVars _         = S.empty

-- | Returns true if the constraint does not contain any existential binders
isNNF :: Cstr a -> Bool
isNNF Head{} = True
isNNF (CAnd cs) = all isNNF cs
isNNF (All _ c) = isNNF c
isNNF Any{} = False

buildKvarEdges :: Query a -> Cstr a -> KVEdges
buildKvarEdges (Query qs vs _ cons dist) nnf = mapMaybe removeNonKVar edges
  where
    edges = FG.kvgEdges $ FG.kvGraph $ hornFInfo $ Query qs vs nnf cons dist

    removeNonKVar (FG.KVar k, _, connections) = Just (FG.KVar k, FG.KVar k, connections')
      where connections' = [FG.KVar k' | FG.KVar k' <- connections]
    removeNonKVar _ = Nothing

findAcyclicKVars :: KVEdges -> [F.Symbol]
findAcyclicKVars edges = [F.kv k | DG.AcyclicSCC (KVar k) <- DG.stronglyConnComp edges]

simplify :: Cstr a -> Cstr a
simplify = flatten . pruneTauts . removeDuplicateBinders

removeDuplicateBinders :: Cstr a -> Cstr a
removeDuplicateBinders = go S.empty
  where
    go _ c@Head{} = c
    go xs (CAnd cs) = CAnd $ go xs <$> cs
    go xs (All b@(Bind x _ _) c) = if x `S.member` xs then go xs c else All b $ go (S.insert x xs) c
    go xs (Any b c) = Any b $ go xs c

pruneTauts :: Cstr a -> Cstr a
pruneTauts = fromJust . go
  where
    go (Head p l) = do
      p' <- goP p
      pure $ Head p' l
    go (CAnd cs) = if null cs' then Nothing else Just $ CAnd cs'
      where cs' = mapMaybe go cs
    go (All b c) = do
      c' <- go c
      pure (All b c')
    go c@Any{} = Just c

    goP (Reft e) = if F.isTautoPred e then Nothing else Just $ Reft e
    goP p@Var{} = Just p
    goP (PAnd ps) = if null ps' then Nothing else Just $ PAnd ps'
      where ps' = mapMaybe goP ps
