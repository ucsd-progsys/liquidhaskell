{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE TupleSections  #-}
module Language.Fixpoint.Horn.Transformations (
    uniq
  , flatten
  , elim
  , elimPis
  , solveEbs
  , cstrToExpr
) where

import           Language.Fixpoint.Horn.Types
import           Language.Fixpoint.Horn.Info
import           Language.Fixpoint.Smt.Theories as F
import qualified Language.Fixpoint.Types      as F
import qualified Language.Fixpoint.Types.Config as F
import           Language.Fixpoint.Graph      as FG
import qualified Data.HashMap.Strict          as M
import           Data.String                  (IsString (..))
import           Data.Either                  (partitionEithers, rights)
import           Data.List                    (nub)
import qualified Data.Set                     as S
import qualified Data.HashSet                 as HS
import qualified Data.Graph                   as DG
import           Control.Monad.State
import           Data.Maybe                   (catMaybes, mapMaybe, fromMaybe)
import           Language.Fixpoint.Types.Visitor as V
import           System.Console.CmdArgs.Verbosity
import           Data.Bifunctor (second)
import System.IO (hFlush, stdout)
-- import qualified Debug.Trace as DBG

-- $setup
-- >>> :l src/Language/Fixpoint/Horn/Transformations.hs src/Language/Fixpoint/Horn/Parse.hs
-- >>> :m + *Language.Fixpoint.Horn.Parse
-- >>> import Language.Fixpoint.Parse
-- >>> :set -XOverloadedStrings

---------------
-- Debugging
---------------
trace :: String -> a -> a
-- trace _msg v = DBG.trace _msg v
trace _msg v = v

printPiSols :: (F.PPrint a1, F.PPrint a2, F.PPrint a3) =>
               M.HashMap a1 ((a4, a2), a3) -> IO ()
printPiSols piSols =
  sequence_ $ ((\(piVar, ((_, args), cstr)) -> do
                  putStr $ F.showpp piVar
                  putStr " := "
                  putStrLn $ F.showpp args
                  putStrLn $ F.showpp cstr
                  putStr "\n"
                  hFlush stdout) <$> M.toList piSols)
---------------

-- type Sol a = M.HashMap F.Symbol (Either (Either [[Bind]] (Cstr a)) F.Expr)

-- | solveEbs takes a query and returns a query with the ebinds solved out
--
-- it has some preconditions
-- - pi -> k -> pi structure. That is, there are no cycles, and while ks
-- can depend on other ks, pis cannot directly depend on other pis
-- - predicate for exists binder is `true`. (TODO: is this pre stale?)

solveEbs :: (F.PPrint a) => F.Config -> Query a -> IO (Query a)
------------------------------------------------------------------------------
solveEbs cfg query@(Query qs vs c cons dist eqns mats dds) = do
  -- clean up
  let normalizedC = flatten . pruneTauts $ hornify c
  whenLoud $ putStrLn "Normalized EHC:"
  whenLoud $ putStrLn $ F.showpp normalizedC

  -- short circuit if no ebinds are present
  if isNNF c then pure $ Query qs vs normalizedC cons dist eqns mats dds else do
  let kvars = boundKvars normalizedC

  whenLoud $ putStrLn "Skolemized:"
  let poked = pokec normalizedC
  whenLoud $ putStrLn $ F.showpp poked

  whenLoud $ putStrLn "Skolemized + split:"
  let (Just _horn, Just _side) = split poked
  let horn = flatten . pruneTauts $ _horn
  let side = flatten . pruneTauts $ _side
  whenLoud $ putStrLn $ F.showpp (horn, side)

  -- collect predicate variables
  let pivars = boundKvars poked `S.difference` kvars

  let cuts = calculateCuts cfg query (forgetPiVars pivars horn)
  let acyclicKs = kvars `S.difference` cuts

  whenLoud $ putStrLn "solved acyclic kvars:"
  let (horn', side') = elimKs' (S.toList acyclicKs) (horn, side)
  whenLoud $ putStrLn $ F.showpp horn'
  whenLoud $ putStrLn $ F.showpp side'

  -- if not $ S.null cuts then error $ F.showpp $ S.toList cuts else pure ()
  let elimCutK k c = doelim k [] c
  horn' <- pure $ foldr elimCutK horn' cuts
  side' <- pure $ foldr elimCutK side' cuts

  whenLoud $ putStrLn "pi defining constraints:"
  let piSols = M.fromList $ fmap (\pivar -> (pivar, piDefConstr pivar horn')) (S.toList pivars)
  whenLoud $ printPiSols piSols

  whenLoud $ putStrLn "solved pis:"
  let solvedPiCstrs = solPis (S.fromList $ M.keys cons ++ M.keys dist) piSols
  whenLoud $ putStrLn $ F.showpp solvedPiCstrs

  whenLoud $ putStrLn "solved horn:"
  let solvedHorn = substPiSols solvedPiCstrs horn'
  whenLoud $ putStrLn $ F.showpp solvedHorn

  whenLoud $ putStrLn "solved side:"
  let solvedSide = substPiSols solvedPiCstrs side'
  whenLoud $ putStrLn $ F.showpp solvedSide

  pure $ (Query qs vs (CAnd [solvedHorn, solvedSide]) cons dist eqns mats dds)

-- | Collects the defining constraint for π
-- that is, given `∀ Γ.∀ n.π => c`, returns `((π, n:Γ), c)`
piDefConstr :: F.Symbol -> Cstr a -> ((F.Symbol, [F.Symbol]), Cstr a)
piDefConstr k c = ((head ns, head formals), defC)
  where
    (ns, formals, defC) = case go c of
      (ns, formals, Just defC) -> (ns, formals, defC)
      (_, _, Nothing) -> error $ "pi variable " <> F.showpp k <> " has no defining constraint."

    go :: Cstr a -> ([F.Symbol], [[F.Symbol]], Maybe (Cstr a))
    go (CAnd cs) = (\(as, bs, cs) -> (concat as, concat bs, cAndMaybes cs)) $ unzip3 $ go <$> cs
    go (All b@(Bind n _ (Var k' xs)) c')
      | k == k' = ([n], [S.toList $ S.fromList xs `S.difference` S.singleton n], Just c')
      | otherwise = map3 (fmap (All b)) (go c')
    go (All b c') = map3 (fmap (All b)) (go c')
    go _ = ([], [], Nothing)

    cAndMaybes :: [Maybe (Cstr a)] -> Maybe (Cstr a)
    cAndMaybes maybeCs = case catMaybes maybeCs of
      [] -> Nothing
      cs -> Just $ CAnd cs

map3 :: (c -> d) -> (a, b, c) -> (a, b, d)
map3 f (x, y, z) = (x, y, f z)

-- | Solve out the given pivars
solPis :: S.Set F.Symbol -> M.HashMap F.Symbol ((F.Symbol, [F.Symbol]), Cstr a) -> M.HashMap F.Symbol Pred
solPis measures piSols = go (M.toList piSols) piSols
  where
    go ((pi, ((n, xs), c)):pis) piSols = M.insert pi solved $ go pis piSols
      where solved = solPi measures pi n (S.fromList xs) piSols c
    go [] _ = mempty

-- TODO: rewrite to use CC
solPi :: S.Set F.Symbol -> F.Symbol -> F.Symbol -> S.Set F.Symbol -> M.HashMap F.Symbol ((F.Symbol, [F.Symbol]), Cstr a) -> Cstr a -> Pred
solPi measures basePi n args piSols c = trace ("\n\nsolPi: " <> F.showpp basePi <> "\n\n" <> F.showpp n <> "\n" <> F.showpp (S.toList args) <> "\n" <> F.showpp ((\(a, _, c) -> (a, c)) <$> edges) <> "\n" <> F.showpp (sols n) <> "\n" <> F.showpp rewritten <> "\n" <> F.showpp c <> "\n\n") $ PAnd $ rewritten
  where
    rewritten = rewriteWithEqualities measures n args equalities
    equalities = (nub . fst) $ go (S.singleton basePi) c
    edges = eqEdges args mempty equalities
    (eGraph, vf, lookupVertex) = DG.graphFromEdges edges
    sols x = case lookupVertex x of
      Nothing -> []
      Just vertex -> nub $ filter (/= F.EVar x) $ mconcat [es | ((_, es), _, _) <- vf <$> DG.reachable eGraph vertex]

    go :: S.Set F.Symbol -> Cstr a -> ([(F.Symbol, F.Expr)], S.Set F.Symbol)
    go visited (Head p _) = (collectEqualities p, visited)
    go visited (CAnd cs) = foldl (\(eqs, visited) c -> let (eqs', visited') = go visited c in (eqs' <> eqs, visited')) (mempty, visited) cs
    go visited (All (Bind _ _ (Var pi _)) c)
      | S.member pi visited = go visited c
      | otherwise = let (_, defC) = (piSols M.! pi)
                        (eqs', newVisited) = go (S.insert pi visited) defC
                        (eqs'', newVisited') = go newVisited c in
          (eqs' <> eqs'', newVisited')
    go visited (All (Bind _ _ p) c) = let (eqs, visited') = go visited c in
      (eqs <> collectEqualities p, visited')
    go _ Any{} = error "exists should not be present in piSols"

------------------------------------------------------------------------------
{- | pokec skolemizes the EHC into an HC + side condition
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

{- |

Now we split the poked constraint into the side conditions and the meat of
the constraint

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

Takes noside, side, piSols and solves a set of kvars in them

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

-- TODO: make this elimKs and update tests for elimKs
elimKs' :: [F.Symbol] -> (Cstr a, Cstr a) -> (Cstr a, Cstr a)
elimKs' [] cstrs = cstrs
elimKs' (k:ks) (noside, side) = elimKs' (trace ("solved kvar " <> F.showpp k <> ":\n" <> F.showpp sol) ks) (noside', side')
  where
    sol = sol1 k $ scope k noside
    noside' = simplify $ doelim k sol noside
    side' = simplify $ doelim k sol side

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

-- qe :: F.Symbol -> S.Set F.Symbol -> Cstr a -> Pred
-- qe n args c = PAnd $ ps
--   where
--     equalities = collectEqualities c
--     ps = rewriteWithEqualities n args equalities

rewriteWithEqualities :: S.Set F.Symbol -> F.Symbol -> S.Set F.Symbol -> [(F.Symbol, F.Expr)] -> [Pred]
rewriteWithEqualities measures n args equalities = preds
  where
    (eGraph, vf, lookupVertex) = DG.graphFromEdges $ eqEdges args mempty equalities

    nResult = (n, makeWellFormed 15 $ sols n)
    argResults = map (\arg -> (arg, makeWellFormed 15 $ sols arg)) (S.toList args)

    preds = (mconcat $ (\(x, es) -> mconcat $ mkEquality x <$> es) <$> (nResult:argResults))

    mkEquality x e = [Reft (F.PAtom F.Eq (F.EVar x) e)]

    sols :: F.Symbol -> [F.Expr]
    sols x = case lookupVertex x of
      Nothing -> []
      Just vertex -> nub $ filter (/= F.EVar x) $ mconcat [es | ((_, es), _, _) <- vf <$> DG.reachable eGraph vertex]

    argsAndPrims = args `S.union` (S.fromList $ map fst $ F.toListSEnv $ F.theorySymbols []) `S.union`measures

    isWellFormed :: F.Expr -> Bool
    isWellFormed e = (S.fromList $ F.syms e) `S.isSubsetOf` argsAndPrims

    makeWellFormed :: Int -> [F.Expr] -> [F.Expr]
    makeWellFormed 0 es = filter isWellFormed es -- We solved it. Maybe.
    makeWellFormed n es = makeWellFormed (n - 1) $ mconcat $ go <$> es
      where
        go e = if isWellFormed e then [e] else rewrite rewrites [e]
          where
            needSolving = (S.fromList $ F.syms e) `S.difference` argsAndPrims
            rewrites = (\x -> (x, filter (/= F.EVar x) $ sols x)) <$> S.toList needSolving
            rewrite [] es = es
            rewrite ((x, rewrites):rewrites') es = rewrite rewrites' $ [F.subst (F.mkSubst [(x, e')]) e | e' <- rewrites, e <- es]

eqEdges :: S.Set F.Symbol ->
           M.HashMap F.Symbol ([F.Symbol], [F.Expr]) ->
           [(F.Symbol, F.Expr)] ->
           [((F.Symbol, [F.Expr]), F.Symbol, [F.Symbol])]
eqEdges _args edgeMap [] = M.foldrWithKey (\x (ys, es) edges -> ((x, es), x, ys):edges) [] edgeMap
eqEdges args edgeMap ((x, e):eqs)
  | F.EVar y <- e
  , S.member y args = eqEdges args (M.insertWith (<>) x ([y], [F.EVar y]) edgeMap) eqs
  | F.EVar y <- e   = eqEdges args (M.insertWith (<>) x ([y], []) edgeMap) eqs
  | otherwise       = eqEdges args (M.insertWith (<>) x ([], [e]) edgeMap) eqs

collectEqualities :: Pred -> [(F.Symbol, F.Expr)]
collectEqualities = goP
  where
    goP (Reft e) = goE e
    goP (PAnd ps) = mconcat $ goP <$> ps
    goP _ = mempty

    goE (F.PAtom F.Eq left right) = extractEquality left right
    goE (F.PAnd es) = mconcat $ goE <$> es
    goE _ = mempty

extractEquality :: F.Expr -> F.Expr -> [(F.Symbol, F.Expr)]
extractEquality left right
  | F.EVar x <- left, F.EVar y <- right, x == y = mempty
  | F.EVar x <- left, F.EVar y <- right  = [(x, right), (y, left)]
  | F.EVar x <- left = [(x, right)]
  | F.EVar x <- right = [(x, left)]
  | otherwise = mempty

substPiSols :: M.HashMap F.Symbol Pred -> Cstr a -> Cstr a
substPiSols _ c@Head{} = c
substPiSols piSols (CAnd cs) = CAnd $ substPiSols piSols <$> cs
substPiSols piSols (All (Bind x t p) c)
  | Var k _ <- p = All (Bind x t $ M.lookupDefault p k piSols) (substPiSols piSols c)
  | otherwise = All (Bind x t p) (substPiSols piSols c)
substPiSols piSols (Any (Bind n _ p) c)
  | Head (Var pi _) label <- c, Just sol <- M.lookup pi piSols =
    case findSol n sol of
      Just e -> Head (flatten $ PAnd $ (\pred -> F.subst1 pred (n, e)) <$> [p, sol]) label
      Nothing -> Head (Reft $ F.PAnd []) label
  | otherwise = error "missing piSol"

findSol :: F.Symbol -> Pred -> Maybe F.Expr
findSol x = go
  where
    go (Reft e) = findEq e
    go Var{} = Nothing
    go (PAnd ps) = case mapMaybe go ps of
      [] -> Nothing
      x:_ -> Just x

    findEq (F.PAtom F.Eq left right)
      | F.EVar y <- left, y == x = Just right
      | F.EVar y <- right, y == x = Just left
    findEq _ = Nothing

------------------------------------------------------------------------------
-- | uniq makes sure each binder has a unique name
------------------------------------------------------------------------------
type RenameMap = M.HashMap F.Symbol (Integer, [Integer]) -- the first component is how many times we've seen this name. the second is the name mappings

uniq :: Cstr a -> Cstr a
uniq c = evalState (uniq' c) M.empty

uniq' :: Cstr a -> State RenameMap (Cstr a)
uniq' (Head c a) = Head <$> gets (rename c) <*> pure a
uniq' (CAnd c) = CAnd <$> mapM uniq' c
uniq' (All b@(Bind x _ _) c2) = do
    b' <- uBind b
    c2' <- uniq' c2
    modify $ popName x
    pure $ All b' c2'
uniq' (Any b@(Bind x _ _) c2) = do
    b' <- uBind b
    c2' <- uniq' c2
    modify $ popName x
    pure $ Any b' c2'

popName :: F.Symbol -> RenameMap -> RenameMap
popName x m = M.adjust (second tail) x m

pushName :: Maybe (Integer, [Integer]) -> Maybe (Integer, [Integer])
pushName Nothing = Just (0, [0])
pushName (Just (i, is)) = Just (i + 1, (i + 1):is)

uBind :: Bind -> State RenameMap Bind
uBind (Bind x t p) = do
   x' <- uVariable x
   -- nmap <- get
   p' <- gets (rename p)
   pure $ Bind x' t p'

uVariable :: IsString a => F.Symbol -> State RenameMap a
uVariable x = do
   modify (M.alter pushName x)
   i <- gets (head . snd . (M.! x))
   pure $ numSym x i

rename :: Pred -> RenameMap -> Pred
rename e m = substPred (M.mapMaybeWithKey (\k v -> case v of
                                              (_, n:_) -> Just $ numSym k n
                                              _ -> Nothing) m) e

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

-- scope is lca
scope :: F.Symbol -> Cstr a -> Cstr a
scope k cstr = case go cstr of
                 Right c -> c
                 Left l -> Head (Reft F.PTrue) l
  where
    go c@(Head (Var k' _) _)
      | k' == k = Right c
    go (Head _ l) = Left l
    go c@(All (Bind _ _ p) c') =
      if k `S.member` (pKVars p) then Right c else go c'
    go Any{} = error "any should not appear after poke"

    -- if kvar doesn't appear, then just return the left
    -- if kvar appears in one child, that is the lca
    -- but if kvar appear in multiple chlidren, this is the lca
    go c@(CAnd cs) = case rights (go <$> cs) of
                       [] -> Left $ cLabel c
                       [c] -> Right c
                       _ -> Right c


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
doelim k bss (CAnd cs)
  = CAnd $ doelim k bss <$> cs
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

calculateCuts :: F.Config -> Query a -> Cstr a -> S.Set F.Symbol
calculateCuts cfg (Query qs vs _ cons dist eqns mats dds) nnf = convert $ FG.depCuts deps
  where
    (_, deps) = elimVars cfg (hornFInfo cfg $ Query qs vs nnf cons dist eqns mats dds)
    convert hashset = S.fromList $ F.kv <$> (HS.toList hashset)

forgetPiVars :: S.Set F.Symbol -> Cstr a -> Cstr a
forgetPiVars _ c@Head{} = c
forgetPiVars pis (CAnd cs) = CAnd $ forgetPiVars pis <$> cs
forgetPiVars pis (All (Bind x t p) c)
  | Var k _ <- p, k `S.member` pis = All (Bind x t (PAnd [])) $ forgetPiVars pis c
  | otherwise = All (Bind x t p) $ forgetPiVars pis c
forgetPiVars _ Any{} = error "shouldn't be present"

-----------------------------------------------------------------------------------
-- | Cleanup Horn Constraint
-- We want to simplify the Query a little bit, and make sure it is Horn,
-- that is, only a kvar-free (ie concrete) predicate or a single kvar in
-- each head
-----------------------------------------------------------------------------------

simplify :: Cstr a -> Cstr a
simplify = flatten . pruneTauts . removeDuplicateBinders

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

-- | Split heads into one for each kvar so that queries are always horn constraints
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

removeDuplicateBinders :: Cstr a -> Cstr a
removeDuplicateBinders = go S.empty
  where
    go _ c@Head{} = c
    go xs (CAnd cs) = CAnd $ go xs <$> cs
    go xs (All b@(Bind x _ _) c) = if x `S.member` xs then go xs c else All b $ go (S.insert x xs) c
    go xs (Any b c) = Any b $ go xs c

pruneTauts :: Cstr a -> Cstr a
pruneTauts = fromMaybe (CAnd []) . go
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
