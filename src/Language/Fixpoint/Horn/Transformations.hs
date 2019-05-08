{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE LambdaCase  #-}
{-# LANGUAGE FlexibleInstances  #-}
module Language.Fixpoint.Horn.Transformations (
    uniq
  , flatten
  , elim
  , elimPis
  , elimKs
  , solveEbs
  , cstrToExpr
) where

import           Language.Fixpoint.Horn.Types
import qualified Language.Fixpoint.Types      as F
import qualified Data.HashMap.Strict          as M
import           Control.Monad.Identity
import           Data.String                  (IsString (..))
import qualified Data.Set                     as S
import           Control.Monad.State
import           Data.Maybe                   (catMaybes, fromMaybe)
import           Language.Fixpoint.Types.Visitor as V
import           System.Console.CmdArgs.Verbosity
-- import           Debug.Trace

trace :: p -> a -> a
trace _ = id

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

type Sol a = M.HashMap F.Symbol (Either (Either [[Bind]] (Cstr a)) F.Expr)
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
solveEbs (Query qs vs c cons dist) = do
  let c' = pokec c
  whenLoud $ putStrLn "Horn pokec:"
  whenLoud $ putStrLn $ F.showpp c'
  -- This rhs pattern match will fail if there's not at least one eb!
  let (Just horn, mside) = split c'
  whenLoud $ putStrLn "Horn split:"
  whenLoud $ putStrLn $ F.showpp (horn, mside)

  case mside of 
    Nothing   -> pure $ Query qs vs horn cons dist
    Just side -> do 
        -- This whole business depends on Stringly-typed invariant that an ebind
        -- n corresponds to a pivar πn. That's pretty bad but I can't think of
        -- a better way to do this.
      
        -- find solutions to the pivars, put them on the Left of the map
        let ns = fst <$> ebs c
        let l0 = cLabel horn
        let pisols = M.fromList [(piSym n, Left $ Right $ nSol) | n <- ns, Just nSol <- [defs n horn]] -- :: Sol a
        whenLoud $ putStrLn "Pisols:"
        -- whenLoud $ putStrLn $ F.showpp $ pisols
      
        -- find solutions to the kvars, put them on the Right of the map
        let ksols = M.fromList [(k, Left $ Left $ sol1 k (scope k horn)) | k <- hvName <$> vs] -- :: Sol
        -- whenLoud $ putStrLn "Horn Elim:"
        -- whenLoud $ putStrLn $ F.showpp ksols
      
        let sol = evalState (mapM (lookupSol l0 M.empty . piVar) ns) (ksols <> pisols)
        whenLoud $ putStrLn "QE sols:"
        let elimSol = M.fromList $ zip (piSym <$> ns) [Head (Reft p) l0 | p <- sol]
        whenLoud $ putStrLn $ F.showpp elimSol
        let kSol = M.mapMaybe (either (either Just (const Nothing)) (const Nothing)) ksols
      
        let hornFinal = M.foldrWithKey applyPi horn elimSol
        whenLoud $ putStrLn "Final Horn:"
        whenLoud $ putStrLn $ F.showpp hornFinal
      
        let sideCstr = M.foldrWithKey applyPi (M.foldrWithKey doelim' side kSol) elimSol
        whenLoud $ putStrLn "PreElim Side:"
        whenLoud $ putStrLn $ F.showpp sideCstr
        let sideEE = hornify $ elimE undefined sideCstr
        whenLoud $ putStrLn "Final Side:"
        whenLoud $ putStrLn $ F.showpp sideEE
      
        pure $ (Query qs vs (CAnd [ hornFinal, sideEE ]) cons dist)

elimE :: Sol a -> Cstr a -> Cstr a
elimE m (All b c) = All b (elimE m c)
elimE m (CAnd cs) = CAnd (elimE m <$> cs)
elimE _m p@Head{} = p
-- need to QE inside here first
elimE _m (Any (Bind x _ _) (Head p l)) = Head (F.subst1 p (x,e)) l
    where e = fromMaybe F.PTrue $ findSolP x p
elimE _m (Any _ _) = error "oops"

hornify :: Cstr a -> Cstr a
hornify (Head (PAnd ps) a) = CAnd (flip Head a <$> ps')
  where ps' = let (ks, qs) = split ps [] [] in PAnd qs : ks

        split ks ps ((Var x xs):qs) = split ((Var x xs):ks) ps qs
        split ks ps (q:qs) = split ks (q:ps) qs
        split ks ps [] = (ks, ps)
hornify (Head (Reft r) a) = CAnd (flip Head a <$> ((Reft $ F.PAnd ps):(Reft <$> ks)))
  where (ks, ps) = split [] [] $ F.splitPAnd r
        split ks ps (r@F.PKVar{}:rs) = split (r:ks) ps rs
        split ks ps (r:rs) = split ks (r:ps) rs
        split ks ps [] = (ks,ps)
hornify (Head h a) = Head h a
hornify (All b c) = All b $ hornify c
hornify (Any b c) = Any b $ hornify c
hornify (CAnd cs) = CAnd $ hornify <$> cs

instance F.Subable Bind where
    syms = undefined
    substa = undefined
    substf = undefined
    subst su (Bind x t p) = (Bind x t (F.subst su p))

instance F.Subable Pred where
    syms = undefined
    substa = undefined
    substf = undefined
    subst su p = substP su p

substP :: F.Subst -> Pred -> Pred
substP su (Reft e) = Reft $ F.subst su e
substP su (PAnd ps) = PAnd $ substP su <$> ps
substP su (Var k xs) = Var k $ F.subst su xs

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

ebs :: Cstr a -> [(F.Symbol, F.Sort)]
ebs (Head _ _) = []
ebs (CAnd cs) = ebs =<< cs
ebs (All _ c) = ebs c
ebs (Any (Bind x t _) c) = (x,t) : ebs c

pokec :: Cstr a -> Cstr a
pokec (Head c l) = Head c l
pokec (CAnd c)   = CAnd (pokec <$> c)
pokec (All b c2) = All b $ pokec c2
pokec (Any b c2) = CAnd [All b' $ pokec c2, Any b (Head pi l)]
  -- TODO: actually use the renamer?
  where
    Bind x t _p = b
    -- TODO: deal with refined ebinds somehow. currently the rest of the
    -- machinery assumes they're in the approrpiate syntactic form
    b' = Bind x t pi -- (PAnd [p, pi])
    pi = piVar x
    l  = cLabel c2

piVar :: F.Symbol -> Pred
piVar x = Var (piSym x) [x]

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
elimKs :: [F.Symbol] -> (Cstr a, Cstr a) -> (Cstr a, Cstr a)
elimKs [] cc = cc
elimKs (k:ks) (horn, side) = elimKs ks (horn', side')
  where sol = sol1 k (scope k horn)
        -- Eliminate Kvars inside Cstr inside horn, and in Expr (under
        -- quantifiers waiting to be eliminated) in both.
        horn' = doelim' k sol . doelim k sol $ horn
        side' = doelim' k sol $ side

doelim' :: F.Symbol -> [[Bind]] -> Cstr a -> Cstr a
doelim' k bss (CAnd cs) = CAnd $ doelim' k bss <$> cs
doelim' k bss (Head p a) = Head (tx k bss p) a
doelim' k bss (All (Bind x t p) c) = All (Bind x t $ tx k bss p) (doelim' k bss c)
doelim' k bss (Any (Bind x t p) c) = Any (Bind x t $ tx k bss p) (doelim' k bss c)

-- [NOTE-elimK-positivity]:
--
-- uh-oh I suspect this traversal is WRONG. We can build an
-- existentialPackage as a solution to a K in a negative position, but in
-- the *positive* position, the K should be solved to FALSE.
--
-- Well, this may be fine --- semantically, this is all the same, but the
-- exists in the positive positions (which will stay exists when we go to
-- prenex) may give us a lot of trouble during _quantifier elimination_
tx :: F.Symbol -> [[Bind]] -> Pred -> Pred
tx k bss = trans (defaultVisitor { txExpr = existentialPackage, ctxExpr = ctxKV }) M.empty ()
  where
  splitBinds xs = unzip $ (\(Bind x t p) -> ((x,t),p)) <$> xs
  cubeSol su (Bind _ _ (Reft eqs):xs)
    | (xts, es) <- splitBinds xs
    = F.PExist xts $ F.PAnd (F.subst su eqs : map predToExpr es)
  cubeSol _ _ = error "cubeSol in doelim'"
  -- This case is a HACK. In actuality, we need some notion of
  -- positivity...
  existentialPackage _ (F.PAll _ (F.PImp _ (F.PKVar (F.KV k') _)))
    | k' == k
    = F.PTrue
  existentialPackage m (F.PKVar (F.KV k') su)
    | k' == k
    , M.lookupDefault 0 k m < 2
    = F.PAnd $ cubeSol su . reverse <$> bss
  existentialPackage _ e = e
  ctxKV m (F.PKVar (F.KV k) _) = M.insertWith (+) k 1 m
  ctxKV m _ = m

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

qe :: M.HashMap F.Symbol Integer -> Cstr a -> State (Sol a) F.Expr
qe m c = do
 c' <- qe' m c
 pure $ trace (show c ++ " =[qe]=>  " ++ show c') c'

qe' :: M.HashMap F.Symbol Integer -> Cstr a -> State (Sol a) F.Expr
qe' m (Head p l)           = lookupSol l m p
qe' m (CAnd cs)            = F.PAnd <$> mapM (qe m) cs
qe' m (All (Bind x _ p) c) = forallElim x <$> lookupSol (cLabel c) m p <*> qe m c
qe' _ Any{}                = error "QE for Any????"

forallElim :: (F.Subable t, Visitable t) => F.Symbol -> t -> F.Expr -> F.Expr
forallElim x p e = forallElim' x eqs p e
  where
  eqs = fold eqVis () [] p
  eqVis             = (defaultVisitor :: Visitor F.Expr t) { accExpr = kv' }
  kv' _ e@(F.PAtom F.Eq a b)
    | F.EVar x == a || F.EVar x == b
    = [e]
  kv' _ _                    = []

forallElim' :: F.Subable a => F.Symbol -> [F.Expr] -> a -> F.Expr -> F.Expr
forallElim' x (F.PAtom F.Eq a b : _) _ e
  | F.EVar x == a
  = F.subst1 e (x,b)
  | F.EVar x == b
  = F.subst1 e (x,a)
forallElim' x _ p e
  | x `notElem` F.syms p && x `notElem` F.syms e  = e
forallElim' x _ _ e = runIdentity $ flip mapMExpr e $ \case
    p@F.PAtom{} -> if x `notElem` F.syms p then pure p else pure F.PTrue
   -- TODO: where else might this appear? App, KVar?
    p -> pure p

lookupSol :: a -> M.HashMap F.Symbol Integer -> Pred -> State (Sol a) F.Expr
lookupSol l m c = do
 c' <- lookupSol' l m c
 pure $ trace (show m ++ show c ++ " =[l]=> " ++ show c')  c'

lookupSol' :: a -> M.HashMap F.Symbol Integer -> Pred -> State (Sol a) F.Expr
lookupSol' l m (Var x xs) =
  let n = M.lookupDefault 0 x m in
  if n > 0 then pure $ predToExpr (Var x xs) else
  let m' = M.insert x (n+1) m in gets (M.lookup x) >>= \case
    -- Memoize only the solutions to Pivars, because they don't depend on args
    (Just (Left (Right sol))) -> do
      sol <- qe m' sol
      -- modify $ M.insert x $ Right $ sol
      pure sol
    (Just (Left (Left sol))) -> 
      qe m' $ doelim2 l sol (Var x xs)

    (Just (Right sol)) -> pure sol
    Nothing -> error $ "no soution to Var " ++ F.symbolString x
    
lookupSol' _ _ (Reft e) = pure e
lookupSol' l m (PAnd ps) = F.PAnd <$> mapM (lookupSol l m) ps

findSolP :: F.Symbol -> Pred -> Maybe F.Expr
findSolP x (Reft e) = findSolE x e
findSolP x (PAnd (p:ps)) = findSolP x p <> findSolP x (PAnd ps)
findSolP _ _ = error "findSolP KVar"

findSolE :: F.Symbol -> F.Expr -> Maybe F.Expr
findSolE x (F.PAtom F.Eq (F.EVar y) e) | x == y = Just e
findSolE x (F.PAtom F.Eq e (F.EVar y)) | x == y = Just e
findSolE x (F.PAnd (e:es)) = findSolE x e <> findSolE x (F.PAnd es)
findSolE _ _ = Nothing

-- This solution is "wrong" ... forall should be exists and implies should
-- be and, but it's fine because that doesn't matter to QE above
doelim2 :: a -> [[Bind]] -> Pred -> Cstr a
doelim2 l bss (Var k xs)
  = mkAnd $ cubeSol . reverse <$> bss
  where su = F.Su $ M.fromList $ zip (kargs k) (F.EVar <$> xs)
        mkAnd [c] = c
        mkAnd cs = CAnd cs
        cubeSol ((Bind _ _ (Reft eqs)):xs) =
          foldl (flip All) (Head (Reft $ F.subst su eqs) l) xs
        cubeSol _ = error "internal error"
doelim2 l _ p = Head p l

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
elim c = if S.null $ boundKvars res then res else error "called elim on cyclic fucker"
  where
  res = S.foldl elim1 c (boundKvars c)

elim1 :: Cstr a -> F.Symbol -> Cstr a
-- Find a `sol1` solution to a kvar `k`, and then subsitute in the solution for
-- each rhs occurence of k.
elim1 c k = doelim k sol c
  where sol = sol1 k (scope k c)

-- scope drops extraneous leading binders so that we can take the strongest
-- scoped solution instead of the strongest solution
scope :: F.Symbol -> Cstr a -> Cstr a
scope k = go . snd . scope' k
  where go (All _ c') = go c'
        go c = c

-- |
-- >>> sc <- scope' "k0" . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sc
-- (True,(forall ((x ... (and (forall ((y ... (forall ((v ... ((k0 v)))) (forall ((z ...

-- scope' prunes out branches that don't have k
scope' :: F.Symbol -> Cstr a -> (Bool, Cstr a)

scope' k (CAnd c) = case map snd $ filter fst $ map (scope' k) c of
                     []  -> (False, CAnd [])
                     [c] -> (True, c)
                     cs  -> (True, CAnd cs)

-- TODO: Bind PAnd Case
scope' k c@(All (Bind x t (Var k' su)) c')
  | k == k' = (True, c)
  | otherwise = All (Bind x t (Var k' su)) <$> scope' k c'
scope' k c@(All _ c')
  = const c <$> scope' k c'
scope' _ (Any _ _) = error "ebinds don't work with old elim"

scope' k c@(Head (Var k' _) _)
-- this case seems extraneous?
  | k == k'   = (True, c)
scope' _ c@Head{} = (False, c)

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

sol1 :: F.Symbol -> Cstr a -> [[Bind]]
-- sol1 k cs = go k [] cs
--   where
--     go k branch (CAnd cs) = go k branch =<< cs
--     go k branch (All b c) = go k (branch ++ [b]) c
--     go k branch (Head (Var k' ys) _) | k == k' = [F.subst (F.Su $ M.fromList $ zip ys (F.EVar <$> xs)) branch]
--       where xs = zipWith const (kargs k) ys
--     go _ _ (Head _ _) = []
--     go _ _ (Any _ _) =  error "ebinds don't work with old elim"

sol1 k (CAnd cs) = sol1 k =<< cs
sol1 k (All b c) = (b:) <$> sol1 k c
sol1 k (Head (Var k' ys) _) | k == k'
  = [[Bind (fromString "_") F.boolSort $ Reft $ F.PAnd $ zipWith (F.PAtom F.Eq) (F.EVar <$> xs) (F.EVar <$> ys)]]
  where xs = zipWith const (kargs k) ys
sol1 _ (Head _ _) = []
sol1 _ (Any _ _) =  error "ebinds don't work with old elim"

kargs :: F.Symbol -> [F.Symbol]
kargs k = fromString . (("κarg$" ++ F.symbolString k ++ "#") ++) . show <$> [1..]

-- |
-- >>> let c = doParse' hCstrP "" "(forall ((z Int) ($k0 z)) ((z = x)))"
-- >>> doelim "k0" [[Bind "v" F.boolSort (Reft $ F.EVar "v"), Bind "_" F.boolSort (Reft $ F.EVar "donkey")]]  c
-- (forall ((v bool) (v)) (forall ((z int) (donkey)) ((z == x))))

doelim :: F.Symbol -> [[Bind]] -> Cstr a -> Cstr a
doelim k bp (CAnd cs)
  = CAnd $ doelim k bp <$> cs
doelim k bss (All (Bind x t (Var k' xs)) c)
  | k == k'
  = mkAnd $ cubeSol . reverse <$> bss
  where su = F.Su $ M.fromList $ zip (kargs k) (F.EVar <$> xs)
        mkAnd [c] = c
        mkAnd cs = CAnd cs
        cubeSol ((Bind _ _ (Reft eqs)):xs) =
          foldl (flip All) (All (Bind x t (Reft $ F.subst su eqs)) $ doelim k bss c) xs
        cubeSol _ = error "internal error"
--- TODO: what about the PAnd case inside b?
doelim k bp (All b c)
  = All b (doelim k bp c)
doelim k _ (Head (Var k' _) a)
  | k == k'
  = Head (Reft F.PTrue) a
doelim _ _ (Head p a) = Head p a
doelim _ _ (Any _ _) =  error "ebinds don't work with old elim"

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
