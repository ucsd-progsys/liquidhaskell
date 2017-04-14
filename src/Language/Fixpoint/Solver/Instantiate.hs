{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ExistentialQuantification #-}

--------------------------------------------------------------------------------
-- | Axiom Instantiation  ------------------------------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Instantiate (

  instantiateAxioms,
  AxiomEnv (..),
  Equation (..),
  Simplify (..)

  ) where

import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Smt.Theories as FT
import           Language.Fixpoint.Types.Visitor (eapps, kvars, mapMExpr)
import           Language.Fixpoint.Misc          (mapFst)

import Language.Fixpoint.Smt.Interface          (smtPop, smtPush, smtDecls, smtAssert,
                                                 checkValid', Context(..) )
import Language.Fixpoint.Defunctionalize        (defuncAny, Defunc, makeLamArg)
import Language.Fixpoint.SortCheck              (elaborate, Elaborate)

import Control.Monad.State

-- AT: I've inlined this, but we should have a more elegant solution
--     (track predicates instead of selectors!)
-- import           Language.Haskell.Liquid.GHC.Misc (dropModuleNames)
import qualified Data.Text            as T
import qualified Data.HashMap.Strict  as M
import qualified Data.List            as L
import           Data.Maybe           (catMaybes, fromMaybe)
import           Data.Char            (isUpper)
import           Data.Foldable        (foldlM)

-- DEBUGGING
------------
import qualified Debug.Trace as T

trace :: AxiomEnv c -> String -> a -> a
trace aenv str x
  | aenvVerbose aenv
  = T.trace str x
  | otherwise
  = x

returnTrace :: String -> Expr -> Expr -> EvalST Expr
returnTrace str e e'
  = do (EvalEnv i _ c) <- get
       return $
           trace c
             ("\nEval " ++ show i ++ " by " ++ str ++ " :\n" ++
             showpp e ++ " ~> " ++ showpp e' ++ "\n")
             e'

(~>) :: (Expr, String) -> Expr -> EvalST Expr
(e,str) ~> e' = do
    modify (\st -> st{evId = evId st + 1})
    returnTrace str e (η e')

------------
-- Interface
------------
data AxiomEnv a = AEnv { aenvSyms    :: ![Symbol]
                       , aenvEqs     :: ![Equation]
                       , aenvSimpl   :: ![Simplify]
                       , aenvFuel    :: M.HashMap SubcId Int
                       , aenvExpand  :: M.HashMap SubcId Bool
                       , aenvDoRW    :: Bool
                       , aenvDoEqs   :: Bool
                       , aenvVerbose :: !Bool
                       , aenvConfig  :: FC.Config
                       , aenvContext :: Context
                       }


data Equation = Equ { eqName :: Symbol
                    , eqArgs :: [Symbol]
                    , eqBody :: Expr
                    } deriving (Show)

-- eg  SMeasure (f D [x1..xn] e)
-- for f (D x1 .. xn) = e
data Simplify = SMeasure  { smName  :: Symbol         -- eg. f
                          , smDC    :: Symbol         -- eg. D
                          , smArgs  :: [Symbol]       -- eg. xs
                          , smBody  :: Expr           -- eg. e[xs]
                          } deriving (Show)

getEqBody :: Equation -> Maybe Expr
getEqBody (Equ x xs (PAnd (PAtom Eq fxs e:_)))
  | (EVar f, es) <- splitEApp fxs
  , f == x
  , es == (EVar <$> xs)
  = Just e
getEqBody _
  = Nothing

---------------------
-- Instantiate Axioms
---------------------
instantiateAxioms :: Show c => BindEnv -> SEnv Sort -> AxiomEnv c -> (Integer, SubC c) -> IO (SubC c)
instantiateAxioms _ _ aenv (sid,sub)
  | not (M.lookupDefault False sid (aenvExpand aenv))
  = return sub
instantiateAxioms bds fenv aenv (sid,sub)
  = flip strengthenLhs sub . pAnd . trace aenv msg . (is0 ++) . (is ++) <$> evalEqs
  where
    is0 = eqBody <$> L.filter (null . eqArgs) eqs
    -- AT: Fuck strict IO semantics
    is               = if aenvDoEqs aenv
                          then instances maxNumber aenv (trace aenv initMsg initOccurences)
                          else []
    evalEqs          = if aenvDoRW aenv
                         then trace aenv evalMsg
             map (uncurry (PAtom Eq)) .
             filter (uncurry (/=)) <$>
             evaluate ((vv Nothing, slhs sub):binds) fenv as aenv initExpressions
                         else return []
    initExpressions  = expr (slhs sub) : expr (srhs sub) : (expr <$> binds)
    binds            = envCs bds (senv sub)
    initOccurences   = concatMap (makeInitOccurences as eqs) initExpressions

    eqs = aenvEqs aenv

    as  = (,fuelNumber) . eqName <$> filter (not . null . eqArgs) eqs
    fuelNumber    = M.lookupDefault 0 sid (aenvFuel aenv)
    initOccNumber = length initOccurences
    axiomNumber   = length $ aenvSyms aenv
    maxNumber     = (axiomNumber * initOccNumber) ^ fuelNumber

    initMsg = "\nStart instantiation" ++ show (sinfo sub) ++
              " with fuel = " ++ show fuelNumber ++
              " init occurences = " ++ show initOccNumber ++
              " axioms = " ++ show axiomNumber ++
              " can generate up to " ++ show maxNumber ++ " instantiations\n" ++
              "\n\nShow simplifies "  ++ show (aenvSimpl aenv) ++ evalMsg
    evalMsg = "\n\nStart Rewriting"

    msg = "\n\nLiquid Instantiation with " ++ show (L.intercalate "and" methods) ++ "\n\n"
    methods = catMaybes [if aenvDoEqs aenv
                            then Just "arithmetic" else Nothing ,
                         if aenvDoRW  aenv
                            then Just "rewrite"    else Nothing
                        ] :: [String]


------------------------------
-- Knowledge (SMT Interaction)
------------------------------
data Knowledge
  = KN { knSels    :: ![(Expr, Expr)]
       , knEqs     :: ![(Expr, Expr)]
       , knSims    :: ![Simplify]
       , knAms     :: ![Equation]
       , knContext :: IO Context
       , knPreds   :: !([(Symbol, Sort)] -> Expr -> Context -> IO Bool)
       , knLams    :: [(Symbol, Sort)]
       }

emptyKnowledge :: IO Context -> Knowledge
emptyKnowledge cxt = KN [] [] [] [] cxt (\_ _ _ -> return False) []

lookupKnowledge :: Knowledge -> Expr -> Maybe Expr
lookupKnowledge γ e
  -- Zero argument axioms like `mempty = N`
  | Just e' <- L.lookup e (knEqs γ)
  = Just e'
  | Just e' <- L.lookup e (knSels γ)
  = Just e'
  | otherwise
  = Nothing

makeKnowledge :: AxiomEnv c -> SEnv Sort -> [(Symbol, SortedReft)] -> ([(Expr, Expr)], Knowledge)
makeKnowledge aenv fenv es = trace aenv ("\n\nMY KNOWLEDGE= \n\n" ++ -- showpp (expr <$> es) ++
                              -- "INIT KNOWLEDGE\n" ++
                              -- L.intercalate "\n" (showpp <$> es) ++
                              -- L.intercalate "\n" (showpp <$> filter noPKVar (expr <$> es)) ++
                              -- if null tes then "" else "\n\nTRUES = \n\n" ++ showpp tes ++
                              -- if null fes then "" else "\n\nFALSE\n\n" ++ showpp fes ++
                              -- if null sels then "" else "\n\nSELECTORS\n\n" ++ showpp sels ++
                              -- if null eqs then "" else "\n\nAxioms\n\n" ++ showpp eqs ++
                              -- "\n\nAxioms \n\n" ++ show (aenvEqs aenv) ++
                              -- if null proofs then "" else "\n\nProofs\n\n" ++ showpp proofs ++
                              -- if null eqs' then "" else "\n\nCheckers\n\n" ++ showpp eqs' ++
                              "\n" )
                             (simpleEqs,) $ (emptyKnowledge context)
                                 { knSels   = sels
                                 , knEqs    = eqs
                                 , knSims   = aenvSimpl aenv
                                 , knAms    = aenvEqs aenv
                                 , knPreds  = \bs e c -> askSMT c bs e
                                 }
  where
    (xv, sv) = (vv Nothing,  sr_sort $ snd $ head es)
    initCtx = aenvContext aenv

    context :: IO Context
    context = do
      smtPop initCtx
      smtPush initCtx
      smtDecls initCtx $ L.nub [(x, toSMT xv sv [] aenv senv s) | (x, s) <- fbinds, not (M.member x FT.theorySymbols)]
      smtAssert initCtx (pAnd ([toSMT xv sv [] aenv senv $ PAtom Eq e1 e2 |  (e1, e2) <- simpleEqs] ++ filter noPKVar ((toSMT xv sv [] aenv senv . expr) <$> es)))
      return initCtx

    fbinds = toListSEnv fenv ++ [(x, s) | (x, RR s _) <- es]

    senv = fromListSEnv fbinds

    noPKVar = null . kvars

    askSMT :: Context -> [(Symbol, Sort)] -> Expr -> IO Bool
    askSMT _ _ e     | isTautoPred e = return True
    askSMT _ _ e     | isFalse e     = return False
    askSMT cxt xss e | noPKVar e = do
        smtPush cxt
        b <- checkValid' cxt [] PTrue (toSMT xv sv xss aenv senv e)
        smtPop cxt
        return b
    askSMT _ _ _ = return False

    proofs = filter isProof es
    eqs = [(EVar x, ex) | Equ a _ bd <- filter (null . eqArgs) $ aenvEqs aenv, PAtom Eq (EVar x) ex <- splitPAnd bd, x == a, EVar x /= ex ]
    -- This creates the rewrite rule e1 -> e2
    -- when should I apply it?
    -- 1. when e2 is a data con and can lead to further reductions
    -- 2. when size e2 < size e1
    simpleEqs = concatMap (makeSimplifications (aenvSimpl aenv)) dcEqs
    dcEqs = L.nub $ catMaybes [getDCEquality e1 e2 | PAtom Eq e1 e2 <- concatMap splitPAnd (expr <$> proofs)]
    sels  = concatMap (go . expr) es
    go e = let es  = splitPAnd e
               su  = mkSubst [(x, EVar y) | PAtom Eq (EVar x) (EVar y) <- es ]
               sels = [(EApp (EVar s) x, e) | PAtom Eq (EApp (EVar s) x) e <- es, isSelector s ]
           in L.nub (sels ++ subst su sels)

    isSelector :: Symbol -> Bool
    isSelector  = L.isPrefixOf "select" . symbolString

    isProof (_, RR s _) =  showpp s == "Tuple"


toSMT :: (Elaborate a, Defunc a, PPrint a) => Symbol -> Sort -> [(Symbol, Sort)] -> AxiomEnv c -> SEnv Sort -> a -> a
toSMT xv sv xs aenv senv
  = defuncAny (aenvConfig aenv) (insertSEnv xv sv senv) .
    elaborate "symbolic evaluation" (foldl (\env (x,s) -> insertSEnv x s (deleteSEnv x env)) (insertSEnv xv sv senv) xs)


makeSimplifications :: [Simplify] -> (Symbol, [Expr], Expr) -> [(Expr, Expr)]
makeSimplifications sis (dc, es, e)
 = go =<< sis
 where
   go (SMeasure f dc' xs bd)
     | dc == dc', length xs == length es
     = [(EApp (EVar f) e, subst (mkSubst $ zip xs es) bd)]
   go _
     = []

getDCEquality :: Expr -> Expr -> Maybe (Symbol, [Expr], Expr)
getDCEquality e1 e2
    | Just dc1 <- f1
    , Just dc2 <- f2
    = if dc1 == dc2 then Nothing else error ("isDCEquality on" ++ showpp e1 ++ "\n" ++ showpp e2)
    | Just dc1 <- f1
    = Just (dc1, es1, e2)
    | Just dc2 <- f2
    = Just (dc2, es2, e1)
    | otherwise
    = Nothing
  where
    (f1, es1) = mapFst getDC $ splitEApp e1
    (f2, es2) = mapFst getDC $ splitEApp e2

    getDC (EVar x)
        = if isUpper $ head $ symbolString $ dropModuleNames x then Just x else Nothing
    getDC _
        = Nothing

    dropModuleNames  = mungeNames (symbol . last) "."

    mungeNames _ _ ""  = ""
    mungeNames f d s'@(symbolText -> s)
      | s' == tupConName = tupConName
      | otherwise        = f $ T.splitOn d $ stripParens s

    stripParens t = fromMaybe t ((T.stripPrefix "(" >=> T.stripSuffix ")") t)


splitPAnd :: Expr -> [Expr]
splitPAnd (PAnd es) = concatMap splitPAnd es
splitPAnd e         = [e]

addSMTEquality :: Knowledge -> Expr -> Expr -> EvalST (IO ())
addSMTEquality γ e1 e2 =
  return $ do ctx <- knContext γ
              smtAssert ctx (PAtom Eq (makeLam γ e1) (makeLam γ e2))

------------------------
-- Creating Measure Info
------------------------
-- AT@TODO do this for all reflected functions, not just DataCons

-- Insert measure info for every constructor
-- that appears in the expression e
-- required by PMEquivalence.mconcatChunk
assertSelectors :: Knowledge -> Expr -> EvalST ()
assertSelectors γ e = do
   EvalEnv _ _ evaenv <- get
   let sims = aenvSimpl evaenv
   _ <- foldlM (\_ s -> mapMExpr (go s) e) e sims
   return ()
  where
    go :: Simplify -> Expr -> EvalST Expr
    go (SMeasure f dc xs bd) e@(EApp _ _)
      | (EVar dc', es) <- splitEApp e
      , dc == dc', length xs == length es
      = addSMTEquality γ (EApp (EVar f) e) (subst (mkSubst $ zip xs es) bd)
      >> return e
    go _ e
      = return e

-------------------------------
-- Symbolic Evaluation with SMT
-------------------------------
data EvalEnv = forall a . EvalEnv { evId        :: Int
                                  , evSequence  :: [(Expr,Expr)]
                                  , _evAEnv      :: AxiomEnv a
                                  }

type EvalST a = StateT EvalEnv IO a

evaluate :: [(Symbol, SortedReft)] -> SEnv Sort -> FuelMap -> AxiomEnv c -> [Expr] -> IO [(Expr, Expr)]
evaluate facts fenv _ aenv einit
  = (eqs ++) <$> (fmap join . sequence) (evalOne <$> L.nub (grepTopApps =<< einit))
  where
    (eqs, γ) = makeKnowledge aenv fenv facts
    initEvalSt = EvalEnv 0 [] aenv
    -- This adds all intermediate unfoldings into the assumptions
    -- no test needs it
    -- TODO: add a flag to enable it
    evalOne :: Expr -> IO [(Expr, Expr)]
    evalOne e = do
      (e', st) <- runStateT (eval γ $ trace aenv ("\n\nSTART EVALUATION OF\n" ++ showpp e)
                                    e) initEvalSt
      if e' == e then return [] else trace aenv
        ("\n\nEVALUATION OF \n\n" ++ showpp e ++ "\nIS\n" ++ showpp e')
        (return $ (e, e'):evSequence st)

grepTopApps :: Expr -> [Expr]
grepTopApps (PAnd es) = concatMap grepTopApps es
grepTopApps (PAtom _ e1 e2) = grepTopApps e1 ++ grepTopApps e2
grepTopApps e@(EApp _ _) = [e]
grepTopApps _ = []
-- POr    ![Expr]
-- PNot   !Expr
-- PImp   !Expr !Expr
-- PIff   !Expr !Expr

-- AT: I think makeLam is the adjoint of splitEApp?
makeLam :: Knowledge -> Expr -> Expr
makeLam γ e = foldl (flip ELam) e (knLams γ)

eval :: Knowledge -> Expr -> EvalST Expr
eval γ e | Just e' <- lookupKnowledge γ e
   = (e, "Knowledge") ~> e'
eval γ (ELam (x,s) e)
  = do let x' = makeLamArg s (1+ length (knLams γ))
       e'    <- eval γ{knLams = (x',s):knLams γ} (subst1 e (x, EVar x'))
       return $ ELam (x,s) $ subst1 e' (x', EVar x)
eval γ (PAtom r e1 e2)
  = PAtom r <$> eval γ e1 <*> eval γ e2
eval γ e@(EIte b e1 e2)
  = do b' <- eval γ b
       evalIte γ e b' e1 e2
eval γ e@(EApp _ _)
  = evalArgs γ e >>= evalApp γ e
eval _ e
  = do EvalEnv _ _ _env <- get
       return e -- trace env ("\n\nEvaluation stops at " ++ showpp e) e


evalArgs :: Knowledge -> Expr -> EvalST (Expr, [Expr])
evalArgs γ = go []
  where
    go acc (EApp f e)
      = do f' <- eval γ f
           e' <- eval γ e
           go (e':acc) f'
    go acc e
      = do e' <- eval γ e
           return (e', acc)

evalApp :: Knowledge -> Expr -> (Expr, [Expr]) -> EvalST Expr
evalApp γ e (EVar f, [ex])
  | (EVar dc, es) <- splitEApp ex
  , Just simp <- L.find (\simp -> (smName simp == f) && (smDC simp == dc)) (knSims γ)
  , length (smArgs simp) == length es
  = do e'    <- eval γ $ η $ substPopIf (zip (smArgs simp) es) (smBody simp)
       (e, "Simplify-" ++ showpp f) ~> e'

evalApp γ _ (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es
  , f `notElem` syms bd -- not recursive
  = eval γ $ η $ substPopIf (zip (eqArgs eq) es) bd
evalApp γ _e (EVar f, es)
  | Just eq <- L.find ((==f) . eqName) (knAms γ)
  , Just bd <- getEqBody eq
  , length (eqArgs eq) == length es  --  recursive
  = evalRecApplication γ (eApps (EVar f) es) $ subst (mkSubst $ zip (eqArgs eq) es) bd

evalApp _ _ (f, es)
  = return $ eApps f es


evalRecApplication :: Knowledge ->  Expr -> Expr -> EvalST Expr
evalRecApplication γ e (EIte b e1 e2)
  = do b' <- eval γ b
       b'' <- liftIO (isValid γ b')
       if b''
          then addApplicationEq γ e e1 >> assertSelectors γ e1 >> eval γ e1 >>= ((e, "App") ~>)
          else do b''' <- liftIO (isValid γ (PNot b'))
                  if b'''
                   then addApplicationEq γ e e2 >> assertSelectors γ e2 >> eval γ e2 >>= ((e, "App") ~>)
                   else return e --  T.trace ("FAIL TO EVALUATE\n" ++ showpp b' ++ "\nOR\n" ++ showpp b )  e
evalRecApplication _ _ e
  = return e

isValid :: Knowledge -> Expr -> IO Bool
isValid γ b = knPreds γ (knLams γ) b =<< knContext γ

evalIte :: Knowledge -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ e b e1 e2 = join $ evalIte' γ e b e1 e2 <$> liftIO (isValid γ b) <*> liftIO (isValid γ (PNot b))

evalIte' :: Knowledge -> Expr -> Expr -> Expr -> Expr -> Bool -> Bool -> EvalST Expr
evalIte' γ e _ e1 _ b _
  | b
  = do e' <- eval γ e1
       (e, "If-True of:" ++ showpp b)  ~> e'
evalIte' γ e _ _ e2 _ b'
  | b'
  = do e' <- eval γ e2
       (e, "If-False") ~> e'
evalIte' γ _ b e1 e2 _ _
  = do e1' <- eval γ e1
       e2' <- eval γ e2
       return $ EIte b e1' e2'

addApplicationEq :: Knowledge -> Expr -> Expr -> EvalST ()
addApplicationEq γ e1 e2 =
  modify (\st -> st{evSequence = (makeLam γ e1, makeLam γ e2):evSequence st})

substPopIf :: [(Symbol, Expr)] -> Expr -> Expr
substPopIf xes e = η $ foldl go e xes
  where
    go e (x, EIte b e1 e2) = EIte b (subst1 e (x, e1)) (subst1 e (x, e2))
    go e (x, ex)           = subst1 e (x, ex)

-- normalization required by ApplicativeMaybe.composition
η :: Expr -> Expr
η = snd . go
  where
    go (EIte b t f) | isTautoPred t && isFalse f = (True, b)
    go (EIte b e1 e2) = let (fb, b') = go b
                            (f1, e1') = go e1
                            (f2, e2') = go e2
                        in  (fb || f1 || f2, EIte b' e1' e2')
    go (EApp (EIte b f1 f2) e) = (True, EIte b (snd $ go $ EApp f1 e) (snd $ go $ EApp f2 e))
    go (EApp f (EIte b e1 e2)) = (True, EIte b (snd $ go $ EApp f e1) (snd $ go $ EApp f e2))
    go (EApp e1 e2)            = let (f1, e1') = go e1
                                     (f2, e2') = go e2
                                 in if f1 || f2 then go $ EApp e1' e2' else (False, EApp e1' e2')
    go e = (False, e)


-- Fuel
-------
type Fuel = Int
type FuelMap = [(Symbol, Fuel)]

goodFuelMap :: FuelMap -> Bool
goodFuelMap = any ((>0) . snd)

hasFuel :: FuelMap -> Symbol -> Bool
hasFuel fm x = maybe True (\x -> 0 < x) (L.lookup x fm)

makeFuelMap :: (Fuel -> Fuel) -> FuelMap -> Symbol -> FuelMap
makeFuelMap f ((x, fx):fs) y
  | x == y    = (x, f fx) : fs
  | otherwise = (x, fx)   : makeFuelMap f fs y
makeFuelMap _ _ _ = error "makeFuelMap"
{-
maxFuelMap :: [Occurence] -> FuelMap
maxFuelMap occs = mergeMax <$> L.transpose (ofuel <$> occs)
  where
    mergeMax :: FuelMap -> (Symbol, Fuel)
    mergeMax xfs = let (xs, fs) = unzip xfs in (head xs, maximum fs)
-}

-----------------------------
-- Naieve evaluation strategy
-----------------------------
data Occurence = Occ {_ofun :: Symbol, _oargs :: [Expr], ofuel :: FuelMap}
 deriving (Show)

instances :: Int -> AxiomEnv c -> [Occurence] -> [Expr]
instances maxIs aenv !occs
  = instancesLoop aenv maxIs eqs occs -- (eqBody <$> eqsZero) ++ is
  where
    eqs = filter (not . null . eqArgs) (aenvEqs  aenv)

-- Currently: Instantiation happens arbitrary times (in recursive functions it diverges)
-- Step 1: Hack it so that instantiation of axiom A happens from an occurences and its
-- subsequent instances <= FUEL times
-- How? Hack expressions to contatin fuel info within eg Cst
-- Step 2: Compute fuel based on Ranjit's algorithm

instancesLoop :: AxiomEnv c ->  Int -> [Equation] -> [Occurence] -> [Expr]
instancesLoop aenv maxIns eqs = go 0 []
  where
    go :: Int -> [Expr] -> [Occurence] -> [Expr]
    go !i acc occs = let is      = concatMap (unfold eqs) occs
                         newIs   = findNewEqs is acc
                         newOccs = concatMap (grepOccurences eqs) newIs
                         msg     = show (i + length newIs) ++ "/" ++ show maxIns ++ "\t\t"
                     in  if null newIs then acc else go (trace aenv msg (i + length newIs)) ((fst <$> newIs) ++ acc) newOccs

findNewEqs :: [(Expr, FuelMap)] -> [Expr] -> [(Expr, FuelMap)]
findNewEqs [] _ = []
findNewEqs ((e, f):xss) es
  | e `elem` es = findNewEqs xss es
  | otherwise   = (e,f):findNewEqs xss es

makeInitOccurences :: [(Symbol, Fuel)] -> [Equation] -> Expr -> [Occurence]
makeInitOccurences xs eqs e
  = [Occ x es xs | (EVar x, es) <- splitEApp <$> eapps e
                 , Equ x' xs' _ <- eqs, x == x'
                 , length xs' == length es]

grepOccurences :: [Equation] -> (Expr, FuelMap) -> [Occurence]
grepOccurences eqs (e, fs)
  = filter (goodFuelMap . ofuel)
           [Occ x es fs | (EVar x, es) <- splitEApp <$> eapps e
                        , Equ x' xs' _ <- eqs, x == x'
                        , length xs' == length es]

unfold :: [Equation] -> Occurence -> [(Expr, FuelMap)]
unfold eqs (Occ x es fs)
  = catMaybes [if hasFuel fs x then Just (subst (mkSubst $ zip  xs' es) e, makeFuelMap (\x -> x-1) fs x) else Nothing
              | Equ x' xs' e <- eqs
              , x == x'
              , length xs' == length es]


{-
showExpr :: Expr -> String
showExpr (PAnd eqs)
  = L.intercalate "\n" (showpp . lhs <$> eqs )
  where
    lhs (PAtom Eq l _) = l
    lhs e                = e
showExpr e = showpp e
-}


instance Expression (Symbol, SortedReft) where
  expr (x, RR _ (Reft (v, r))) = subst1 (expr r) (v, EVar x)
