{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternGuards             #-}

module Language.Fixpoint.Solver.Rewrite
  ( getRewrite
  , subExprs
  , unify
  , RewriteArgs(..)
  , RWTerminationOpts(..)
  , SubExpr
  , TermOrigin(..)
  ) where

import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           GHC.Generics
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb
import           Language.Fixpoint.Types hiding (simplify)
import qualified Data.Text as TX

type Op = Symbol
type OpOrdering = [Symbol]
data Term = Term Symbol [Term] deriving (Eq, Generic)
instance Hashable Term

termSym :: Term -> Symbol
termSym (Term s _) = s

instance Show Term where
  show (Term op [])   = TX.unpack $ symbolText op
  show (Term op args) =
    TX.unpack (symbolText op) ++ "(" ++ L.intercalate ", " (map show args) ++ ")"

data SCDir =
    SCUp
  | SCEq 
  | SCDown
  deriving (Eq, Ord, Show, Generic)

instance Hashable SCDir

type SCPath = ((Op, Int), (Op, Int), [SCDir])
type SubExpr = (Expr, Expr -> Expr)

data SCEntry = SCEntry {
    from :: (Op, Int)
  , to   :: (Op, Int)
  , dir  :: SCDir
} deriving (Eq, Ord, Show, Generic)

instance Hashable SCEntry

getDir :: OpOrdering -> Term -> Term -> SCDir
getDir o from to =
  case (synGTE o from to, synGTE o to from) of
      (True, True)  -> SCEq
      (True, False) -> SCDown
      (False, _)    -> SCUp

getSC :: OpOrdering -> Term -> Term -> S.HashSet SCEntry
getSC o (Term op ts) (Term op' us) = 
  S.fromList $ do
    (i, from) <- zip [0..] ts
    (j, to)   <- zip [0..] us
    return $ SCEntry (op, i) (op', j) (getDir o from to)

scp :: OpOrdering -> [Term] -> S.HashSet SCPath
scp _ []       = S.empty
scp _ [_]      = S.empty
scp o [t1, t2] = S.fromList $ do
  (SCEntry a b d) <- S.toList $ getSC o t1 t2
  return (a, b, [d])
scp o (t1:t2:trms) = S.fromList $ do
  (SCEntry a b' d) <- S.toList $ getSC o t1 t2
  (a', b, ds)      <- S.toList $ scp o (t2:trms)
  guard $ b' == a'
  return (a, b, d:ds)

synEQ :: OpOrdering -> Term -> Term -> Bool
synEQ o l r = synGTE o l r && synGTE o r l

opGT :: OpOrdering -> Op -> Op -> Bool
opGT ordering op1 op2 = case (L.elemIndex op1 ordering, L.elemIndex op2 ordering) of
  (Just index1, Just index2) -> index1 < index2
  (Just _, Nothing)          -> True
  _                          -> False

removeSynEQs :: OpOrdering -> [Term] -> [Term] -> ([Term], [Term])
removeSynEQs _ [] ys      = ([], ys)
removeSynEQs ordering (x:xs) ys
  | Just yIndex <- L.findIndex (synEQ ordering x) ys
  = removeSynEQs ordering xs $ take yIndex ys ++ drop (yIndex + 1) ys
  | otherwise =
    let
      (xs', ys') = removeSynEQs ordering xs ys
    in
      (x:xs', ys')

synGTEM :: OpOrdering -> [Term] -> [Term] -> Bool
synGTEM ordering xs ys =     
  case removeSynEQs ordering xs ys of
    (_   , []) -> True
    (xs', ys') -> any (\x -> all (synGT ordering x) ys') xs'
    
synGT :: OpOrdering -> Term -> Term -> Bool
synGT o t1 t2 = synGTE o t1 t2 && not (synGTE o t2 t1)

synGTM :: OpOrdering -> [Term] -> [Term] -> Bool
synGTM o t1 t2 = synGTEM o t1 t2 && not (synGTEM o t2 t1)

synGTE :: OpOrdering -> Term -> Term -> Bool
synGTE ordering t1@(Term x tms) t2@(Term y tms') =
  if opGT ordering x y then
    synGTM ordering [t1] tms'
  else if opGT ordering y x then
    synGTEM ordering tms [t2]
  else
    synGTEM ordering tms tms'

subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

data TermOrigin = PLE | RW OpOrdering deriving (Show, Eq)

data DivergeResult = Diverging | NotDiverging OpOrdering

fromRW :: TermOrigin -> Bool
fromRW (RW _) = True
fromRW PLE    = False

getOrdering :: TermOrigin -> Maybe OpOrdering
getOrdering (RW o) = Just o
getOrdering PLE    = Nothing

diverges :: Maybe Int -> [(Term, TermOrigin)] -> Term -> DivergeResult
diverges maxOrderingConstraints path term = go 0
  where
   path' = map fst path ++ [term]
   go n |    n > length syms'
          || n > Mb.fromMaybe (length syms') maxOrderingConstraints = Diverging
   go n = case L.find (not . diverges') (orderings' n) of
     Just ordering -> NotDiverging ordering
     Nothing       -> go (n + 1)
   ops (Term o xs) = o:concatMap ops xs
   syms'           = L.nub $ concatMap ops path'
   suggestedOrderings :: [OpOrdering]
   suggestedOrderings =
     reverse $ Mb.catMaybes $ map (getOrdering . snd) path
   orderings' n    =
     suggestedOrderings ++ concatMap L.permutations ((subsequencesOfSize n) syms')
   diverges' o     = divergesFor o path term

divergesFor :: OpOrdering -> [(Term, TermOrigin)] -> Term -> Bool
divergesFor o path term = any diverges' terms'
  where
    terms = map fst path ++ [term]
    lastRWIndex =
      Mb.fromMaybe 0 (fmap fst $ L.find (fromRW . snd . snd) $ reverse $ zip [1..] path) 
    okTerms    = take lastRWIndex terms
    checkTerms = drop lastRWIndex terms
    terms' = L.subsequences checkTerms ++ do
      firstpart  <- L.tails okTerms
      secondpart <- L.inits checkTerms
      return $ firstpart ++ secondpart
    diverges' :: [Term] -> Bool
    diverges' trms' =
      if length trms' <= 1 || termSym (head trms') /= termSym (last trms') then
        False
      else
        any ascending (scp o trms') && all (not . descending) (scp o trms')
      
descending :: SCPath -> Bool
descending (a, b, ds) = a == b && L.elem SCDown ds && L.notElem SCUp ds

ascending :: SCPath -> Bool
ascending  (a, b, ds) = a == b && L.elem SCUp ds

data RWTerminationOpts =
    RWTerminationCheckEnabled (Maybe Int) -- # Of constraints to consider
  | RWTerminationCheckDisabled

data RewriteArgs = RWArgs
 { isRWValid          :: Expr -> IO Bool
 , rwTerminationOpts  :: RWTerminationOpts
 }

getRewrite :: RewriteArgs -> [(Expr, TermOrigin)] -> SubExpr -> AutoRewrite -> MaybeT IO (Expr, TermOrigin)
getRewrite rwArgs path (subE, toE) (AutoRewrite args lhs rhs) =
  do
    su <- MaybeT $ return $ unify freeVars lhs subE
    let subE' = subst su rhs
    let expr' = toE subE'
    guard $ all ( (/= expr') . fst) path
    mapM_ (check . subst su) exprs
    let termPath = map (\(t, o) -> (convert t, o)) path
    case rwTerminationOpts rwArgs of
      RWTerminationCheckEnabled maxConstraints ->
        case diverges maxConstraints termPath (convert expr') of
          NotDiverging opOrdering  ->
            return (expr', RW opOrdering)
          Diverging ->
            mzero
      RWTerminationCheckDisabled -> return (expr', RW [])
  where
    
    convert (EIte i t e) = Term "$ite" $ map convert [i,t,e]
    convert (EApp (EVar s) (EVar var))
      | dcPrefix `isPrefixOfSym` s
      = Term (symbol $ TX.concat [symbolText s, "$", symbolText var]) []
     
    convert e@(EApp{})    | (EVar fName, terms) <- splitEApp e
                          = Term fName $ map convert terms
    convert (EVar s)      = Term s []                  
    convert (PAnd es)     = Term "$and" $ map convert es
    convert (POr es)      = Term "$or" $ map convert es
    convert (PAtom s l r) = Term (symbol $ "$atom" ++ show s) [convert l, convert r]
    convert (EBin o l r)  = Term (symbol $ "$ebin" ++ show o) [convert l, convert r]
    convert (ECon c)      = Term (symbol $ "$econ" ++ show c) []
    convert e             = error (show e)
    
    
    check :: Expr -> MaybeT IO ()
    check e = do
      valid <- MaybeT $ Just <$> isRWValid rwArgs e
      guard valid
      
    dcPrefix = "lqdc"

    freeVars = [s | RR _ (Reft (s, _)) <- args ]
    exprs    = [e | RR _ (Reft (_, e)) <- args ]

subExprs :: Expr -> [SubExpr]
subExprs e = (e,id):subExprs' e

subExprs' :: Expr -> [SubExpr]
subExprs' (EIte c lhs rhs)  = c'' ++ l'' ++ r''
  where
    c' = subExprs c
    l' = subExprs lhs
    r' = subExprs rhs
    c'' = map (\(e, f) -> (e, \e' -> EIte (f e') lhs rhs)) c'
    l'' = map (\(e, f) -> (e, \e' -> EIte c (f e') rhs)) l'
    r'' = map (\(e, f) -> (e, \e' -> EIte c lhs (f e'))) r'
    
subExprs' (EBin op lhs rhs) = lhs'' ++ rhs''
  where
    lhs' = subExprs lhs
    rhs' = subExprs rhs
    lhs'' :: [SubExpr]
    lhs'' = map (\(e, f) -> (e, \e' -> EBin op (f e') rhs)) lhs'
    rhs'' :: [SubExpr]
    rhs'' = map (\(e, f) -> (e, \e' -> EBin op lhs (f e'))) rhs'
    
subExprs' (PImp lhs rhs) = lhs'' ++ rhs''
  where
    lhs' = subExprs lhs
    rhs' = subExprs rhs
    lhs'' :: [SubExpr]
    lhs'' = map (\(e, f) -> (e, \e' -> PImp (f e') rhs)) lhs'
    rhs'' :: [SubExpr]
    rhs'' = map (\(e, f) -> (e, \e' -> PImp lhs (f e'))) rhs'
    
subExprs' (PAtom op lhs rhs) = lhs'' ++ rhs''
  where
    lhs' = subExprs lhs
    rhs' = subExprs rhs
    lhs'' :: [SubExpr]
    lhs'' = map (\(e, f) -> (e, \e' -> PAtom op (f e') rhs)) lhs'
    rhs'' :: [SubExpr]
    rhs'' = map (\(e, f) -> (e, \e' -> PAtom op lhs (f e'))) rhs'

-- subExprs' e@(EApp{}) = concatMap replace indexedArgs
--   where
--     (f, es)          = splitEApp e
--     indexedArgs      = zip [0..] es
--     replace (i, arg) = do
--       (subArg, toArg) <- subExprs arg
--       return (subArg, \subArg' -> eApps f $ (take i es) ++ (toArg subArg'):(drop (i+1) es))
      
subExprs' _ = []

unifyAll :: [Symbol] -> [Expr] -> [Expr] -> Maybe Subst
unifyAll _ []     []               = Just (Su M.empty)
unifyAll freeVars (template:xs) (seen:ys) =
  do
    rs@(Su s1) <- unify freeVars template seen
    let xs' = map (subst rs) xs
    let ys' = map (subst rs) ys
    (Su s2) <- unifyAll (freeVars L.\\ M.keys s1) xs' ys'
    return $ Su (M.union s1 s2)
unifyAll _ _ _ = undefined

unify :: [Symbol] -> Expr -> Expr -> Maybe Subst
unify _ template seenExpr | template == seenExpr = Just (Su M.empty)
unify freeVars template seenExpr = case (template, seenExpr) of
  (EVar rwVar, _) | rwVar `elem` freeVars ->
    return $ Su (M.singleton rwVar seenExpr)
  (EApp templateF templateBody, EApp seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (ENeg rw, ENeg seen) ->
    unify freeVars rw seen
  (EBin op rwLeft rwRight, EBin op' seenLeft seenRight) | op == op' ->
    unifyAll freeVars [rwLeft, rwRight] [seenLeft, seenRight]
  (EIte cond rwLeft rwRight, EIte seenCond seenLeft seenRight) ->
    unifyAll freeVars [cond, rwLeft, rwRight] [seenCond, seenLeft, seenRight]
  (ECst rw _, ECst seen _) ->
    unify freeVars rw seen
  (ETApp rw _, ETApp seen _) ->
    unify freeVars rw seen
  (ETAbs rw _, ETAbs seen _) ->
    unify freeVars rw seen
  (PAnd rw, PAnd seen ) ->
    unifyAll freeVars rw seen
  (POr rw, POr seen ) ->
    unifyAll freeVars rw seen
  (PNot rw, PNot seen) ->
    unify freeVars rw seen
  (PImp templateF templateBody, PImp seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PIff templateF templateBody, PIff seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PAtom rel templateF templateBody, PAtom rel' seenF seenBody) | rel == rel' ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PAll _ rw, PAll _ seen) ->
    unify freeVars rw seen
  (PExist _ rw, PExist _ seen) ->
    unify freeVars rw seen
  (PGrad _ _ _ rw, PGrad _ _ _ seen) ->
    unify freeVars rw seen
  (ECoerc _ _ rw, ECoerc _ _ seen) ->
    unify freeVars rw seen
  _ -> Nothing
