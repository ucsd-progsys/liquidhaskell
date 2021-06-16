{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Language.Fixpoint.Solver.Rewrite
  ( getRewrite
  , getRewrite'
  , subExprs
  , unify
  , ordConstraints
  , convert
  , passesTerminationCheck
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
import Text.PrettyPrint (text)
import           Language.REST
import           Language.REST.AbstractOC
import qualified Language.REST.RuntimeTerm as RT
import           Language.REST.Op
import           Language.REST.OrderingConstraints as OC
import           Language.REST.Core (orient)

import Debug.Trace

type SubExpr = (Expr, Expr -> Expr)

data TermOrigin = PLE | RW deriving (Show, Eq)

instance PPrint TermOrigin where
  pprintTidy _ = text . show

data DivergeResult = Diverging | NotDiverging

fromRW :: TermOrigin -> Bool
fromRW RW  = True
fromRW PLE = False

data RWTerminationOpts =
    RWTerminationCheckEnabled (Maybe Int) -- # Of constraints to consider
  | RWTerminationCheckDisabled

data RewriteArgs = RWArgs
 { isRWValid          :: Expr -> IO Bool
 , rwTerminationOpts  :: RWTerminationOpts
 }

ordConstraints = contramap convert defaultOC


convert :: Expr -> RT.RuntimeTerm
convert (EIte i t e) = RT.App "$ite" $ map convert [i,t,e]
convert (EApp (EVar s) (EVar var))
  | "lqdc" `isPrefixOfSym` s
  = RT.App (Op $ TX.unpack $ TX.concat [symbolText s, "$", symbolText var]) []

convert e@(EApp{})    | (EVar fName, terms) <- splitEApp e
                      = RT.App (Op (symbolString fName)) $ map convert terms
convert (EVar s)      = RT.App (Op (symbolString s)) []
convert (PAnd es)     = RT.App "$and" $ map convert es
convert (POr es)      = RT.App "$or" $ map convert es
convert (PAtom s l r) = RT.App (Op $ "$atom" ++ show s) [convert l, convert r]
convert (EBin o l r)  = RT.App (Op $ "$ebin" ++ show o) [convert l, convert r]
convert (ECon c)      = RT.App (Op $ "$econ" ++ show c) []
convert e             = error (show e)

passesTerminationCheck :: AbstractOC oc a -> RewriteArgs -> oc -> Bool
passesTerminationCheck aoc rwArgs c =
  case rwTerminationOpts rwArgs of
    RWTerminationCheckEnabled _ -> isSat aoc c
    RWTerminationCheckDisabled  -> True

getRewrite' ::
     RewriteArgs
  -> SubExpr
  -> AutoRewrite
  -> MaybeT IO Expr
getRewrite' rwArgs (subE, toE) (AutoRewrite args lhs rhs) =
  do
    su <- MaybeT $ return $ unify freeVars lhs subE
    let subE' = subst su rhs
    mapM_ (check . subst su) exprs
    let expr' = toE subE'
    return expr'
  where
    check :: Expr -> MaybeT IO ()
    check e = do
      valid <- MaybeT $ Just <$> isRWValid rwArgs e
      guard valid

    freeVars = [s | RR _ (Reft (s, _)) <- args ]
    exprs    = [e | RR _ (Reft (_, e)) <- args ]

getRewrite ::
     AbstractOC oc Expr
  -> RewriteArgs
  -> oc
  -> SubExpr
  -> AutoRewrite
  -> MaybeT IO (Expr, oc)
getRewrite aoc rwArgs c (subE, toE) (AutoRewrite args lhs rhs) =
  do
    su <- MaybeT $ return $ unify freeVars lhs subE
    let subE' = subst su rhs
    let expr  = toE subE
    let expr' = toE subE'
    -- lift $ putStrLn $ "Unified " ++ (show subE) ++ " to " ++ (show subE')
    mapM_ (check . subst su) exprs
    -- lift $ putStrLn $ (show $ convert expr) ++ " -> " ++ (show $ convert expr')
    return $ case rwTerminationOpts rwArgs of
      RWTerminationCheckEnabled _ ->
        let
          c' = refine aoc c expr expr'
        in
          (expr', c')
      RWTerminationCheckDisabled -> (expr', c)
  where
    check :: Expr -> MaybeT IO ()
    check e = do
      valid <- MaybeT $ Just <$> isRWValid rwArgs e
      guard valid

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

subExprs' e@(EApp{}) = concatMap replace indexedArgs
  where
    (f, es)          = splitEApp e
    indexedArgs      = zip [0..] es
    replace (i, arg) = do
      (subArg, toArg) <- subExprs arg
      return (subArg, \subArg' -> eApps f $ (take i es) ++ (toArg subArg'):(drop (i+1) es))

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
  (EVar lhs, EVar rhs) | removeModName lhs == removeModName rhs ->
                         Just (Su M.empty)
    where
      removeModName ts = go "" (symbolString ts) where
        go buf []         = buf
        go _   ('.':rest) = go [] rest
        go buf (x:xs)     = go (buf ++ [x]) xs
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
