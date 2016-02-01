{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
module Language.Haskell.Liquid.Model where

import           Control.Monad
import qualified Data.HashMap.Lazy as HashMap

import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Types hiding (ofReft, reft)
import           Language.Fixpoint.Types.Config (SMTSolver(..))
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.RefType


getModels :: Config -> FixResult Cinfo -> IO ()
getModels cfg (Unsafe cs) = mapM_ (getModel cfg) cs
getModels _ _ = return ()

getModel :: Config -> Cinfo -> IO ()
getModel cfg Ci { ci_err = Just (ErrSubType { ctx, tact, texp }) } = do
  smt <- makeContext True Z3 "model.smt2"
  let print = putStrLn . showpp
  forM_ (HashMap.toList ctx) $ \(v, t) -> do
    putStrLn $ showpp (v,t)
    smtDecl smt v FInt
  let vv = rTypeValueVar tact
  smtDecl smt vv FInt
  forM_ (HashMap.toList ctx) $ \(v, t) -> do    
    smtAssert smt $ ofReft (reft t) (EVar v)
  print tact
  smtAssert smt $ ofReft (reft tact) (EVar vv)
  print texp
  smtAssert smt $ PNot $ ofReft (reft texp) (EVar vv)
  r <- command smt CheckSat
  let print = putStrLn . show
  print r
  r <- command smt (GetValue [vv])
  print r
  undefined
  return ()

getModel _ _ = return ()


-- | Given a refinement @{v | p}@ and an expression @e@, construct
-- the predicate @p[e/v]@.
ofReft :: Reft -> Expr -> Expr
ofReft (Reft (v, p)) e
  = let x = mkSubst [(v, e)]
    in subst x p

reft :: SpecType -> Reft
reft = rTypeReft -- toReft . rt_reft
