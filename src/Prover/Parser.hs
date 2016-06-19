module Prover.Parser where

import Prover.Types
import Prover.Constants (default_depth)

import Text.Parsec

import Language.Fixpoint.Parse hiding (bindP)
import Language.Fixpoint.Types        (Expr(PAnd), symbol, Sort(FObj))

parseQuery :: String -> IO LQuery
parseQuery fn = parseFromFile (queryP fn) fn

queryP :: FilePath -> Parser LQuery
queryP fn = do
  n      <- depthP
  bs     <- sepBy envP   whiteSpace
  semi
  vars   <- sepBy bindP  whiteSpace
  semi
  ds     <- declsP
  axioms <- sepBy axiomP whiteSpace
  semi
  ctors  <- sepBy ctorP  whiteSpace
  semi
  goal   <- goalP
  return $ mempty { q_axioms = axioms
                  , q_vars   = vars
                  , q_ctors  = ctors
                  , q_goal   = goal
                  , q_fname  = fn
                  , q_depth  = n
                  , q_env    = bs
                  , q_decls  = ds
                  }


declsP :: Parser [Predicate]
declsP = try (do {n <- sepBy declP whiteSpace; semi; return n} )
      <|> return []

declP :: Parser Predicate
declP = reserved "declare" >> predicateP

depthP :: Parser Int
depthP = try (do {reserved "depth"; reserved "="; n <- fromInteger <$> integer; semi; return n} )
      <|> return default_depth

goalP :: Parser Predicate
goalP = reserved "goal" >> colon >> predicateP

ctorP :: Parser LVarCtor
ctorP = do reserved "constructor"
           v <- varP
           (vs, p) <- try ctorAxiomP
           return $ VarCtor v vs p

ctorAxiomP :: Parser ([LVar], Predicate)
ctorAxiomP
   =  do reserved "with"
         reserved "forall"
         aargs <- argumentsP
         abody <- predicateP
         return (aargs, abody)
  <|> return ([], Pred $ PAnd [])

bindP :: Parser LVar
bindP = reserved "bind" >> varP

envP :: Parser LVar
envP = reserved "constant" >> varP

predicateP :: Parser Predicate
predicateP = Pred <$> predP

axiomP :: Parser LAxiom
axiomP = do
  reserved "axiom"
  aname <- mkVar <$> symbolP
  colon
  reserved "forall"
  aargs <- argumentsP
  abody <- predicateP
  return $ Axiom aname aargs abody
 where
   dummySort = FObj (symbol "dummySort")
   mkVar x   = Var x dummySort ()


argumentsP :: Parser [LVar]
argumentsP = brackets $ sepBy varP comma

varP :: Parser LVar
varP = do
  x <- symbolP
  colon
  s <- sortP
  return $ Var x s ()
