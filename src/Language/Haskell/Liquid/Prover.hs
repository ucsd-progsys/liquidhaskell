module Main where

import System.Environment             (getArgs)

import Language.Haskell.Liquid.Prover.Solve
import Language.Haskell.Liquid.Prover.Parser

import Language.Haskell.Liquid.Prover.Pretty ()

main :: IO ()
main = getArgs >>= (runSolver . head)


runSolver :: FilePath -> IO ()
runSolver fn = 
  do query <- parseQuery fn
     sol   <- solve query
     putStrLn ("\nInput = \n" ++ show query)     
     putStrLn ("\nOuput = \n" ++ show sol)
