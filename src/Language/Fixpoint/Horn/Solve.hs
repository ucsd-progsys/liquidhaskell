-------------------------------------------------------------------------------
-- | This module defines a function to solve NNF constraints,
--   by reducing them to the standard FInfo.
-------------------------------------------------------------------------------

module Language.Fixpoint.Horn.Solve (solveHorn, solve) where

import System.Exit ( ExitCode )
import Control.DeepSeq ( NFData )
import Control.Monad (when)
import qualified Language.Fixpoint.Misc         as Misc
import qualified Language.Fixpoint.Utils.Files  as Files
import qualified Language.Fixpoint.Solver       as Solver
import qualified Language.Fixpoint.Parse        as Parse
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Horn.Parse   as H
import qualified Language.Fixpoint.Horn.Transformations as Tx
import Text.PrettyPrint.HughesPJ.Compat ( render )
import Language.Fixpoint.Horn.Info ( hornFInfo )

import System.Console.CmdArgs.Verbosity ( whenLoud )

-- import Debug.Trace (traceM)

----------------------------------------------------------------------------------
solveHorn :: F.Config -> IO ExitCode
----------------------------------------------------------------------------------
solveHorn cfg = do
  (q, opts) <- parseQuery cfg
  
  -- If you want to set --eliminate=none, you better make it a pragma
  cfg <- if F.eliminate cfg == F.None
           then pure (cfg { F.eliminate =  F.Some })
           else pure cfg
  
  cfg <- F.withPragmas cfg opts

  when (F.save cfg) (saveHornQuery cfg q)

  r <- solve cfg q
  Solver.resultExitCode cfg r

parseQuery :: F.Config -> IO (H.Query H.Tag, [String])
parseQuery cfg 
  | F.stdin cfg = Parse.parseFromStdIn H.hornP
  | otherwise   = Parse.parseFromFile H.hornP (F.srcFile cfg)

saveHornQuery :: F.Config -> H.Query H.Tag -> IO ()
saveHornQuery cfg q = do
  let hq   = F.queryFile Files.HSmt2 cfg
  putStrLn $ "Saving Horn Query: " ++ hq ++ "\n"
  Misc.ensurePath hq
  writeFile hq $ render (F.pprint q)

----------------------------------------------------------------------------------
eliminate :: (F.PPrint a) => F.Config -> H.Query a -> IO (H.Query a)
----------------------------------------------------------------------------------
eliminate cfg q
  | F.eliminate cfg == F.Existentials = do
    Tx.solveEbs cfg q
  | F.eliminate cfg == F.Horn = do
    let c = Tx.elim $ H.qCstr q
    whenLoud $ putStrLn "Horn Elim:"
    whenLoud $ putStrLn $ F.showpp c
    pure $ q { H.qCstr = c }
  | otherwise = pure q

----------------------------------------------------------------------------------
solve :: (F.PPrint a, NFData a, F.Loc a, Show a, F.Fixpoint a) => F.Config -> H.Query a
       -> IO (F.Result (Integer, a))
----------------------------------------------------------------------------------
solve cfg q = do
  let c = Tx.uniq $ Tx.flatten $ H.qCstr q
  whenLoud $ putStrLn "Horn Uniq:"
  whenLoud $ putStrLn $ F.showpp c
  q <- eliminate cfg ({- void $ -} q { H.qCstr = c })
  Solver.solve cfg (hornFInfo cfg q)

