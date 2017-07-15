{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ViewPatterns               #-}
module Test.Target.Monad
  ( whenVerbose
  , noteUsed
  , addDep
  , addConstraint
  , addConstructor
  , addSort
  , addVariable
  , inModule
  , making
  , lookupCtor
  , guarded
  , fresh
  , freshChoice
  , freshInt
  , getValue
  , Target, runTarget
  , TargetState(..), initState
  , TargetOpts(..), defaultOpts
  ) where

import           Control.Applicative
import           Control.Arrow                    (first, second, (***))
import qualified Control.Exception                as Ex
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.HashMap.Strict              as M
import qualified Data.HashSet                     as S
import           Data.IORef
import           Data.List                        hiding (sort)

import qualified Data.Text                        as ST
import           System.IO.Unsafe
-- import           Text.Printf

import           Language.Fixpoint.Smt.Interface  hiding (SMTLIB2(..))
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config (SMTSolver(..))
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RefType

import           Language.Haskell.Liquid.Types    hiding (var, Target)

import qualified GHC
import qualified Type as GHC

-- import           Test.Target.Serialize
import           Test.Target.Types
import           Test.Target.Util

-- import           Debug.Trace


newtype Target a = Target (StateT TargetState (ReaderT TargetOpts IO) a)
  deriving ( Functor, Applicative, Monad, MonadIO, Alternative
           , MonadState TargetState, MonadCatch, MonadReader TargetOpts )
instance MonadThrow Target where
  throwM = Ex.throw

runTarget :: TargetOpts -> TargetState -> Target a -> IO a
runTarget opts st (Target x) = runReaderT (evalStateT x st) opts

-- evalTarget :: TargetOpts -> TargetState -> Target a -> IO a
-- evalTarget o s (Target x) = runReaderT (evalStateT x s) o

-- execTarget :: GhcSpec -> Target a -> IO TargetState
-- execTarget e (Target x) = execStateT x (initGS e)

seed :: IORef Int
seed = unsafePerformIO $ newIORef 0
{-# NOINLINE seed #-}

freshInt :: Target Int
freshInt = liftIO $ do
  n <- readIORef seed
  modifyIORef' seed (+1)
  return n

data TargetOpts = TargetOpts
  { depth      :: !Int
  , solver     :: !SMTSolver
  , verbose    :: !Bool
  , logging    :: !Bool
  , keepGoing  :: !Bool
    -- ^ whether to keep going after finding a counter-example, useful for
    -- checking coverage
  , maxSuccess :: !(Maybe Int)
    -- ^ whether to stop after a certain number of successful tests, or
    -- enumerate the whole input space
  , scDepth    :: !Bool
    -- ^ whether to use SmallCheck's notion of depth
  , ghcOpts    :: ![String]
    -- ^ extra options to pass to GHC
  }

defaultOpts :: TargetOpts
defaultOpts = TargetOpts
  { depth = 3
  , solver = Z3
  , verbose = False
  , logging = True
  , keepGoing = False
  , maxSuccess = Nothing
  , scDepth = True
  , ghcOpts = []
  }

data TargetState = TargetState
  { variables    :: ![Variable]
  , choices      :: ![Variable]
  , constraints  :: !Constraint
  , deps         :: !(M.HashMap Symbol [Symbol])
  , realized     :: ![(Symbol, Value)]
  -- , dconEnv      :: ![(Symbol, DataConP)]
  , ctorEnv      :: !DataConEnv
  , measEnv      :: !MeasureEnv
  , embEnv       :: !(TCEmb GHC.TyCon)
  , tyconInfo    :: !(M.HashMap GHC.TyCon RTyCon)
  , freesyms     :: ![(Symbol,Symbol)]
  , constructors :: ![Variable] -- (S.HashSet Variable)  --[(String, String)]
  , sigs         :: ![(Symbol, SpecType)]
  , chosen       :: !(Maybe Symbol)
  , sorts        :: !(S.HashSet Sort)
  , modName      :: !Symbol
  , filePath     :: !FilePath
  , makingTy     :: !Sort
  , smtContext   :: !Context
  }

initState :: FilePath -> GhcSpec -> Context -> TargetState
initState fp sp ctx = TargetState
  { variables    = []
  , choices      = []
  , constraints  = []
  , deps         = mempty
  , realized     = []
  -- , dconEnv      = dcons
  , ctorEnv      = cts
  , measEnv      = meas
  , embEnv       = gsTcEmbeds sp
  , tyconInfo    = tyi
  , freesyms     = free
  , constructors = []
  , sigs         = sigs
  , chosen       = Nothing
  , sorts        = S.empty
  , modName      = ""
  , filePath     = fp
  , makingTy     = FObj ""
  , smtContext   = ctx
  }
  where
    -- FIXME: can we NOT tidy???
    -- dcons = tidyF $ map (first symbol) (gsDconsP sp)

    -- NOTE: we want to tidy all occurrences of nullary datacons in the signatures
    cts   = subst su $ tidyF $ map (symbol *** val) (gsCtors sp)
    sigs  = subst su $ tidyF $ map (symbol *** val) $ gsTySigs sp

    tyi   = makeTyConInfo (gsTconsP sp)
    free  = tidyS $ map (second symbol)
          $ gsFreeSyms sp ++ map (\(c,_) -> (symbol c, c)) (gsCtors sp)
    meas  = gsMeasures sp
    tidyF = map (first tidySymbol)
    tidyS = map (second tidySymbol)
    su = mkSubst (map (second eVar) free)

whenVerbose :: Target () -> Target ()
whenVerbose x
  = do v <- asks verbose
       when v x

noteUsed :: (Symbol, Value) -> Target ()
noteUsed (v,x) = modify $ \s@(TargetState {..}) -> s { realized = (v,x) : realized }

-- TODO: does this type make sense? should it be Symbol -> Symbol -> Target ()?
addDep :: Symbol -> Expr -> Target ()
addDep from (EVar to) = modify $ \s@(TargetState {..}) ->
  s { deps = M.insertWith (flip (++)) from [to] deps }
addDep _ _ = return ()

addConstraint :: Expr -> Target ()
addConstraint p = modify $ \s@(TargetState {..}) -> s { constraints = p:constraints }

addConstructor :: Variable -> Target ()
addConstructor c
  = modify $ \s@(TargetState {..}) -> s { constructors = nub $ c:constructors }

inModule :: Symbol -> Target a -> Target a
inModule m act
  = do m' <- gets modName
       modify $ \s -> s { modName = m }
       r <- act
       modify $ \s -> s { modName = m' }
       return r

making :: Sort -> Target a -> Target a
making ty act
  = do ty' <- gets makingTy
       modify $ \s -> s { makingTy = ty }
       r <- act
       modify $ \s -> s { makingTy = ty' }
       return r

-- | Find the refined type of a data constructor.
lookupCtor :: Symbol -> SpecType -> Target SpecType
lookupCtor c (toType -> t)
             -- FIXME: WTF, how do two symbols share a Text
             -- without being equal??
  = do mt <- find (\(c', _) -> symbolText c == symbolText c')
               <$> gets ctorEnv
       case mt of
         Just (_, t) -> return t
         Nothing -> do
           -- m  <- gets filePath
           -- o  <- asks ghcOpts
           let tc = GHC.tyConAppTyCon t
           let dcs = GHC.tyConDataCons tc
           let Just dc = find (\d -> c == symbol (GHC.getName d)) dcs
           let t = ofType (GHC.dataConUserType dc)
           -- t <- io $ runGhc o $ do
           --        _ <- loadModule m
           --        traceShowM c
           --        t <- GHC.exprType (printf "(%s)" (symbolString c))
           --        return (ofType t)
           modify $ \s@(TargetState {..}) -> s { ctorEnv = (c,t) : ctorEnv }
           return t

-- | Given a data constructor @d@ and an action, create a new choice variable
-- @c@ and execute the action while guarding any generated constraints with
-- @c@. Returns @(action-result, c)@.
guarded :: String -> Target Expr -> Target (Expr, Expr)
guarded cn act
  = do c  <- freshChoice cn
       mc <- gets chosen
       modify $ \s -> s { chosen = Just c }
       x <- act
       modify $ \s -> s { chosen = mc }
       return (x, EVar c)

-- | Generate a fresh variable of the given 'Sort'.
fresh :: Sort -> Target Symbol
fresh sort
  = do n <- freshInt
       let sorts' = sortTys sort
       let x = symbol $ ST.unpack (ST.intercalate "->" $ map (symbolText.unObj) sorts') ++ show n
       addVariable (x, sort)
       return x

addSort :: Sort -> Target ()
addSort sort = do
  let sorts' = sortTys sort
  modify $ \s@(TargetState {..}) -> s { sorts = S.union (S.fromList (arrowize sort : sorts')) sorts }

addVariable :: Variable -> Target ()
addVariable (v, sort) = do
  addSort sort
  modify $ \s@(TargetState {..}) -> s { variables = (v, sort) : variables }


sortTys :: Sort -> [Sort]
--sortTys (FFunc _ ts) = concatMap sortTys ts
sortTys t
  | Just (_, ts, t) <- functionSort t
  = concatMap sortTys ts ++ [t]
  | otherwise
  = [t]

arrowize :: Sort -> Sort
arrowize = FObj . symbol . ST.intercalate "->" . map (symbolText . unObj) . sortTys

unObj :: Sort -> Symbol
unObj FInt     = "Int"
unObj (FObj s) = s
unObj s        = error $ "unObj: " ++ show s

-- | Given a data constructor @d@, create a new choice variable corresponding to
-- @d@.
freshChoice :: String -> Target Symbol
freshChoice cn
  = do n <- freshInt
       let x = intSymbol (unObj choicesort) (cn ++ "-" ++ show n)
       --  ... symbol $ T.unpack (Builder.toLazyText $ smt2 choicesort)
       --                  ++ "-" ++ cn ++ "-" ++ show n
       modify $ \s@(TargetState {..}) -> s { variables = (x, choicesort) : variables }
       return x

-- | Ask the SMT solver for the 'Value' of the given variable.
getValue :: Symbol -> Target Value
getValue v = do
  ctx <- gets smtContext
  Values [x] <- io $ ensureValues $ command ctx (GetValue [v])
  noteUsed x
  return (snd x)
