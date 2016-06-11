{-# LANGUAGE FlexibleContexts         #-}

module Language.Haskell.Liquid.Bare.Env (
    BareM
  , Warn
  , TCEnv

  , BareEnv(..)

  , TInline(..), InlnEnv

  , inModule
  , withVArgs

  , setRTAlias
  , setREAlias

  , execBare

  , insertLogicEnv
  , insertAxiom
  ) where

import           HscTypes
import           Prelude                              hiding (error)
import           Text.Parsec.Pos
import           TyCon
import           Var

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import qualified Control.Exception                    as Ex
import qualified Data.HashMap.Strict                  as M


import           Language.Fixpoint.Types              (Expr(..), Symbol, symbol)
-- import           Language.Fixpoint.Misc (traceShow)

import           Language.Haskell.Liquid.UX.Errors    ()
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Bounds


-----------------------------------------------------------------------------------
-- | Error-Reader-IO For Bare Transformation --------------------------------------
-----------------------------------------------------------------------------------

-- FIXME: don't use WriterT [], very slow
type BareM = WriterT [Warn] (ExceptT Error (StateT BareEnv IO))

type Warn  = String

type TCEnv = M.HashMap TyCon RTyCon

type InlnEnv = M.HashMap Symbol TInline

data TInline = TI { tiargs :: [Symbol]
                  , tibody :: Expr
                  } deriving (Show)



data BareEnv = BE { modName  :: !ModName
                  , tcEnv    :: !TCEnv
                  , rtEnv    :: !RTEnv
                  , varEnv   :: ![(Symbol,Var)]
                  , hscEnv   :: HscEnv
                  , logicEnv :: LogicMap
                  , inlines  :: InlnEnv
                  , bounds   :: RBEnv
                  }


insertLogicEnv
  :: MonadState BareEnv m => Symbol -> [Symbol] -> Expr -> m ()
insertLogicEnv x ys e
  = modify $ \be -> be {logicEnv = (logicEnv be) {logic_map = M.insert x (LMap x ys e) $ logic_map $ logicEnv be}}

insertAxiom :: MonadState BareEnv m => Var -> Symbol -> m ()
insertAxiom x s
  = modify $ \be -> be {logicEnv = (logicEnv be){axiom_map = M.insert x s $ axiom_map $ logicEnv be}}

setModule :: ModName -> BareEnv -> BareEnv
setModule m b = b { modName = m }

inModule :: MonadState BareEnv m => ModName -> m b -> m b
inModule m act = do
  old <- gets modName
  modify $ setModule m
  res <- act
  modify $ setModule old
  return res

withVArgs :: (Foldable t,PPrint a,MonadState BareEnv m)
          => SourcePos
          -> SourcePos
          -> t a
          -> m b
          -> m b
withVArgs l l' vs act = do
  old <- gets rtEnv
  mapM_ (mkExprAlias l l' . symbol . showpp) vs
  res <- act
  modify $ \be -> be { rtEnv = old }
  return res

mkExprAlias
  :: MonadState BareEnv m
  => SourcePos -> SourcePos -> Symbol -> m ()
mkExprAlias l l' v
  = setRTAlias v (RTA v [] [] (RExprArg (Loc l l' $ EVar $ symbol v)) l l')

setRTAlias
  :: MonadState BareEnv m
  => Symbol -> RTAlias RTyVar SpecType -> m ()
setRTAlias s a =
  modify $ \b -> b { rtEnv = mapRT (M.insert s a) $ rtEnv b }


setREAlias
  :: MonadState BareEnv m
  => Symbol -> RTAlias Symbol Expr -> m ()
setREAlias s a =
  modify $ \b -> b { rtEnv = mapRE (M.insert s a) $ rtEnv b }

------------------------------------------------------------------
execBare :: BareM a -> BareEnv -> IO (Either Error a)
------------------------------------------------------------------
execBare act benv =
   do z <- evalStateT (runExceptT (runWriterT act)) benv `Ex.catch` (return . Left)
      case z of
        Left s        -> return $ Left s
        Right (x, ws) -> do forM_ ws $ putStrLn . ("WARNING: " ++)
                            return $ Right x
