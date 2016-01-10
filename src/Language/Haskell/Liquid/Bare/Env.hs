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

import Prelude hiding (error)
import HscTypes
import TyCon
import Var

import Control.Monad.Error hiding (Error)
import Control.Monad.State
import Control.Monad.Writer

import qualified Control.Exception   as Ex
import qualified Data.HashMap.Strict as M


import Language.Fixpoint.Types (Expr(..), Symbol, symbol)

import Language.Haskell.Liquid.UX.Errors ()
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.Bounds


-----------------------------------------------------------------------------------
-- | Error-Reader-IO For Bare Transformation --------------------------------------
-----------------------------------------------------------------------------------

-- FIXME: don't use WriterT [], very slow
type BareM = WriterT [Warn] (ErrorT Error (StateT BareEnv IO))

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



insertLogicEnv x ys e
  = modify $ \be -> be {logicEnv = (logicEnv be) {logic_map = M.insert x (LMap x ys e) $ logic_map $ logicEnv be}}

insertAxiom x s
  = modify $ \be -> be {logicEnv = (logicEnv be){axiom_map = M.insert x s $ axiom_map $ logicEnv be}}

setModule m b = b { modName = m }

inModule m act = do
  old <- gets modName
  modify $ setModule m
  res <- act
  modify $ setModule old
  return res

withVArgs l l' vs act = do
  old <- gets rtEnv
  mapM_ (mkExprAlias l l' . symbol . showpp) vs
  res <- act
  modify $ \be -> be { rtEnv = old }
  return res

mkExprAlias l l' v
  = setRTAlias v (RTA v [] [] (RExprArg (Loc l l' $ EVar $ symbol v)) l l')

setRTAlias s a =
  modify $ \b -> b { rtEnv = mapRT (M.insert s a) $ rtEnv b }


setREAlias s a =
  modify $ \b -> b { rtEnv = mapRE (M.insert s a) $ rtEnv b }

------------------------------------------------------------------
execBare :: BareM a -> BareEnv -> IO (Either Error a)
------------------------------------------------------------------
execBare act benv =
   do z <- evalStateT (runErrorT (runWriterT act)) benv `Ex.catch` (return . Left)
      case z of
        Left s        -> return $ Left s
        Right (x, ws) -> do forM_ ws $ putStrLn . ("WARNING: " ++)
                            return $ Right x
