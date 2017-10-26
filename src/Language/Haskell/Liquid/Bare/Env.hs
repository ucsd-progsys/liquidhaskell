{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Haskell.Liquid.Bare.Env (
    BareM
  , Warn
  , TCEnv
  , BareEnv(..)
  , InlnEnv

  , inModule
  , withVArgs

  , setRTAlias
  , setREAlias
  -- , setEmbeds
  , setDataDecls

  , execBare

  , insertLogicEnv
  , insertAxiom
  , addDefs


  -- * Exact DataConstructor Functions
  , DataConMap
  , dataConMap
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
import qualified Data.HashSet                         as S


import           Language.Fixpoint.Types              (Expr(..), TCEmb)
import qualified Language.Fixpoint.Types as F

import           Language.Haskell.Liquid.UX.Errors    ()
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types.Bounds

--------------------------------------------------------------------------------
-- | 'DataConMap' stores the names of those ctor-fields that have been declared
--   as SMT ADTs so we don't make up new names for them.
--------------------------------------------------------------------------------
type DataConMap = M.HashMap (F.Symbol, Int) F.Symbol

dataConMap :: [F.DataDecl] -> DataConMap
dataConMap ds = M.fromList $ do
  d     <- ds
  c     <- F.ddCtors d
  let fs = F.symbol <$> F.dcFields c
  zip ((F.symbol c,) <$> [1..]) fs

--------------------------------------------------------------------------------
-- | Error-Reader-IO For Bare Transformation -----------------------------------
--------------------------------------------------------------------------------

-- FIXME: don't use WriterT [], very slow
type BareM   = WriterT [Warn] (ExceptT Error (StateT BareEnv IO))
type Warn    = String
type TCEnv   = M.HashMap TyCon RTyCon
type InlnEnv = M.HashMap F.Symbol LMap

data BareEnv = BE
  { modName  :: !ModName
  , tcEnv    :: !TCEnv
  , rtEnv    :: !RTEnv
  , varEnv   :: !(M.HashMap F.Symbol Var)
  , hscEnv   :: !(HscEnv)
  , logicEnv :: !LogicMap
  , dcEnv    :: !DataConMap
  , bounds   :: !(RBEnv)
  , embeds   :: !(TCEmb TyCon)
  , axSyms   :: !(M.HashMap F.Symbol LocSymbol)
  , propSyms :: !(M.HashMap F.Symbol LocSymbol)
  , beConfig :: !Config
  , beIndex  :: !Integer
  }

instance Freshable BareM Integer where
  fresh = do s <- get
             let n = beIndex s
             put $ s { beIndex = n + 1 }
             return n

instance HasConfig BareEnv where
  getConfig = beConfig

setDataDecls :: [F.DataDecl] -> BareM ()
setDataDecls adts = modify $ \be -> be { dcEnv = dataConMap adts }

_setEmbeds :: TCEmb TyCon -> BareM ()
_setEmbeds emb = modify $ \be -> be {embeds = emb}

insertLogicEnv :: String -> LocSymbol -> [F.Symbol] -> Expr -> BareM ()
insertLogicEnv _msg x ys e = modify $ \be -> be {logicEnv = (logicEnv be) {lmSymDefs = M.insert (val x) (LMap x ys e) $ lmSymDefs $ logicEnv be}}

insertAxiom :: Var -> Maybe F.Symbol -> BareM ()
insertAxiom x s
  = modify $ \be -> be {logicEnv = (logicEnv be) {lmVarSyms = M.insert x s $ lmVarSyms $ logicEnv be}}

addDefs :: S.HashSet (Var, F.Symbol) -> BareM ()
addDefs ds = forM_ (S.toList ds) $ \(v, x) -> insertAxiom v (Just x)

setModule :: ModName -> BareEnv -> BareEnv
setModule m b = b { modName = m }

inModule :: ModName -> BareM b -> BareM b
inModule m act = do
  old <- gets modName
  modify $ setModule m
  res <- act
  modify $ setModule old
  return res

withVArgs :: (Foldable t, PPrint a)
          => SourcePos
          -> SourcePos
          -> t a
          -> BareM b
          -> BareM b
withVArgs l l' vs act = do
  old <- gets rtEnv
  mapM_ (mkExprAlias l l' . F.symbol . showpp) vs
  res <- act
  modify $ \be -> be { rtEnv = old }
  return res

mkExprAlias :: SourcePos -> SourcePos -> F.Symbol -> BareM ()
mkExprAlias l l' v = setRTAlias v (RTA v [] [] (RExprArg (Loc l l' $ EVar $ F.symbol v)) l l')

setRTAlias :: F.Symbol -> RTAlias RTyVar SpecType -> BareM ()
setRTAlias s a = modify $ \b -> b { rtEnv = mapRT (M.insert s a) $ rtEnv b }

setREAlias :: F.Symbol -> RTAlias F.Symbol Expr -> BareM ()
setREAlias s a = modify $ \b -> b { rtEnv = mapRE (M.insert s a) $ rtEnv b }

------------------------------------------------------------------
execBare :: BareM a -> BareEnv -> IO (Either Error a)
------------------------------------------------------------------
execBare act benv =
   do z <- evalStateT (runExceptT (runWriterT act)) benv `Ex.catch` (return . Left)
      case z of
        Left s        -> return $ Left s
        Right (x, ws) -> do forM_ ws $ putStrLn . ("WARNING: " ++)
                            return $ Right x
