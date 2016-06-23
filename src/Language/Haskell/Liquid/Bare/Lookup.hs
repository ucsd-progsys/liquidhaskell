{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Liquid.Bare.Lookup (
    GhcLookup(..)

  , lookupGhcThing
  , lookupGhcVar
  , lookupGhcTyCon
  , lookupGhcDataCon
  ) where

import           BasicTypes
import           ConLike
import           DataCon
import           GHC                              (HscEnv)
import           HscMain
import           Name
import           PrelInfo                         (wiredInThings)
import           PrelNames                        (fromIntegerName, smallIntegerName, integerTyConName)
import           Prelude                          hiding (error)
import           RdrName                          (setRdrNameSpace)
import           SrcLoc                           (SrcSpan, GenLocated(L))
import           TcEnv
import           TyCon
import           TysWiredIn
import           Var

import           Control.Monad.Except             (MonadError, catchError, throwError)
import           Control.Monad.State
import           Data.Maybe
import           Text.PrettyPrint.HughesPJ        (text)

import qualified Data.List                        as L
import qualified Data.HashMap.Strict              as M

import           Language.Fixpoint.Types.Names    (hpropConName, isPrefixOfSym, lengthSym, propConName, symbolString)
import           Language.Fixpoint.Types          (Symbol, Symbolic(..))

import           Language.Haskell.Liquid.GHC.Misc (lookupRdrName, sourcePosSrcSpan, tcRnLookupRdrName)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.WiredIn

import           Language.Haskell.Liquid.Bare.Env

-----------------------------------------------------------------
------ Querying GHC for Id, Type, Class, Con etc. ---------------
-----------------------------------------------------------------

class Symbolic a => GhcLookup a where
  lookupName :: HscEnv -> ModName -> a -> IO [Name]
  srcSpan    :: a -> SrcSpan

instance GhcLookup (Located Symbol) where
  lookupName e m = symbolLookup e m . val
  srcSpan        = sourcePosSrcSpan . loc

instance GhcLookup Name where
  lookupName _ _ = return . (:[])
  srcSpan        = nameSrcSpan



-- lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM b
lookupGhcThing
  :: (MonadIO m,MonadError (TError t) m,MonadState BareEnv m,GhcLookup a)
  => [Char] -> (TyThing -> Maybe b) -> a -> m b
lookupGhcThing name f x
  = do zs <- lookupGhcThing' name f x
       case zs of
         Just x' -> return x'
         Nothing -> throwError $ ErrGhc (srcSpan x) (text msg)
  where
    msg = "Not in scope: " ++ name ++ " `" ++ symbolString (symbol x) ++ "'"

-- lookupGhcThing' :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> a -> BareM (Maybe b)
lookupGhcThing'
  :: (MonadIO m,MonadState BareEnv m,GhcLookup a)
  => t -> (TyThing -> Maybe a1) -> a -> m (Maybe a1)
lookupGhcThing' _    f x
  = do BE {modName = mod, hscEnv = env} <- get
       ns                 <- liftIO $ lookupName env mod x
       mts                <- liftIO $ mapM (fmap (join . fmap f) . hscTcRcLookupName env) ns
       case catMaybes mts of
         []    -> return Nothing
         (t:_) -> return $ Just t

symbolLookup :: HscEnv -> ModName -> Symbol -> IO [Name]
symbolLookup env mod k
  | k `M.member` wiredIn
  = return $ maybeToList $ M.lookup k wiredIn
  | otherwise
  = symbolLookupEnv env mod k


wiredIn      :: M.HashMap Symbol Name
wiredIn      = M.fromList $ special ++ wiredIns
  where
    wiredIns = [ (symbol n, n) | thing <- wiredInThings, let n = getName thing ]
    special  = [ ("GHC.Integer.smallInteger", smallIntegerName)
               , ("GHC.Integer.Type.Integer", integerTyConName)
               , ("GHC.Num.fromInteger"     , fromIntegerName ) ]

symbolLookupEnv :: HscEnv -> ModName -> Symbol -> IO [Name]
symbolLookupEnv env mod s
  | isSrcImport mod
  = do let modName = getModName mod
       L _ rn <- hscParseIdentifier env $ symbolString s
       res    <- lookupRdrName env modName rn
       -- 'hscParseIdentifier' defaults constructors to 'DataCon's, but we also
       -- need to get the 'TyCon's for declarations like @data Foo = Foo Int@.
       res'   <- lookupRdrName env modName (setRdrNameSpace rn tcName)
       return $ catMaybes [res, res']
  | otherwise
  = do rn             <- hscParseIdentifier env $ symbolString s
       (_, lookupres) <- tcRnLookupRdrName env rn
       case lookupres of
         Just ns -> return ns
         _       -> return []


-- | It's possible that we have already resolved the 'Name' we are looking for,
-- but have had to turn it back into a 'String', e.g. to be used in an 'Expr',
-- as in @{v:Ordering | v = EQ}@. In this case, the fully-qualified 'Name'
-- (@GHC.Types.EQ@) will likely not be in scope, so we store our own mapping of
-- fully-qualified 'Name's to 'Var's and prefer pulling 'Var's from it.
lookupGhcVar :: GhcLookup a => a -> BareM Var
lookupGhcVar x
  = do env <- gets varEnv
       case L.lookup (symbol x) env of
         Nothing -> lookupGhcThing "variable" fv x
         Just v  -> return v
  where
    fv (AnId x)                   = Just x
    fv (AConLike (RealDataCon x)) = Just $ dataConWorkId x
    fv _                          = Nothing


lookupGhcTyCon       ::  GhcLookup a => a -> BareM TyCon
lookupGhcTyCon s     = (lookupGhcThing err ftc s)
                       `catchError` (tryPropTyCon s)
                       `catchError` (\_ -> lookupGhcThing err fdc s)
  where
    ftc (ATyCon x)   
      = Just x
    ftc _            
      = Nothing

    fdc (AConLike (RealDataCon x)) | isJust $ promoteDataCon_maybe x 
      = Just $ promoteDataCon x
    fdc _ 
      = Nothing 

    err = "type constructor or class"

tryPropTyCon :: (Symbolic a, MonadError e m) => a -> e -> m TyCon
tryPropTyCon s e
  | sx == propConName  = return propTyCon
  | sx == hpropConName = return hpropTyCon
  | otherwise          = throwError e
  where
    sx                 = symbol s

lookupGhcDataCon :: (MonadIO m, MonadError (TError t) m, MonadState BareEnv m)
                 => Located Symbol -> m DataCon
lookupGhcDataCon dc
 | Just n <- isTupleDC (val dc)
 = return $ tupleCon BoxedTuple n
 | val dc == "[]"
 = return nilDataCon
 | val dc == ":"
 = return consDataCon
 | otherwise
 = lookupGhcDataCon' dc

isTupleDC :: Symbol -> Maybe Int
isTupleDC zs
  | "(," `isPrefixOfSym` zs
  = Just $ lengthSym zs - 1
  | otherwise
  = Nothing

lookupGhcDataCon' :: (MonadIO m, MonadError (TError t) m, MonadState BareEnv m, GhcLookup a)
                  => a -> m DataCon
lookupGhcDataCon'    = lookupGhcThing "data constructor" fdc
  where
    fdc (AConLike (RealDataCon x)) = Just x
    fdc _            = Nothing
