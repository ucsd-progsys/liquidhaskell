-- | This module contains various functions that add/update in the CG monad.

{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE FlexibleContexts          #-}

module Language.Haskell.Liquid.Constraint.Monad  where

import           Var
import           Name (getSrcSpan)
import           SrcLoc
import           Outputable hiding (showPpr, panic, (<>), showSDoc, text)

import qualified TyCon as TC
import           Text.PrettyPrint.HughesPJ (text)

import qualified Data.HashMap.Strict as M
import qualified Data.Text           as T

import           Control.Monad
import           Control.Monad.State (get, modify)
import           Language.Haskell.Liquid.Types hiding (loc)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Fixpoint.Misc hiding (errorstar)
import           Language.Haskell.Liquid.GHC.Misc -- (concatMapM)
import           Language.Haskell.Liquid.GHC.SpanStack (srcSpan)
import qualified Language.Haskell.Liquid.GHC.API            as Ghc

--------------------------------------------------------------------------------
-- | `addC` adds a subtyping constraint into the global pool.
--------------------------------------------------------------------------------
addC :: SubC -> String -> CG ()
--------------------------------------------------------------------------------
addC c@(SubC γ t1 t2) _msg
  | toType t1 /= toType t2
  = panic (Just $ getLocation γ) $ "addC: malformed constraint:\n" ++ _msg ++ showpp t1 ++ "\n <: \n" ++ showpp t2 
  | otherwise
  = modify $ \s -> s { hsCs  = c : (hsCs s) }
 

addC c _msg
  = modify $ \s -> s { hsCs  = c : hsCs s }

--------------------------------------------------------------------------------
-- | addPost: RJ: what DOES this function do?
--------------------------------------------------------------------------------
addPost :: CGEnv -> SpecType -> CG SpecType
--------------------------------------------------------------------------------
addPost γ (RRTy e r OInv t)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("addPost", x,t)) γ e
       addC (SubR γ' OInv r) "precondition" >> return t

addPost γ (RRTy e r OTerm t)
  = do γ' <- foldM (\γ (x, t) -> γ += ("addPost", x, t)) γ e
       addC (SubR γ' OTerm r) "precondition" >> return t

addPost _ (RRTy _ _ OCons t)
  = return t

addPost _ t
  = return t

--------------------------------------------------------------------------------
-- | Add Well formedness Constraint
--------------------------------------------------------------------------------
addW   :: WfC -> CG ()
--------------------------------------------------------------------------------
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

--------------------------------------------------------------------------------
-- | Add a warning
--------------------------------------------------------------------------------
addWarning   :: Error -> CG ()
--------------------------------------------------------------------------------
addWarning w = modify $ \s -> s { logErrors = w : logErrors s }

-- | Add Identifier Annotations, used for annotation binders (i.e. at binder sites)
addIdA            :: Var -> Annot SpecType -> CG ()
addIdA !x !t      = modify $ \s -> s { annotMap = upd $ annotMap s }
  where
    l             = getSrcSpan x
    upd m@(AI _)  = if boundRecVar l m then m else addA l (Just x) t m

boundRecVar :: SrcSpan -> AnnInfo (Annot a) -> Bool
boundRecVar l (AI m) = not $ null [t | (_, AnnRDf t) <- M.lookupDefault [] l m]


-- | Used for annotating reads (i.e. at Var x sites)

addLocA :: Maybe Var -> SrcSpan -> Annot SpecType -> CG ()
addLocA !xo !l !t
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }


-- | Used for annotating holes 

addHole :: Var -> SpecType -> CGEnv -> CG () 
addHole x t γ = do 
  modify $ \s -> s {holesMap = M.insertWith (<>) x hinfo $ holesMap s}
  addWarning $ ErrHole loc ("hole found") (reGlobal env <> reLocal env) x' t 
    where 
      hinfo = [HoleInfo t loc env]
      loc   = srcSpan $ cgLoc γ
      env   = mconcat [renv γ, grtys γ, assms γ, intys γ]
      x'    = text $ showSDoc $ Ghc.pprNameUnqualified $ Ghc.getName x


--------------------------------------------------------------------------------
-- | Update annotations for a location, due to (ghost) predicate applications
--------------------------------------------------------------------------------
updateLocA :: Maybe SrcSpan -> SpecType -> CG ()
--------------------------------------------------------------------------------
updateLocA (Just l) t = addLocA Nothing l (AnnUse t)
updateLocA _        _ = return ()
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
addA :: (Outputable a) => SrcSpan -> Maybe a -> b -> AnnInfo b -> AnnInfo b
--------------------------------------------------------------------------------
addA !l xo@(Just _) !t (AI m)
  | isGoodSrcSpan l
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA !l xo@Nothing  !t (AI m)
  | l `M.member` m                  -- only spans known to be variables
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA _ _ _ !a
  = a


lookupNewType :: TC.TyCon -> CG (Maybe SpecType)
lookupNewType tc
  = M.lookup tc . newTyEnv <$> get
