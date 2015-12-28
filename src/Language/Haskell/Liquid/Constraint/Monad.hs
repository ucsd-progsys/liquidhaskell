-- | This module contains various functions that add/update in the CG monad.

{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleContexts          #-}

module Language.Haskell.Liquid.Constraint.Monad  where


import           Text.PrettyPrint.HughesPJ hiding (first)
import qualified TyCon  as TC
import           Var
import           Name (getSrcSpan)
import           SrcLoc -- (SrcSpan)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.Text           as T
import qualified Data.List           as L

import           Data.Maybe          (fromMaybe) -- catMaybes, fromJust, isJust)
import           Control.Monad
import           Control.Monad.State (get, modify)
import qualified Language.Fixpoint.Types            as F
import           Language.Haskell.Liquid.Types hiding (loc)
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Types.Strata
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Fresh
import           Language.Haskell.Liquid.Types.PredType         hiding (freeTyVars)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.Misc -- (concatMapM)
import           Language.Haskell.Liquid.GHC.Misc -- (concatMapM)

-- RJ: What is this `isBind` business?
pushConsBind act
  = do modify $ \s -> s { isBind = False : isBind s }
       z <- act
       modify $ \s -> s { isBind = tail (isBind s) }
       return z

-- | `addC` adds a subtyping constraint into the global pool.

addC :: SubC -> String -> CG ()
addC !c@(SubC γ t1 t2) _msg
  = do -- trace ("addC at " ++ show (loc γ) ++ _msg++ showpp t1 ++ "\n <: \n" ++ showpp t2 ) $
       modify $ \s -> s { hsCs  = c : (hsCs s) }
       bflag <- headDefault True . isBind <$> get
       sflag <- scheck                 <$> get
       if bflag && sflag
         then modify $ \s -> s {sCs = (SubC γ t2 t1) : (sCs s) }
         else return ()
  where
    headDefault a []    = a
    headDefault _ (x:_) = x

addC !c _msg
  = modify $ \s -> s { hsCs  = c : hsCs s }


--------------------------------------------------------------------------------
-- | addPost: RJ: what does this function do?
--------------------------------------------------------------------------------
addPost :: CGEnv -> SpecType -> CG SpecType
--------------------------------------------------------------------------------
addPost γ t = addPost' γ t >> return t

addPost' :: CGEnv -> SpecType -> CG ()
addPost' γ (RRTy e r OInv t)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("addPost", x,t)) γ e
       addC (SubR γ' OInv r) "precondition" -- >> return t

addPost' γ (RRTy e r OTerm t)
  = do γ' <- foldM (\γ (x, t) -> γ ++= ("addPost", x,t)) γ e
       addC (SubR γ' OTerm r) "precondition" -- >> return t

-- addPost' _ (RRTy _ _ OCons t)
--  = return t

addPost' _ t
  = return () -- t

--------------------------------------------------------------------------------
-- | Add Well formedness Constraint
--------------------------------------------------------------------------------
addW   :: WfC -> CG ()
--------------------------------------------------------------------------------
addW !w = modify $ \s -> s { hsWfs = w : (hsWfs s) }

--------------------------------------------------------------------------------
-- | Add a warning
--------------------------------------------------------------------------------
addWarning   :: TError SpecType -> CG ()
--------------------------------------------------------------------------------
addWarning w = modify $ \s -> s { logErrors = w : logErrors s }

-- | Add Identifier Annotations, used for annotation binders (i.e. at binder sites)
addIdA            :: Var -> Annot SpecType -> CG ()
addIdA !x !t      = modify $ \s -> s { annotMap = upd $ annotMap s }
  where
    loc           = getSrcSpan x
    upd m@(AI _)  = if boundRecVar loc m then m else addA loc (Just x) t m

boundRecVar l (AI m) = not $ null [t | (_, AnnRDf t) <- M.lookupDefault [] l m]


-- | Used for annotating reads (i.e. at Var x sites)

addLocA :: Maybe Var -> SrcSpan -> Annot SpecType -> CG ()
addLocA !xo !l !t
  = modify $ \s -> s { annotMap = addA l xo t $ annotMap s }


--------------------------------------------------------------------------------
-- | Used to update annotations for a location, due to (ghost) predicate applications
--------------------------------------------------------------------------------
updateLocA (_:_)  (Just l) t = addLocA Nothing l (AnnUse t)
updateLocA _      _        _ = return ()
--------------------------------------------------------------------------------

addA !l xo@(Just _) !t (AI m)
  | isGoodSrcSpan l
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA !l xo@Nothing  !t (AI m)
  | l `M.member` m                  -- only spans known to be variables
  = AI $ inserts l (T.pack . showPpr <$> xo, t) m
addA _ _ _ !a
  = a
