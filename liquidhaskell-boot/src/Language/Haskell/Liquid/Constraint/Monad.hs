-- | This module contains various functions that add/update in the CG monad.

{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleContexts          #-}

module Language.Haskell.Liquid.Constraint.Monad  where

import qualified Data.HashMap.Strict as M
import qualified Data.Text           as T

import           Control.Monad
import           Control.Monad.State (gets, modify)
import           Language.Haskell.Liquid.Types hiding (loc)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Fixpoint.Misc hiding (errorstar)
import           Liquid.GHC.Misc -- (concatMapM)
import           Liquid.GHC.API as Ghc hiding (panic, showPpr)

--------------------------------------------------------------------------------
-- | `addC` adds a subtyping constraint into the global pool.
--------------------------------------------------------------------------------
addC :: SubC -> String -> CG ()
--------------------------------------------------------------------------------
addC c@(SubC γ t1 t2) _msg
  | toType False t1 /= toType False t2
  = panic (Just $ getLocation γ) $ "addC: malformed constraint:\n" ++ _msg ++ showpp t1 ++ "\n <: \n" ++ showpp t2
  | otherwise
  = modify $ \s -> s { hsCs  = c : hsCs s }


addC c _msg
  = modify $ \s -> s { hsCs  = c : hsCs s }

--------------------------------------------------------------------------------
-- | addPost: RJ: what DOES this function do?
--------------------------------------------------------------------------------
addPost :: CGEnv -> SpecType -> CG SpecType
--------------------------------------------------------------------------------
addPost cgenv (RRTy e r OInv rt)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("addPost", x,t)) cgenv e
       addC (SubR γ' OInv r) "precondition-oinv" >> return rt

addPost cgenv (RRTy e r OTerm rt)
  = do γ' <- foldM (\γ (x, t) -> γ += ("addPost", x, t)) cgenv e
       addC (SubR γ' OTerm r) "precondition-oterm" >> return rt

addPost cgenv (RRTy cts _ OCons rt)
  = do γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x,t)) cgenv xts
       addC (SubC  γ' t1 t2)  "precondition-ocons"
       addPost cgenv rt
  where
    (xts, t1, t2) = envToSub cts
addPost _ t
  = return t

--------------------------------------------------------------------------------
-- | Add Well formedness Constraint
--------------------------------------------------------------------------------
addW   :: WfC -> CG ()
--------------------------------------------------------------------------------
addW !w = modify $ \s -> s { hsWfs = w : hsWfs s }

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


lookupNewType :: Ghc.TyCon -> CG (Maybe SpecType)
lookupNewType tc
  = gets (M.lookup tc . newTyEnv)


--------------------------------------------------------------------------------
{-@ envToSub :: {v:[(a, b)] | 2 <= len v} -> ([(a, b)], b, b) @-}
envToSub :: [(a, b)] -> ([(a, b)], b, b)
--------------------------------------------------------------------------------
envToSub = go []
  where
    go _   []              = impossible Nothing "This cannot happen: envToSub on 0 elems"
    go _   [(_,_)]         = impossible Nothing "This cannot happen: envToSub on 1 elem"
    go ack [(_,l), (_, r)] = (reverse ack, l, r)
    go ack (x:xs)          = go (x:ack) xs
