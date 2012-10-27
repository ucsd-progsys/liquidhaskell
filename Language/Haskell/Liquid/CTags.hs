
-- | This module contains the code for generating "tags" for constraints
-- based on their source, i.e. the top-level binders under which the
-- constraint was generated. These tags are used by fixpoint in
-- Language.Haskell.Liquid.FixInterface to prioritize constraints by the
-- source function.

module Language.Haskell.Liquid.CTags (
    -- * Type for constraint tags
    TagKey, TagEnv
 
    -- * Default tag value
  , defaultTag
   
    -- * Constructing @TagEnv@
  , makeTagEnv
  
    -- * Accessing @TagEnv@
  , getTag, memTagEnv

) where

import Var
import CoreSyn
import qualified Data.List as L
import qualified Data.Map  as M
import Language.Haskell.Liquid.Fixpoint (Tag)

-- | The @TagKey@ is the top-level binder, and @Tag@ is a singleton Int list

type TagKey = Var
type TagEnv = M.Map TagKey Tag

-- TODO: use the "callgraph" SCC to do this numbering.

defaultTag :: Tag
defaultTag = [0]

memTagEnv :: TagKey -> TagEnv -> Bool
memTagEnv = M.member

makeTagEnv :: [CoreBind] -> TagEnv 
makeTagEnv = M.fromList . (`zip` (map (:[]) [1..])). L.sort . concatMap topLevelBinders

topLevelBinders (NonRec x _) = [x]
topLevelBinders (Rec xes)    = fmap fst xes 

getTag :: TagKey -> TagEnv -> Tag
getTag = M.findWithDefault defaultTag

