-- | Collection of names and strings used in the translation
module Language.Haskell.Liquid.RefCore.Names where

import Data.Hashable (hash)
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass

-- | Identifiers in both LH and Rocq
type Id = String

-- | return a variable fresh wrt to a set of Id
freshVar :: Id -> Set Id -> Id
freshVar x vars = go x 1
  where
    go n i
      | n `Set.notMember` vars = n
      | otherwise = go (x ++ "_" ++ show (i :: Integer)) (i + 1)

-- | Produce an (almost certainly) unique number string for the given printable object
hashName :: (Pretty a) => a -> Id
hashName e = take 8 $ prettyShow (abs . hash $ prettyShow e)

-- Builtin names

boolTpName :: Id
boolTpName = "Bool"

ttTmName :: Id
ttTmName = "True"

ffTmName :: Id
ffTmName = "False"

unitTpName :: Id
unitTpName = "Unit"

unitTmName :: Id
unitTmName = "unit"

-- | The canonical refinement value variable (the @VV@ in @{VV : tp | …}@).
vvName :: Id
vvName = "VV"
