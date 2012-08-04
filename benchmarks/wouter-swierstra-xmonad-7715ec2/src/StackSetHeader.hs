-----------------------------------------------------------------------------
-- |
-- Module      :  XMonad.StackSet
-- Copyright   :  (c) Don Stewart 2007
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  dons@galois.com
-- Stability   :  experimental
-- Portability :  portable, Haskell 98
--

module XMonad.StackSet (
        -- * Introduction
        -- $intro

        -- ** The Zipper
        -- $zipper

        -- ** Xinerama support
        -- $xinerama

        -- ** Master and Focus
        -- $focus

        StackSet(..), Workspace(..), Screen(..), Stack(..), RationalRect(..), ScreenId(..),
        -- *  Construction
        -- $construction
        new, 
        view, greedyView,
        -- * Xinerama operations
        -- $xinerama
        lookupWorkspace,
        screens, workspaces, allWindows, currentTag,
        -- *  Operations on the current stack
        -- $stackOperations
        peek, index, integrate, integrate', differentiate,
        focusUp, focusDown, focusUp', focusDown', focusMaster, focusWindow,
        tagMember, renameTag, ensureTags, member, findTag, mapWorkspace, mapLayout,
        -- * Modifying the stackset
        -- $modifyStackset
        insertUp, delete, delete', filterStack,
        -- * Setting the master window
        -- $settingMW
        swapUp, swapDown, swapMaster, shiftMaster, modify, modify', float, sink,
        -- * Composite operations
        -- $composite
        shift, shiftWin,

        -- for testing
        abort
    ) where

import qualified Prelude (until,last,maybe,splitAt,zipWith3)
import Prelude hiding (until,last,maybe,seq,splitAt,zipWith3)
import Data.Maybe hiding (maybe)
import qualified Data.List as L (deleteBy,find,splitAt,filter,nub)
import Data.List ( (\\) )
import qualified Data.Map as M (Map,insert,delete,empty)

------------------------------------------------------------------------
-- |
-- A cursor into a non-empty list of workspaces.
--
-- We puncture the workspace list, producing a hole in the structure
-- used to track the currently focused workspace. The two other lists
-- that are produced are used to track those workspaces visible as
-- Xinerama screens, and those workspaces not visible anywhere.

data StackSet i l a sd =
    StackSet { current  :: !(Screen i l a sd)    -- ^ currently focused workspace
             , visible  :: [Screen i l a sd]     -- ^ non-focused workspaces, visible in xinerama
             , hidden   :: [Workspace i l a]         -- ^ workspaces not visible anywhere
             , floating :: M.Map a RationalRect      -- ^ floating windows
             } deriving (Show, Read, Eq)

-- | Visible workspaces, and their Xinerama screens.
data Screen i l a sd = Screen { workspace :: !(Workspace i l a)
                                  , screen :: !ScreenId
                                  , screenDetail :: !sd }
    deriving (Show, Read, Eq)

-- |
-- A workspace is just a tag, a layout, and a stack.
--
data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }
    deriving (Show, Read, Eq)

-- | A structure for window geometries
data RationalRect = 
  RationalRect Rational Rational Rational Rational
    deriving (Show, Read, Eq)

-- |
-- A stack is a cursor onto a (possibly empty) window list.
-- The data structure tracks focus by construction, and
-- the master window is by convention the top-most item.
-- Focus operations will not reorder the list that results from
-- flattening the cursor. The structure can be envisaged as:
--
-- >    +-- master:  < '7' >
-- > up |            [ '2' ]
-- >    +---------   [ '3' ]
-- > focus:          < '4' >
-- > dn +----------- [ '8' ]
--
-- A 'Stack' can be viewed as a list with a hole punched in it to make
-- the focused position. Under the zipper\/calculus view of such
-- structures, it is the differentiation of a [a], and integrating it
-- back has a natural implementation used in 'index'.
--
data Stack a = Stack { up     :: [a]       -- clowns to the left
                     , focus  :: !a        -- focused thing in this set
                     , down   :: [a] }     -- jokers to the right
    deriving (Show, Read, Eq)


type ScreenId = Int

-- | this function indicates to catch that an error is expected
abort :: String -> a
abort x = error $ "xmonad: StackSet: " ++ x

type List a = [a]
-----------------------------------------------------------------------

findTag :: Eq a => a -> StackSet i l a s -> Maybe i
findTag = _findTag (==)

member :: Eq a => a -> StackSet i l a s -> Bool
member = _member (==)

view :: (Eq i) => i -> StackSet i l a s-> StackSet i l a s
view = _view (==)

greedyView :: (Eq i) => i -> StackSet i l a s -> StackSet i l a s
greedyView = _greedyView (==)

focusWindow :: (Eq a, Eq i) => a -> StackSet i l a s -> StackSet i l a s
focusWindow = _focusWindow (==) (==)

tagMember :: Eq i => i -> StackSet i l a s -> Bool
tagMember = _tagMember (==)

renameTag :: Eq i => i -> i -> StackSet i l a s -> StackSet i l a s
renameTag = _renameTag (==)

ensureTags :: Eq i => l -> [i] -> StackSet i l a s -> StackSet i l a s
ensureTags = _ensureTags (==)

insertUp :: Eq a => a -> StackSet i l a s -> StackSet i l a s
insertUp = _insertUp (==)

delete :: (Ord a, Eq s) => a -> StackSet i l a s -> StackSet i l a s
delete = _delete (==)

delete' :: (Eq a) => a -> StackSet i l a s -> StackSet i l a s
delete' = _delete' (==)

shiftWin :: (Eq a, Eq i) => i -> a -> StackSet i l a s -> StackSet i l a s
shiftWin = _shiftWin (==) (==)

shift :: (Ord a, Eq i) => i -> StackSet i l a s -> StackSet i l a s
shift = _shift (==) (==)
