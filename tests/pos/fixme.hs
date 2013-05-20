{-# LANGUAGE PatternGuards #-}

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

module XMonad.StackSet  where

import Prelude hiding (filter, reverse, (++), elem) -- LIQUID
import Data.Maybe   (listToMaybe,isJust,fromMaybe)
import qualified Data.List as L (deleteBy,find,splitAt,filter,nub)
import Data.List ( (\\) )
import qualified Data.Map  as M (Map,insert,delete,empty)
import qualified Data.Set -- LIQUID

-------------------------------------------------------------------------------
----------------------------- Refinements on  Lists ---------------------------
-------------------------------------------------------------------------------

-- measures

{-@
  measure head :: [a] -> a
  head([])   = {v | false}
  head(x:xs) = {v | v = x} 
  @-}

{-@
  measure listDup :: [a] -> (Data.Set.Set a)
  listDup([]) = {v | (? Set_emp (v))}
  listDup(x:xs) = {v | v = ((Set_mem x (listElts xs))?(Set_cup (Set_sng x) (listDup xs)):(listDup xs)) }
  @-}

-- predicates 

{-@ predicate EqElts X Y =
       ((listElts X) = (listElts Y)) @-}

{-@ predicate SubElts X Y =
       (Set_sub (listElts X) (listElts Y)) @-}

{-@ predicate UnionElts X Y Z =
       ((listElts X) = (Set_cup (listElts Y) (listElts Z))) @-}

{-@ predicate ListElt N LS =
       (Set_mem N (listElts LS)) @-}

{-@ predicate ListUnique LS =
       (Set_emp (listDup LS)) @-}

{-@ predicate ListUniqueDif LS X =
       ((ListUnique LS) && (not (ListElt X LS))) @-}


{-@ predicate ListDisjoint X Y =
       (Set_emp (Set_cap (listElts X) (listElts Y))) @-}


-- types

{-@ type UList a = {v:[a] | (ListUnique v)} @-}

{-@ type UListDif a N = {v:[a] | ((not (ListElt N v)) && (ListUnique v))} @-}



-------------------------------------------------------------------------------
----------------------------- Refinements on Stacks ---------------------------
-------------------------------------------------------------------------------

{-@
data Stack a = Stack { focus :: a   
                     , up    :: UListDif a focus
                     , down  :: UListDif a focus }
@-}

{-@ type UStack a = {v:(Stack a) | (ListDisjoint (getUp v) (getDown v))}@-}

{-@ measure getUp :: forall a. (Stack a) -> [a] 
    getUp (Stack focus up down) = up
  @-}

{-@ measure getDown :: forall a. (Stack a) -> [a] 
    getDown (Stack focus up down) = down
  @-}

{-@ measure getFocus :: forall a. (Stack a) -> a
    getFocus (Stack focus up down) = focus
  @-}

{-@ predicate StackElt N S =
       (((ListElt N (getUp S)) 
       || (Set_mem N (Set_sng (getFocus S))) 
       || (ListElt N (getDown S))))
  @-}

{-@ predicate StackSetVisibleElt N S = true @-}
{-@ predicate StackSetHiddenElt N S = true @-}

-- $intro
--
-- The 'StackSet' data type encodes a window manager abstraction. The
-- window manager is a set of virtual workspaces. On each workspace is a
-- stack of windows. A given workspace is always current, and a given
-- window on each workspace has focus. The focused window on the current
-- workspace is the one which will take user input. It can be visualised
-- as follows:
--
-- > Workspace  { 0*}   { 1 }   { 2 }   { 3 }   { 4 }
-- >
-- > Windows    [1      []      [3*     [6*]    []
-- >            ,2*]            ,4
-- >                            ,5]
--
-- Note that workspaces are indexed from 0, windows are numbered
-- uniquely. A '*' indicates the window on each workspace that has
-- focus, and which workspace is current.

-- $zipper
--
-- We encode all the focus tracking directly in the data structure, with a 'zipper':
--
--    A Zipper is essentially an `updateable' and yet pure functional
--    cursor into a data structure. Zipper is also a delimited
--    continuation reified as a data structure.
--
--    The Zipper lets us replace an item deep in a complex data
--    structure, e.g., a tree or a term, without an  mutation.  The
--    resulting data structure will share as much of its components with
--    the old structure as possible.
--
--      Oleg Kiselyov, 27 Apr 2005, haskell\@, "Zipper as a delimited continuation"
--
-- We use the zipper to keep track of the focused workspace and the
-- focused window on each workspace, allowing us to have correct focus
-- by construction. We closely follow Huet's original implementation:
--
--      G. Huet, /Functional Pearl: The Zipper/,
--      1997, J. Functional Programming 75(5):549-554.
-- and:
--      R. Hinze and J. Jeuring, /Functional Pearl: The Web/.
--
-- and Conor McBride's zipper differentiation paper.
-- Another good reference is:
--
--      The Zipper, Haskell wikibook

-- $xinerama
-- Xinerama in X11 lets us view multiple virtual workspaces
-- simultaneously. While only one will ever be in focus (i.e. will
-- receive keyboard events), other workspaces may be passively
-- viewable.  We thus need to track which virtual workspaces are
-- associated (viewed) on which physical screens.  To keep track of
-- this, 'StackSet' keeps separate lists of visible but non-focused
-- workspaces, and non-visible workspaces.

-- $focus
--
-- Each stack tracks a focused item, and for tiling purposes also tracks
-- a 'master' position. The connection between 'master' and 'focus'
-- needs to be well defined, particularly in relation to 'insert' and
-- 'delete'.
--

------------------------------------------------------------------------
-- |
-- A cursor into a non-empty list of workspaces.
--
-- We puncture the workspace list, producing a hole in the structure
-- used to track the currently focused workspace. The two other lists
-- that are produced are used to track those workspaces visible as
-- Xinerama screens, and those workspaces not visible anywhere.

data StackSet i l a sid sd =
    StackSet { current  :: !(Screen i l a sid sd)    -- ^ currently focused workspace
             , visible  :: [Screen i l a sid sd]     -- ^ non-focused workspaces, visible in xinerama
             , hidden   :: [Workspace i l a]         -- ^ workspaces not visible anywhere
             , floating :: M.Map a RationalRect      -- ^ floating windows
             } deriving (Show, Eq)
-- LIQUID             } deriving (Show, Read, Eq)

{-@ 
data StackSet i l a sid sd =
    StackSet { current  :: (Screen i l a sid sd)   
             , visible  :: [Screen i l a sid sd]   
             , hidden   :: [Workspace i l a]       
             , floating :: M.Map a RationalRect    
             }
@-}

{-@ measure getCurrentScreen :: (StackSet i l a sid sd) -> (Screen i l a sid sd)
    getCurrentScreen(StackSet current v h f) = current @-}


-- NEW current tag

{-@ measure getTag :: (Workspace i l a) -> i
    getTag(Workspace t l s) = t
  @-}

{-@ tag :: w:(Workspace i l a) -> {v:i|v = (getTag w)} @-}

{-@ predicate IsCurrentTag X Y = (X = (getTag (getWorkspaceScreen (getCurrentScreen Y))) )@-}
-- END current tag
-- get StackSet Elements

{-@ measure stackSetElts :: (StackSet i l a sid sd) -> (Data.Set.Set a)
    stackSetElts(StackSet current visible hidden f) = (Set_cup (Set_cup (screenElts current) (screensElts visible)) (workspacesElts hidden))
   @-}

{-@ measure screensElts :: [(Screen i l a sid sd)] -> (Data.Set.Set a)
    screensElts([])   = {v|(? (Set_emp v))} 
    screensElts(x:xs) = (Set_cup (screenElt x) (screensElts xs))
  @-}

{-@ measure screenElts :: (Screen i l a sid sd) -> (Data.Set.Set a)
    screenElts(Screen w s sd) = (workspaceElts w) @-}

{-@ measure workspacesElts :: [(Workspace i l a)] -> (Data.Set.Set a)
    workspacesElts([])   = {v|(? (Set_emp v))} 
    workspacesElts(x:xs) = (Set_cup (workspaceElts x) (workspacesElts xs))
  @-}

{-@ measure workspaceElts :: (Workspace i l a) -> (Data.Set.Set a)
    workspaceElts(Workspace t l s) = {v| (if (isJust s) then (stackElts (fromJust s)) else (? (Set_emp v)))} @-}

{-@ measure stackElts :: (StackSet i l a sid sd) -> (Data.Set.Set a)
    stackElts(Stack f up down) = (Set_cup (Set_sng f) (Set_cup (listElts up) (listElts down))) @-}

{-@ predicate EmptyStackSet X = (? (Set_emp (stackSetElts X)))@-}

-- END get StackSet Elements

{-@ predicate StackSetCurrentElt N S = 
      (ScreenElt N (getCurrentScreen S))
  @-}

{-@ current :: s:(StackSet i l a sid sd) 
            -> {v:(Screen i l a sid sd) | v = (getCurrentScreen s)}
  @-}

{-@ stack :: w:(Workspace i l a) 
          -> {v:(Maybe (UStack a)) | v = (getStackWorkspace w)}
  @-}

{-@ workspace :: s:(Screen i l a sid sd) 
              -> {v:(Workspace i l a) | v = (getWorkspaceScreen s)}
  @-}


-- | Visible workspaces, and their Xinerama screens.
data Screen i l a sid sd = Screen { workspace :: !(Workspace i l a)
                                  , screen :: !sid
                                  , screenDetail :: !sd }
    deriving (Show, Eq)
-- LIQUID    deriving (Show, Read, Eq)

{-@ 
data Screen i l a sid sd = Screen { workspace :: (Workspace i l a)
                                  , screen :: sid
                                  , screenDetail :: sd }
@-}

{-@ measure getWorkspaceScreen :: (Screen i l a sid sd) -> (Workspace i l a)
    getWorkspaceScreen(Screen w screen s) = w @-}


{-@ predicate ScreenElt N S = 
      (WorkspaceElt N (getWorkspaceScreen S))
  @-}


-- |
-- A workspace is just a tag, a layout, and a stack.
--
data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }
    deriving (Show, Eq)
--     deriving (Show, Read, Eq)

{-@
data Workspace i l a = Workspace  { tag :: i, layout :: l, stack :: Maybe (UStack a) }
  @-}

{-@ measure getStackWorkspace :: (Workspace i l a) -> (Maybe(Stack a))
    getStackWorkspace(Workspace t l stack) = stack @-}

{-@ predicate WorkspaceElt N W =
  ((isJust (getStackWorkspace W)) && (StackElt N (fromJust (getStackWorkspace W)))) @-}

-- | A structure for window geometries
data RationalRect = RationalRect Rational Rational Rational Rational
    deriving (Show, Read, Eq)

-- |
-- A stack is a cursor onto a window list.
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
data Stack a = Stack { focus  :: !a        -- focused thing in this set
                     , up     :: [a]       -- clowns to the left
                     , down   :: [a] }     -- jokers to the right
     deriving (Show, Eq)
-- LIQUID      deriving (Show, Read, Eq)


-- | this function indicates to catch that an error is expected
abort :: String -> a
abort x = error $ "xmonad: StackSet: " ++ x
  where [] ++ ys     = ys              -- LIQUID
        (x:xs) ++ ys = x: (xs ++ ys)   -- LIQUID


-- ---------------------------------------------------------------------
-- $construction

-- | /O(n)/. Create a new stackset, of empty stacks, with given tags,
-- with physical screens whose descriptions are given by 'm'. The
-- number of physical screens (@length 'm'@) should be less than or
-- equal to the number of workspace tags.  The first workspace in the
-- list will be current.
--
-- Xinerama: Virtual workspaces are assigned to physical screens, starting at 0.
--
{-@ new :: (Integral s) 
        => l 
        -> is:[i] 
        -> [sd] 
        -> {v:(StackSet i l a s sd) | ((EmptyStackSet v) && (IsCurrentTag (head is) v))} 
  @-}
new :: (Integral s) => l -> [i] -> [sd] -> StackSet i l a s sd
new l wids m | not (null wids) && length m <= length wids && not (null m)
  = StackSet cur visi unseen M.empty
  where (seen,unseen) = L.splitAt (length m) $ map (\i -> Workspace i l Nothing) wids
        (cur:visi)    = [ Screen i s sd |  (i, s, sd) <- zip3 seen [0..] m ]
                -- now zip up visibles with their screen id
new _ _ _ = abort "non-positive argument to StackSet.new"

