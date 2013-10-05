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

module XMonad.StackSet where

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


-------------------------------------------------------------------------------
-----------------------  Grap StackSet Elements -------------------------------
-------------------------------------------------------------------------------

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


-------------------------------------------------------------------------------
-----------------------  Talking about Tags --- -------------------------------
-------------------------------------------------------------------------------

{-@ measure getTag :: (Workspace i l a) -> i
    getTag(Workspace t l s) = t
  @-}

{-@ predicate IsCurrentTag X Y = 
      (X = (getTag (getWorkspaceScreen (getCurrentScreen Y))))
  @-}

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

{- invariant {v:(StackSet i l a sid sd) | 
     (((?(
       Set_emp (Set_cap (screenElts (getCurrentScreen v)) 
                        (screensElts (getVisible v))
      ))) && (?(
       Set_emp (Set_cap (screenElts (getCurrentScreen v)) 
                        (workspacesElts (getHidden v))
      )))) && (?(
       Set_emp (Set_cap (workspacesElts (getHidden v)) 
                        (screensElts (getVisible v))
      ))))} @-}

{-@ measure getCurrentScreen :: (StackSet i l a sid sd) -> (Screen i l a sid sd)
    getCurrentScreen(StackSet current v h f) = current @-}

{-@ measure getVisible :: (StackSet i l a sid sd) -> [(Screen i l a sid sd)]
    getVisible(StackSet current v h f) = v @-}

{-@ measure getHidden :: (StackSet i l a sid sd) -> [(Workspace i l a)]
    getHidden(StackSet current v h f) = h @-}

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

{-@ tag :: w:(Workspace i l a) -> {v:i|v = (getTag w)} @-}

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
{-@ predicate IsTagInStackSet T ST = 
    ((( (T = (getTag (getWorkspaceScreen (getCurrentScreen ST))))
     )) || ((
      (Set_mem T (getTagScreens (getVisible ST)))
    ) || (false)))
  @-}

--       (Set_mem T (getTagScreens (getVisible ST)))
{-@ view :: (Eq s, Eq i) 
         => t:i 
         -> st: {v:(StackSet i l a s sd) | true}
         -> {v:StackSet i l a s sd|((IsTagInStackSet t st) => (IsCurrentTag t v))} @-}
view :: (Eq s, Eq i) => i -> StackSet i l a s sd -> StackSet i l a s sd
view i s
    | i == currentTag s = s  -- current

    | Just x <- findTagInScreen i (visible s)
    -- if it is visible, it is just raised
    = s { current = x, visible = current s : L.deleteBy (equating screen) x (visible s) }

--     | Just x <- findTagInWorkspace i (hidden  s) -- must be hidden then
    -- if it was hidden, it is raised on the xine screen currently used
--     = s { current = (current s) { workspace = x }
--         , hidden = workspace (current s) : L.deleteBy (equating tag) x (hidden s) }

--     | otherwise = s -- not a member of the stackset

  where equating f = \x y -> f x == f y

{-@ findTagInScreen :: (Eq i) 
         => t:i 
         -> s:([Screen i l a sid sd])
         -> {v:(Maybe (Screen i l a sid sd)) | ( ((isJust v) =>  (t = (getTag (getWorkspaceScreen (fromJust v))))))}
  @-}
findTagInScreen :: (Eq i) => i -> [Screen i l a sid sd] -> Maybe (Screen i l a sid sd)
findTagInScreen i []     = Nothing
findTagInScreen i (x:xs) 
  | i == (tag (workspace x)) = Just x
  | otherwise                = findTagInScreen i xs

{-@ findTagInWorkspace :: (Eq i) 
         => t:i 
         -> [Workspace i l a] 
         -> {v:(Maybe (Workspace i l a)) | ((isJust v) => (t = (getTag (fromJust v))))}
  @-}
findTagInWorkspace :: (Eq i) => i -> [Workspace i l a] -> Maybe (Workspace i l a)
findTagInWorkspace i []     = Nothing
findTagInWorkspace i (x:xs) 
  | i == (tag x) = Just x
  | otherwise    = findTagInWorkspace i xs

{-@ qview :: x:(Workspace i l a) -> {v:(Screen i l a sid sd)|(getWorkspaceScreen v) = x} @-}
qview :: Workspace i l a -> Screen i l a sid sd 
qview = undefined

{-@ qview1 :: x:(Screen i l a sid sd) -> {v:(StackSet i l a sid sd)|(getCurrentScreen v) = x} @-}
qview1 :: Screen i l a sid sd -> StackSet i l a sid sd 
qview1 = undefined

{-@ qview2 :: x:([Workspace i l a]) -> {v:(StackSet i l a sid sd)|(getHidden v) = x} @-}
qview2 :: [Workspace i l a] -> StackSet i l a sid sd 
qview2 = undefined

{-@ qview3 :: x:([Screen i l a sid sd]) -> {v:(StackSet i l a sid sd)|(getVisible v) = x} @-}
qview3 :: [Screen i l a sid sd] -> StackSet i l a sid sd 
qview3 = undefined

{-@ 
qview4 :: x : (Screen i l a sid sd)
       -> y : ([Screen i l a sid sd])
       -> z : Workspace i l a
       -> {v:(StackSet i l a sid sd)|(stackSetElts v) = 
         (Set_cup (Set_cup (screenElts x) (screensElts y)) 
                   (workspaceElts z))}
@-}
qview4 :: (Screen i l a sid sd)
       -> [Screen i l a sid sd]
       -> Workspace i l a
       -> StackSet i l a sid sd
qview4 = undefined

    -- 'Catch'ing this might be hard. Relies on monotonically increasing
    -- workspace tags defined in 'new'
    --
    -- and now tags are not monotonic, what happens here?

-- |
-- Set focus to the given workspace.  If that workspace does not exist
-- in the stackset, the original workspace is returned.  If that workspace is
-- 'hidden', then display that workspace on the current screen, and move the
-- current workspace to 'hidden'.  If that workspace is 'visible' on another
-- screen, the workspaces of the current screen and the other screen are
-- swapped.

{-@ measure getTagWorkspace :: (Workspace i l a) -> (Data.Set.Set i)
    getTagWorkspace(Workspace t l s) = (Set_sng t)
  @-}

{-@ measure getTagScreen :: (Screen i l a sid sd) -> (Data.Set.Set i)
    getTagScreen(Screen w s sd) = (getTagWorkspace w)
  @-}

{-@ measure getTagScreens :: ([(Screen i l a sid sd)]) -> (Data.Set.Set i)
    getTagScreens([])   = {v | (?(Set_emp v))}
    getTagScreens(x:xs) = (Set_cap (getTagScreen x) (getTagScreens xs))
  @-}


{-@ currentTag :: s: StackSet i l a s sd -> {v:i|(IsCurrentTag v s)} @-}
currentTag :: StackSet i l a s sd -> i
currentTag = tag . workspace . current

-- LIQUID : qualifier missing for currentTag
{-@ qcurrentTag :: s:(StackSet i l a s sd) 
                -> {v:(Workspace i l a) | v = (getWorkspaceScreen (getCurrentScreen s))} @-}
qcurrentTag :: StackSet i l a s sd -> Workspace i l a 
qcurrentTag = workspace . current


