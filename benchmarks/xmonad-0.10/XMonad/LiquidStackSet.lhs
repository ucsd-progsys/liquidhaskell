Liquid StackSets
================

Culling out types and code to understand invariants.

How do we write the invariants?


\begin{code}
{-@ 

measure tagsList :: [a] -> Set a
tagsList []     = Set.empty
tagsList (x:xs) = Set.union (Set.sng x) (tagsList xs) 

measure tagsStack :: Stack a -> Set a 
tagsStack (Stack x us ds) = Set.union (Set.sng x) (Set.union (elts us) (elts ds))
    
measure tagsMaybeStack :: Maybe (Stack a) -> Set a
tagsMaybeStack (Just s)  = tagsStack s
tagsMaybeStack (Nothing) = Set.empty

measure tagsWorkspace :: Workspace i l a -> Set a
tagsWorkspace (Workspace _ _ s) = tagsMaybeStack s

measure tagsScreen :: Screen i l a sid sd -> Set a
tagsScreen (Screen w _ _)       = tagsWorkspace w 
@-}

\end{code}

type OKScreen  i l a sid sd  = Screen { workspace    :: !(OKWorkspace i l a)
                                      , screen       :: !sid 
                                      , screenDetail :: !sd
                                      }
type OKScreens i l a sid sd  = ...
type OKWorkspace i l a       = ...
type OKWorkspaces i l a      = ...
type OKStackSet i l a sid sd = ...


\begin{code}
data StackSet i l a sid sd =
    StackSet { current  :: !(Screen i l a sid sd)
             , visible  :: [Screen i l a sid sd]
             , hidden   :: [Workspace i l a]
             , floating :: M.Map a RationalRect
             } deriving (Show, Read, Eq)

data Screen i l a sid sd = Screen { workspace :: !(Workspace i l a)
                                  , screen :: !sid
                                  , screenDetail :: !sd }
    deriving (Show, Read, Eq)

data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }
    deriving (Show, Read, Eq)
   
data Stack a = Stack { focus  :: !a    
                     , up     :: [a] <{\fld v -> fld /= v && v /= focus}>  
                     , down   :: [a] <{\fld v -> fld /= v && v /= focus}>
                     }
    deriving (Show, Read, Eq)
\end{code}

type DList a = [a]<{\fld v -> fld != v}>

data Stack a = Stack { focus  :: !a    
                     , up     :: DList {v: a | v != focus}
                     , down   :: DList {v: a | v != focus}
                     } 
    deriving (Show, Read, Eq)



    
