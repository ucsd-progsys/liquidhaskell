module StackSet where

import Data.Set (Set(..)) 

data LL a = Nil | Cons { head :: a, tail :: LL a }

{-@ data LL a = Nil | Cons { head :: a 
                           , tail :: {v: LL a | not (Set_mem head (LLElts v))  } } 
  @-}

{-@ measure LLElts     :: LL a -> (Set a) 
    LLElts (Nil)       = {v | (Set_emp v)}
    LLElts (Cons x xs) = {v | v = (Set_cup (Set_sng x) (LLElts xs)) }
  @-}

{-@ predicate Disjoint x y   = (Set_emp (Set_cap x y))            @-}  
{-@ predicate NotIn    x y = not (Set_mem x (LLElts y))           @-} 


---------------------------------------------------------------------------------------------

{-@ measure StackElts    :: Stack a -> (Set a) 
    StackElts (St f u d) = (Set_cup (Set_sng f) (Set_cup (LLElts u) (LLElts d)))
  @-}

{-@ data Stack a = St { focus  :: a    
                      , up     :: {vu: LL a | (NotIn focus vu) } 
                      , down   :: {vd: LL a | ((NotIn focus vd) && (Disjoint (LLElts up) (LLElts vd))) } 
                      } 
  @-}

data Stack a = St { focus  :: !a    
                  , up     :: !(LL a) 
                  , down   :: !(LL a)
                  } 

---------------------------------------------------------------------------------------------

{-@ measure MaybeStackElts :: Maybe (Stack a) -> (Set a) 
    MaybeStackElts Nothing  = {v | (? Set_emp(v))  }
    MaybeStackElts (Just s) = {v | v = StackElts s }
  @-}

{-@ measure WorkspaceElts :: Workspace i l a -> (Set a) 
    WorkspaceElts (Workspace t l s) = (MaybeStackElts s) 
  @-}

data Workspace i l a = Workspace  { tag :: !i, layout :: l, stack :: Maybe (Stack a) }

---------------------------------------------------------------------------------------------

{-@ measure ScreenElts :: Screen i l a sid sd -> (Set a) 
    ScreenElts (ScreenElts w s d) = (WorkspaceElts w) 
  @-}

data Screen i l a sid sd = Screen { workspace :: !(Workspace i l a)
                                  , screen :: !sid
                                  , screenDetail :: !sd }

---------------------------------------------------------------------------------------------

{-@ measure ListScreenElts :: [Screen i l a sid sd] -> (Set a) 
    ListScreenElts ([])    =  {v | (Set_emp v)}
    ListScreenElts (x:xs)  =  {v | v = (Set_cup (ScreenElts x) (ListScreenElts xs)) }
  @-}


{-@ measure ListWorkspaceElts :: [Workspace i l a] -> (Set a) 
    ListWorkspaceElts ([])    =  {v | (Set_emp v)}
    ListWorkspaceElts (x:xs)  =  {v | v = (Set_cup (WorkspaceElts x) (ListWorkspaceElts xs)) }
  @-}

data StackSet i l a sid sd =
    StackSet { current  :: !(Screen i l a sid sd)    
             , visible  :: {v : [Screen i l a sid sd] | (Disjoint  (ScreenElts current)     (ListScreenElts v)) }
             , hidden   :: {v : [Workspace i l a]     | ((Disjoint (ScreenElts current)     (ListWorkspaceElts v)) && 
                                                         (Disjoint (ListScreenElts visible) (ListWorkspaceElts v))) }        
             } 

----------------------------------------------------------------------------------------------------------------

{-@ fresh :: a -> Stack a @-}
fresh x = St x Nil Nil

{-@ moveUp :: Stack a -> Stack a @-}
moveUp (St x (Cons y ys) zs) = St y ys (Cons x zs)
moveUp s                     = s 

{-@ moveDn :: Stack a -> Stack a @-}
moveDn (St x ys (Cons z zs)) = St z (Cons x ys) zs
moveDn s                     = s 



