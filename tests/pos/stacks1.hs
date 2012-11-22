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

--| Super Vanilla Operations on Stacks

{-@ fresh :: a -> Stack a @-}
fresh x = St x Nil Nil

{-@ moveUp :: Stack a -> Stack a @-}
moveUp (St x (Cons y ys) zs) = St y ys (Cons x zs)
moveUp s                     = s 

{-@ moveDn :: Stack a -> Stack a @-}
moveDn (St x ys (Cons z zs)) = St z (Cons x ys) zs
moveDn s                     = s 


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
             , floating :: M.Map a RationalRect
             } 

data RationalRect = RationalRect Rational Rational Rational Rational

----------------------------------------------------------------------------------------------------------------

new :: (Integral s) => l -> [i] -> [sd] -> StackSet i l a s sd
new l wids m 
  | not (null wids) && length m <= length wids && not (null m)
  = StackSet cur visi unseen M.empty
  where (seen,unseen) = L.splitAt (length m) $ map (\i -> Workspace i l Nothing) wids
        (cur:visi)    = [ Screen i s sd |  (i, s, sd) <- zip3 seen [0..] m ]
                -- now zip up visibles with their screen id
new _ _ _ = abort "non-positive argument to StackSet.new"


abort :: {v: String | (0 = 1) } -> a
abort x = error $ "xmonad: StackSet: " ++ x
