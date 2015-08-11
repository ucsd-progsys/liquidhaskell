module Problems where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RG
import Language.Haskell.Liquid.Prelude



{-@ predicate SetRG X Y =
    (((IsNull X) && (IsNode Y)) ||
     ((IsNode X) && (IsDel Y) && ((val X) = (val Y)) && ((nxt X) = (nxt Y))) ||
     ((IsNode X) && (IsNode Y) && (IsDel (terminalValue (nxt X))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((IsHead X) && (IsHead Y) && (IsDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((IsNode X) && (IsNode Y) && ((val X) = (val Y)) && (nxt X = nxt (shareValue (nxt Y)))) ||
     ((IsHead X) && (IsHead Y) && (nxt X = nxt (shareValue (nxt Y)))) ||
     (X = Y)
     )
@-}
{-@
data Set a <p :: a -> Prop > = 
    Node (node_val :: a<p>) (slack :: { v : a | node_val <= v}) (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a))))
  | DelNode (del_val :: a<p>) (slack :: { v : a | del_val <= v}) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a)))
  | Null
  | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
@-}
data Set a = Node a a ((RGRef (Set a)))
            | DelNode a a ((RGRef (Set a)))
            | Null
            | Head ((RGRef (Set a))) deriving Eq

{- Colin's issue 1 -}

{-@ measure isNull @-}
isNull :: Set a -> Bool
isNull Null = True 
isNull _    = False

{-@ myNext :: l:{Set a | not (isNull l)} -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> ((IsHead l) || (slack l < x))}> a) |
                   ((nxt l) = r) }
@-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v lb n) = n
myNext (DelNode v lb n) = n
myNext (Head n) = n
myNext _ = liquidError "myNext"

{- Colin's issue 2 -}

{-@ assume injectStable :: forall <p :: (Set Int) -> Prop, 
                                   q :: (Set Int) -> Prop,
                                   r :: (Set Int) -> (Set Int) -> Prop,
                                   g :: (Set Int) -> (Set Int) -> Prop>.
                    {x::(Set Int)<q> |- (Set Int)<r x> <: (Set Int)<q>}
                    ref:RGRef<p,r,g> (Set Int) ->
                    {v:(Set Int)<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> (Set Int)) | (ref = r)} @-}
injectStable :: RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
injectStable ref v = liquidAssume undefined ref


{-@ measure nodeclass :: Set a -> Int
    nodeclass (Head n) = 0
    nodeclass (Node v lb n) = 1
    nodeclass (DelNode v lb n) = 2
    nodeclass (Null) = 3
    @-}
{-@ predicate IsHead X = (nodeclass X = 0) @-}
{-@ predicate IsNode X = (nodeclass X = 1) @-}
{-@ predicate IsDel X  = (nodeclass X = 2) @-}
{-@ predicate IsNull X = (nodeclass X = 3) @-}
{-@ measure nxt :: Set a -> (RGRef (Set a))
    nxt (Node v lb n) = n
    nxt (DelNode v lb n) = n
    nxt (Head n) = n
@-}
{-@ measure val :: Set a -> a
    val (Node v lb n) = v
    val (DelNode v lb n) = v
@-}