module RG where

import Language.Haskell.Liquid.Prelude
import Data.IORef as R
import GHC.Base
import Unsafe.Coerce

{- This is the main implementation of rgref primitives -}

{- We wrap IORefs in a new constructor to add ghost parameters for the predicate and
   relation(s).  It is a standard GHC optimization to eliminate the overhead since there is a single
   constructor with one physical argument, so at runtime these will look the same as IORefs:
   we won't pay time or space overhead. (In fact, in GHC, IORefs are a single constructor wrapping an STRef.) -}
{- data RGRef a <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop > 
    = Wrap (rgref_ref :: R.IORef a<p>) @-}
data RGRef a = Wrap (R.IORef a)
    deriving Eq

{- assume forgetIOTriple :: forall <p :: RealWorld -> Prop, r :: RealWorld -> a -> Prop, q :: a -> Prop>.
                             IO (a<q>) -> IO (a<q>) @-}
forgetIOTriple :: IO a -> IO a
forgetIOTriple a = a

{- A stability proof can be embedded into LH as a function of type:
    x:a<p> -> y:a<r x> -> {v:a<p> | v = y}
    This encodes the requirement that knowing P x and R x y is sufficient to deduce P y.
-}
{- A relational implication can be embedded as a function of type:
    x:a -> y:a<g x> -> {v:() | r x y }
-}

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}
{-@ measure getsnd :: (a, b) -> b
    getsnd (x, y) = y
  @-}

{- TODO: e2 is a hack to sidestep the inference of false for r,
   it forces r to be inhabited. -}
-- ((r (getfst v) (getsnd v)) /\ (v = (x,y)))
{-@ newRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x::a<p> |- a<r x> <: a<p>}
                    {x::a<p> |- a<g x> <: a<r x>}
                    {x::a<p> |- {v:a | v = x} <: a<g x>}
                    e:a<p> -> 
                    IO (RGRef <p, r, g> a) @-}
newRGRef :: a -> IO (RGRef a)
newRGRef e = do r <- newIORef e
                return (Wrap r)

-- We'll be needing some witness of past values
{- measure pastValue :: RGRef a -> a -> Prop @-}
{-@ qualif PastValue(r:RGRef a, x:a): (pastValue r x) @-}
{-@ measure terminalValue :: RGRef a -> a @-}
{- Colin's issue 1: comment out qualif: Non Prop-}
{- qualif TerminalValue(r:RGRef a): (terminalValue r) @-}
-- This is for carrying strong (identity) refinement into sharing/publication
{-@ measure shareValue :: RGRef a -> a @-}
{- Colin's issue 1: comment out qualif: Non Prop-}
{- qualif ShareValue(r:RGRef a): (shareValue r) @-}

{-@ assume axiom_pastIsTerminal :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
                             ref:RGRef<p,r,g> a ->
                             v:{v:a | (pastValue ref v)} ->
                             (x:{x:a | x = v} -> y:a<r x> -> {z:a | ((z = y) && (z = x))}) ->
                             (x:{x:a | x = v} -> y:a<g x> -> {z:a | ((z = y) && (z = x))}) ->
                             { b : Bool | (((terminalValue ref) = v) <=> (pastValue ref v))}
                             @-}
axiom_pastIsTerminal :: RGRef a -> a -> (a -> a -> a) -> (a -> a -> a) -> Bool
axiom_pastIsTerminal = undefined

{- A more general, but less pleasant to use way to exploit observations of stable properties.
 - If we observe that some past value of ref has property q, and q is stable w.r.t. r, we can
 - conclude that current and future values of ref also satisfy q. -}
{-@ assume injectStable :: forall <p :: a -> Prop, 
                                         q :: a -> Prop,
                                         r :: a -> a -> Prop,
                                         g :: a -> a -> Prop>.
                    {x::a<q> |- a<r x> <: a<q>}
                    ref:RGRef<p,r,g> a ->
                    {v:a<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> a) | (ref = r)} @-}
injectStable :: RGRef a -> a -> RGRef a
injectStable ref v = liquidAssume undefined ref
-- TODO: Can we do the above without undefined? it gives a warning...
{-@ assume injectStable2 :: forall <p :: a -> Prop, 
                                         q :: a -> Prop,
                                         r :: a -> a -> Prop,
                                         g :: a -> a -> Prop>.
                    pf:(j:a<q> -> k:a<r j> -> {z:a<q> | z = k}) ->
                    ref:RGRef<p,r,g> a ->
                    {v:a<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> a) | (ref = r)} @-}
injectStable2 :: (a -> a -> a) -> RGRef a -> a -> RGRef a
injectStable2 pf ref v = liquidAssume undefined ref
-- TODO: Can we do the above without undefined? it gives a warning...

                -- { x::b |- b <: a }
{-@ assume downcast :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
                { x::b |- b<r x> <: b<p> }
                ref:RGRef<p,r,g> a ->
                {v:b | pastValue ref v } ->
                {r : RGRef<p,r,g> b | ref = r } @-}
downcast :: RGRef a -> b -> RGRef b
downcast r v =  (unsafeCoerce r)


{-@ assume typecheck_pastval :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
                                x:RGRef<p,r,g> a ->
                                v:{v:a | (pastValue x v)} ->
                                {q:a | (q = v)} @-}
typecheck_pastval :: RGRef a -> a -> a
typecheck_pastval x v = v

{-@ assume readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
                    x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
readRGRef (Wrap x) = readIORef x

{-@ assume readRGRef2 :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
                    x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
readRGRef2 (Wrap x) = readIORef x

-- Again, would be nice to tie to pointsTo
{-@ assume writeRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>. 
                          x:(RGRef<p,r,g> a) -> 
                          old:a -> 
                          new:a<r old> -> 
                          (IO ()) @-}
writeRGRef :: RGRef a -> a -> a -> IO ()
writeRGRef  (Wrap x) old new = writeIORef x new

{- assume Data.IORef.modifyIORef :: forall <p :: a -> Prop>. IORef a<p> -> (a<p> -> a<p>) -> IO () @-}

{-@ modifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
modifyRGRef :: RGRef a -> (a -> a) -> IO ()
modifyRGRef (Wrap x) f = modifyIORef x f --(\ v -> pf v (f v))

{-@ modifyRGRef' :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
-- TODO: strictify, so we don't de-optimize modifyIORef' calls
modifyRGRef' :: RGRef a -> (a -> a) -> IO ()
modifyRGRef' (Wrap x) f = modifyIORef' x f --(\ v -> pf v (f v))

{-@ atomicModifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
atomicModifyRGRef :: RGRef a -> (a -> a) -> IO ()
atomicModifyRGRef (Wrap x) f = atomicModifyIORef' x (\ v -> ((f v),()))

{- The following is an adaptation of atomCAS from GHC's testsuite/tests/concurrent/prog003/CASList.hs -}
{-@ rgCAS :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
             {x::a<p> |- a<g x> <: a<p>}
             Eq a =>
             RGRef<p,r,g> a -> old:a<p> -> new:a<g old> ->
             IO Bool
@-}
rgCAS :: Eq a => RGRef a -> a -> a -> IO Bool
rgCAS (Wrap ptr) old new =
   atomicModifyIORef' ptr (\ cur -> if cur == old
                                   then (new, True)
                                   else (cur, False))

{-@ rgCASpublish :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pb :: b -> Prop, rb :: b -> b -> Prop, gb :: b -> b -> Prop>.
             {x::a<p> |- a<g x> <: a<p>}
             {x::b<pb> |- b<rb x> <: b<pb>}
             {x::b<pb> |- b<gb x> <: b<rb x>}
             {x::b<pb> |- {v:b | v = x} <: b<gb x>}
             Eq a =>
             e:b<pb> ->
             RGRef<p,r,g> a -> old:a<p> -> new:(({r:(RGRef<pb,rb,gb> b) | shareValue r = e}) -> a<g old>) ->
             IO Bool
@-}
rgCASpublish :: Eq a => b -> RGRef a -> a -> (RGRef b -> a) -> IO Bool
rgCASpublish e (Wrap ptr) old new =
   do pub <- newRGRef e
      atomicModifyIORef' ptr (\ cur -> if cur == old
                                      then (new (liquidAssume (coerce pub e) pub), True)
                                      else (cur, False))
           where
           {-@ assume coerce :: forall <pb :: b -> Prop, rb :: b -> b -> Prop, gb :: b -> b -> Prop>.
                         r:RGRef<pb,rb,gb> b -> e:b -> {x:Bool | shareValue r = e} @-}
           coerce :: RGRef b -> b -> Bool
           coerce r e = undefined