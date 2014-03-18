module RG where

import Data.IORef as R

{- Liquid Rely-Guarantee References / RG-Haskell

   This is an embedding of a slightly simplified rely-guarantee reference system.
   (See "Rely-Guarantee References for Refinement Types over Aliased Mutable Data,"
   by Gordon, Ernst, and Grossman, PLDI'13.  I promise to never use such a long paper
   title ever again.)

   The key idea in that paper is to augment each reference with a predicate refining
   the referent and heap reachable from it, and binary relations describing permitted
   local actions (the guarantee) and possible remote actions (the rely):
   
                ref{T|P}[R,G]
   
   The terminology comes from rely-guarantee reasoning, from the concurrent program
   logic literature.  As long as
   each reference's guarantee relation is a subrelation of any alias's rely (plus some
   subtle side conditions about nested references), any predicate P that is /stable/
   with respect to a rely R on a given reference (forall x y, P x -> R x y -> P y)
   is trivially preserved by any update through an alias that respects that alias's
   guarantee relation.

   Embedding into Liquid Haskell instead of Coq requires a few weakenings of the
   original design, so we lose expressiveness but gain substantially from automation
   and being a refinement of a language with real programs!  The main simplifications are:
    - TEMPORARILY, rely and guarantee are the same, until we get rolling.  In general,
      we must always have that the guarantee implies the rely, since Haskell wouldn't
      respect the substructural restrictions.  Leaving them the same makes weakening the
      guarantee unsound, so we should fix this soon.
    - Predicates and relations can refer only to the immediate referent for now.
    - Folding (pushing a local restriction through to new references reached via
      dereference) doesn't exist in this system, mostly because all predicates and
      relations can restrict only one cell.

-}

{- We wrap IORefs in a new constructor to add ghost parameters for the predicate and
   relation(s).  It is a standard GHC optimization to eliminate the overhead since there is a single
   constructor with one physical argument, so at runtime these will look the same as IORefs:
   we won't pay time or space overhead. -}
{-@ data RGRef a <p :: a -> Prop, r :: a -> a -> Prop > 
    = Wrap (r :: R.IORef a<p>) @-}
data RGRef a = Wrap (R.IORef a)

{- A stability proof can be embedded into LH as a function of type:
    x:a<p> -> y:a<r x> -> {v:a<p> | v = y}
    This encodes the requirement that knowing P x and R x y is sufficient to deduce P y.
-}
-- Requires explicit type anno for LH type to refine the inferred Haskell type
{-@ stable_monocount :: x:{v:Int | v > 0 } -> y:{v:Int | x <= v } -> {v:Int | ((v = y) && (v > 0)) } @-}
stable_monocount :: Int -> Int -> Int
stable_monocount x y = y

-- Testing / debugging function
{-@ generic_accept_stable :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    ()
                    @-}
generic_accept_stable :: (a -> a -> a) -> ()
generic_accept_stable pf = ()

{-@ proves_reflexivity :: x:{v:Int | v > 0} -> y:{v:Int | v > 0} -> {v:Int | v > 0} @-}
proves_reflexivity :: Int -> Int -> Int
proves_reflexivity x y = x

test :: ()
test = generic_accept_stable proves_reflexivity

{-@ proves_nothing :: x:a -> y:a -> {v:a | (v = y)} @-}
proves_nothing :: a -> a -> a
proves_nothing x y = y --proves_nothing x y

{- TODO: e2 is a hack to sidestep the inference of false for r,
   it forces r to be inhabited. -}
{-@ newRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    e:a<p> -> 
                    e2:a<r e> ->
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO (RGRef <p, r> a) @-}
newRGRef :: a -> a -> (a -> a -> a) -> IO (RGRef a)
newRGRef e e2 stabilityPf = do {
                            r <- newIORef e;
                            return (Wrap r)
                         }

-- LH's assume statement seems to only affect spec files
{-@ readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    RGRef<p, r> a -> IO (a<p>) @-}
readRGRef (Wrap x) = readIORef x

-- TODO: full spec, fix pf type
writeRGRef :: RGRef a -> a -> (a -> a -> Bool) -> IO ()
writeRGRef  (Wrap x) e pf = writeIORef x e


{- modifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    r:(RGRef<p, r> a) ->
                    f:(x:a<p> -> a<r x>) ->
                    pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO () @-}
modifyRGRef :: RGRef a -> (a -> a) -> (a -> a -> a) -> IO ()
modifyRGRef (Wrap x) f pf = modifyIORef x (\ v -> pf v (f v))
--
--{- modifyRGRef' :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
--                    RGRef<p, r> a ->
--                    f:(x:a<p> -> a<r x>) ->
--                    IO () @-}
---- TODO: strictify, so we don't de-optimize modifyIORef' calls
--modifyRGRef' (Wrap x) f = modifyIORef x f
--
--
main = do {
          r <- newRGRef 1 3 stable_monocount; -- SHOULD BE ref{Int|>0}[<=,<=]
          -- Instead we get ref{Int|>0}[false,false] !
          r2 <- newRGRef 2 9 proves_nothing;  -- SHOULD BE ref{Int|>0}[havoc,havoc].
          -- Instead we get ref{Int|>0}[false,false] !
          --r3 <- newRGRef 3 10 proves_reflexivity; -- BAD, correctly rejected
          return ()
       }


-- What are the subtyping rules for data structure params that aren't
-- used within the structure?
{-@ unused_contra :: RGRef <{\x -> x > 0}, {\x y -> x <= y}> Int -> RGRef <{\x -> x > 0}, {\x y -> false}> Int @-}
unused_contra :: RGRef Int -> RGRef Int
unused_contra r = r


{-@ unused_covar :: RGRef <{\x -> x > 0}, {\x y -> false}> Int -> RGRef <{\x -> x > 0}, {\x y -> x <= y}> Int @-}
unused_covar :: RGRef Int -> RGRef Int
unused_covar r = r
-- It looks like there's simply no constraint!
