{-# Language EmptyDataDecls #-}

{-@ LIQUID "--eliminate=none" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-pattern-inline" @-}

module FindRec where


import RIO2
import Data.Map
import Data.Set
import Language.Haskell.Liquid.Prelude
import Privileges

{- ** API ** -}
{-@ measure caps :: World -> Map FHandle Privilege @-}
{-@ measure active :: World -> Set FHandle @-}
{-@ measure derive :: Path -> Bool @-}

data Path = P String deriving Eq
data FHandle = FH Int deriving Eq

-- ELIMINATED
{- Deriv(v:World, x:FHandle): (pwrite (pcreateFilePrivs (Map_select (caps v) x))) @-}
{- Write(v:World, x:FHandle): (pwrite (Map_select (caps v) x)) @-}
{- List(v:World, x:FHandle): (pcontents (Map_select (caps v) x)) @-}
{- Lkup(v:World, x:FHandle): (plookup (Map_select (caps v) x)) @-}
{- Deriv(v:World,w1:World,x:FHandle,h:FHandle): (caps v) = (Map_store (caps w1) x (pcreateFilePrivs (Map_select (caps w1) h))) @-}
{- MpEq0(v:World,w:World,x:FHandle): (Map_select (caps v) x) = (Map_select (caps w) x) @-}
{- ActiveSub(v:World, w:World): Set_sub (active v) (active w)                         @-}
{- UpdActive(v:World,w1:World,x:FHandle): (active v) = (Set_cup (Set_sng x) (active w1)) @-}
{- MpEq0(v:World,w:World,x:FHandle,z:FHandle): (Map_select (caps v) x) = (Map_select (caps w) z) @-}

-- NEEDED
{-@ qualif Sto(v:World,w1:World,x:FHandle,h:FHandle): (caps v) = (Map_store (caps w1) x (Map_select (caps w1) h)) @-}
{-@ qualif MpEq0(v:World,b:FHandle,x:FHandle): (Map_select (caps v) x) = (Map_select (caps v) b) @-}


{-@ predicate Active W F = Set_mem F (active W) @-}
{-@ predicate HasPriv W P F = (Active W F) && (P (Map_select (caps W) F)) @-}
{-@ predicate Rd  W F = HasPriv W pread F @-}
{-@ predicate Wr  W F = HasPriv W pwrite F @-}
{-@ predicate Cr  W F = HasPriv W pcreateFile F @-}
{-@ predicate Lkup W F = HasPriv W plookup F @-}
{-@ predicate Lst W F = HasPriv W pcontents F @-}
{-@ predicate CrWO W F = (pwrite (pcreateFilePrivs (Map_select (caps W) F))) @-}
{-@ predicate CrAll W F = (pcreateFilePrivs (Map_select (caps W) F)) = (Map_select (caps W) F) @-}

{-@ predicate UpdActive W1 W2 F = (~ (Active W1 F)) && (Active W2 F) && ((active W2) = (Set_cup (Set_sng F) (active W1))) @-}
{-@ predicate UpdCaps W1 W2 X Y = (caps W2) = (Map_store (caps W1) X (Map_select (caps W1) Y)) @-}
{-@ predicate DeriveCaps W1 W2 X Y = (caps W2) = (Map_store (caps W1) X (pcreateFilePrivs (Map_select (caps W1) Y))) @-}
{-@ predicate NoChange W1 W2 = (active W1) = (active W2) && (caps W1) = (caps W2) @-}


{- ** API ** -}
{-@ contents ::
     d:FHandle -> RIO<{v:World | Lst v d},\w1 x -> {v:World | NoChange w1 v}> [Path]
@-}
contents :: FHandle -> RIO [Path]
contents = undefined
{-@ measure parent :: FHandle -> FHandle @-}
{-@ flookup ::
     h:FHandle -> Path -> RIO<{v:World | Lkup v h },\w x -> {v:World | UpdActive w v x && UpdCaps w v x h }> FHandle @-}
flookup :: FHandle -> Path -> RIO FHandle
flookup = undefined

{-@ create ::
     h:FHandle -> p:Path -> RIO<{v:World | Cr v h},\w1 x -> {v:World | (UpdActive w1 v x) && DeriveCaps w1 v x h}> FHandle @-}
create :: FHandle -> Path -> RIO FHandle
create = undefined

{-@ createDir ::
     h:FHandle -> p:Path -> RIO<{w:World | Cr w h},\w1 x -> {w2:World | (UpdActive w1 w2 x) && UpdCaps w1 w2 x h}> FHandle @-}
createDir :: FHandle -> Path -> RIO FHandle
createDir = undefined

{-@ write ::
     h:FHandle -> s:String -> RIO<{w:World | Wr w h},\w1 x -> {w2:World | NoChange w1 w2}> () @-}
write :: FHandle -> String -> RIO ()
write = undefined

{-@ fread ::
     h:FHandle -> RIO<{w:World | Rd w h},\w1 x -> {w2:World | NoChange w1 w2}> String @-}
fread :: FHandle -> RIO String
fread = undefined

{-@ isFile :: h:FHandle -> Bool @-}
isFile :: FHandle -> Bool
isFile = undefined

{-@ isDir :: h:FHandle -> Bool @-}
isDir :: FHandle -> Bool
isDir = undefined

{-@
forM_ :: forall <i :: World -> Bool>.
         [a] ->
         (a -> RIO <i,\w1 x -> {v:World<i> | true}> b) ->
         RIO <i,\w1 x -> {v:World<i> | true}> ()
@-}
forM_ :: [a] -> (a -> RIO b) -> RIO ()
forM_ []     _ = return ()
forM_ (x:xs) m = m x >> forM_ xs m

{-@
when :: forall <p    :: World -> Bool>.
        z:Bool ->
        RIO <p, \w1 x -> {v:World<p> | true}> () ->
        RIO <p, \w1 x -> {v:World<p> | true}> ()
@-}
when :: Bool -> RIO () -> RIO ()
when False  _ = return ()

{-@ predicate StableInv W1 W2 X Y = NoChange W1 W2 || (UpdActive W1 W2 Y && (UpdCaps W1 W2 Y X || DeriveCaps W1 W2 Y X)) @-}

-- | GOOD!!
{-@ predicate FindSpec V F = Lst V F && Lkup V F @-}

-- | BAD!!
{- predicate FindSpec V F = Active V F && Lst V F @-}

{-@
findExec ::
  forall <i :: World -> Bool, p :: FHandle -> World -> Bool, q :: FHandle -> Bool>.
  { x :: FHandle, b :: FHandle, w :: World<i> |- {v:World | StableInv w v x b } <: World<i> }
  { f :: FHandle<q> |- World<i> <: World<p f> }
  { f :: FHandle<q>, z::FHandle |- {v:World<p f> | (Active v z) && (Map_select (caps v) f) == (Map_select (caps v) z)} <: World<p z> }
  f:FHandle<q> ->
  (z:FHandle -> RIO<{v:World<p z> | true },\w x -> {v:World | NoChange w v }> ()) ->
  RIO <{v:World<i> | FindSpec v f},\w x -> {v:World<i> | FindSpec v f }> ()
@-}
findExec :: FHandle -> (FHandle -> RIO ()) -> RIO ()
findExec f cmd = do
  when (isFile f) $
       (cmd f >>= return)
  when (isDir f) $ do
    cs <- contents f
    forM_ cs $ \p -> do
      h <- flookup f p
      (findExec h cmd >>= return)


{-@
  prepend :: f:FHandle -> String ->
          RIO <{v:World | Lst v f && Lkup v f && Wr v f} ,True> () @-}
prepend :: FHandle -> String -> RIO ()
prepend f s = findExec f (\f -> write f s)
