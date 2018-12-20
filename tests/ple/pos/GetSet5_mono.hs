{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module GetSet5 where

type K = Int 
type V = Int 

data GState = GState 
  { sVals :: [(K, V)] -- ^ binders and their values
  , sDef  :: V        -- ^ default value (for missing binder)
  }  

{-@ reflect set @-}
set :: GState -> K -> V -> GState
set (GState kvs v0) k v = GState ((k,v) : kvs) v0 

{-@ reflect get @-}
get :: GState -> K -> V 
get (GState []          v0) key = v0
get (GState ((k,v):kvs) v0) key = if key == k then v else get (GState kvs v0) key

{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: K -> K -> V -> GState -> () 
lemma_get_not_set _ _ _ _ = ()
