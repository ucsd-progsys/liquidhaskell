{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module GetSet5 where

data GState k v = GState 
  { sVals :: [(k, v)] -- ^ binders and their values
  , sDef  :: v        -- ^ default value (for missing binder)
  }  

{-@ reflect set @-}
set :: GState k v -> k -> v -> GState k v 
set (GState kvs v0) k v = GState ((k,v) : kvs) v0 

{-@ reflect get @-}
get :: (Eq k) => GState k v -> k -> v 
get (GState []          v0) key = v0
get (GState ((k,v):kvs) v0) key = if key == k then v else get (GState kvs v0) key

-- WTF do we need the silly "GState {}" below?
{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: k -> k -> v -> GState k v -> () 
lemma_get_not_set _ _ _ (GState {}) = ()
