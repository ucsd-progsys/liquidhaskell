{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module State where

import Prelude hiding ((++), const, max)
import ProofCombinators

data GState k v = Init v | Bind k v (GState k v)

{-@ reflect init @-}
init :: v -> GState k v
init v = Init v

{-@ reflect set @-}
set :: GState k v -> k -> v -> GState k v
set s k v = Bind k v s

{-@ reflect get @-}
get :: (Eq k) => GState k v -> k -> v
get (Init v)     _   = v
get (Bind k v s) key = if key == k then v else get s key

{-@ lemma_get_set :: k:_ -> v:_ -> s:_ -> { get (set s k v) k == v }  @-}
lemma_get_set :: k -> v -> GState k v -> Proof 
lemma_get_set _ _ _ = () 

{-@ lemma_get_not_set :: k0:_ -> k:{k /= k0} -> val:_ -> s:_ 
                      -> { get (set s k val) k0 = get s k0 }  @-}
lemma_get_not_set :: k -> k -> v -> GState k v -> Proof 
lemma_get_not_set _ _ _ (Bind {}) = ()
lemma_get_not_set _ _ _ (Init {}) = ()
