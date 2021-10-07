-- | A reference implementation for Data.ShareMap
module ShareMapReference where

import           Data.Hashable (Hashable)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.List (find)

-- | See "Data.ShareMap" for documentation.
data ShareMap k v = ShareMap
  { -- | Contains all the values in the ShareMap.
    toHashMap :: HashMap k v
  , -- | Contains all the keys in the ShareMap.
    --
    -- All sets in @keyPartitions@ are disjoint.
    -- Every key in in @keyPartitions@ is present in @toHashMap@.
    -- If @k1@ and @k2@ belong to the same set @s@ in @keyPartitions@
    -- then @toHashMap ! k1 == toHashMap ! k2@.
    keyPartitions :: [HashSet k]
  }
  deriving Show

empty :: ShareMap k v
empty = ShareMap HashMap.empty []

insertWith
  :: (Hashable k, Eq k)
  => (v -> v -> v)
  -> k
  -> v
  -> ShareMap k v
  -> ShareMap k v
insertWith f k v sm =
  let h = toHashMap sm
      ks = keyPartitions sm
   in case find (HashSet.member k) ks of
     Nothing ->
       sm
         { toHashMap = HashMap.insertWith f k v h
         , keyPartitions = HashSet.singleton k : ks
         }
     Just keys ->
       sm
         { toHashMap =
             HashSet.foldl' (\h' k' -> HashMap.insertWith f k' v h') h keys
         }

mergeKeysWith
  :: (Hashable k, Eq k)
  => (v -> v -> v)
  -> k
  -> k
  -> ShareMap k v
  -> ShareMap k v
mergeKeysWith f k0 k1 sm | k0 /= k1 =
  let h = toHashMap sm
      ks = keyPartitions sm
   in case break (HashSet.member k0) ks of
     (_before0, []) -> case break (HashSet.member k1) ks of
       (_before1, []) -> sm
       (before1, keys1 : after1) ->
         sm
           { toHashMap = HashMap.insertWith f k0 (h HashMap.! k1) h
           , keyPartitions =
               HashSet.insert k0 keys1 : before1 ++ after1
           }
     (before0, keys0 : after0)
       | HashSet.member k1 keys0 -> sm
       | otherwise ->
         let v0 = h HashMap.! k0
             v1 = maybe v0 (f v0) $ HashMap.lookup k1 h
             keys'
               | otherwise = case break (HashSet.member k1) (before0 ++ after0) of
                 (before1, []) ->
                    HashSet.insert k1 keys0 : before1
                 (before1, keys1 : after1)->
                    HashSet.union keys0 keys1 : before1 ++ after1
          in sm
              { toHashMap =
                  HashSet.foldl' (\h' k' -> HashMap.insert k' v1 h') h (head keys')
              , keyPartitions = keys'
              }
mergeKeysWith _ _ _ sm = sm
