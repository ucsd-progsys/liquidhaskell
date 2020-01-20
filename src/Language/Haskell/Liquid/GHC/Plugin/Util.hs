
module Language.Haskell.Liquid.GHC.Plugin.Util (
        partitionMaybe
      , extractSpecComments
      , findSpecComments
      ) where

import GhcPlugins as GHC

import Data.Either (partitionEithers)

import Language.Haskell.Liquid.GHC.Plugin.Types (SpecComment)

-- | Courtesy of [inspection testing](https://github.com/nomeata/inspection-testing/blob/master/src/Test/Inspection/Plugin.hs)
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = partitionEithers . map (\x -> maybe (Left x) Right (f x))

-- | Extracts the spec comments from the Core 'Annotation's. It returns a
-- "cleaned" 'ModGuts' which doesn't contain the deserialised 'Annotation's.
-- This also means that these 'Annotation's /won't/ land into an interface file,
-- and we won't be able to retrieve them back later on.
extractSpecComments :: ModGuts -> (ModGuts, [SpecComment])
extractSpecComments = extractSpecComments' True

-- | Like 'extractSpecComments', but preserve the 'Annotation's.
findSpecComments :: ModGuts -> (ModGuts, [SpecComment])
findSpecComments = extractSpecComments' False

-- | General version of 'extractSpecComments' which allows to specify whether or
-- not the found annotations needs to be pruned from the input 'ModGuts'.
extractSpecComments' :: Bool 
                     -- ^ Remove the found specs from the annotations.
                     -> ModGuts 
                     -> (ModGuts, [SpecComment])
extractSpecComments' cleanAnnotations guts = (guts', specComments)
  where
    (anns_clean, specComments) = partitionMaybe lookupSpecComments (mg_anns guts)
    guts' = if cleanAnnotations then guts { mg_anns = anns_clean } else guts

    lookupSpecComments :: Annotation -> Maybe SpecComment
    lookupSpecComments (Annotation (ModuleTarget _) payload)
        | Just specComment <- fromSerialized deserializeWithData payload
        = Just specComment
    lookupSpecComments (Annotation (NamedTarget _) payload)
        | Just specComment <- fromSerialized deserializeWithData payload
        = Just specComment
    lookupSpecComments _
        = Nothing

