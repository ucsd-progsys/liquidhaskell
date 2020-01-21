{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.GHC.Plugin.Util (
        partitionMaybe
      , extractSpecComments
      , lookupTcStableData
      ) where

import GhcPlugins as GHC

import           Data.Typeable
import           Data.Bifunctor                           ( second )
import           Data.Maybe                               ( listToMaybe )
import           Data.Data
import           Data.Either                              ( partitionEithers )

import           Language.Haskell.Liquid.GHC.Plugin.Types ( SpecComment
                                                          , TcStableData
                                                          )

-- | Courtesy of [inspection testing](https://github.com/nomeata/inspection-testing/blob/master/src/Test/Inspection/Plugin.hs)
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = partitionEithers . map (\x -> maybe (Left x) Right (f x))

-- | Extracts the spec comments from the Core 'Annotation's. It returns a
-- "cleaned" 'ModGuts' which doesn't contain the deserialised 'Annotation's.
-- This also means that these 'Annotation's /won't/ land into an interface file,
-- and we won't be able to retrieve them back later on.
extractSpecComments :: ModGuts -> (ModGuts, [SpecComment])
extractSpecComments = extractModuleAnnotations

lookupTcStableData :: ModGuts -> (ModGuts, Maybe TcStableData)
lookupTcStableData = second listToMaybe . extractModuleAnnotations

-- | Tries to deserialise the 'Annotation's in the input 'ModGuts', pruning the latter
-- upon successful deserialisation.
extractModuleAnnotations :: forall a. (Typeable a, Data a) => ModGuts -> (ModGuts, [a])
extractModuleAnnotations guts = (guts', extracted)
  where
    thisModule = mg_module guts
    (anns_clean, extracted) = partitionMaybe tryDeserialise (mg_anns guts)
    guts' = guts { mg_anns = anns_clean }

    tryDeserialise :: Annotation -> Maybe a
    tryDeserialise (Annotation (ModuleTarget m) payload)
        | thisModule == m = fromSerialized deserializeWithData payload
        | otherwise       = Nothing
    tryDeserialise (Annotation (NamedTarget _) payload) --NOTE(adn) What is the correct behaviour here?
        | Just a <- fromSerialized deserializeWithData payload
        = Just a
    tryDeserialise _
        = Nothing

