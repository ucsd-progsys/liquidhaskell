{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Language.Haskell.Liquid.GHC.Plugin.Util (
        partitionMaybe
      , extractSpecComments

      -- * Serialising and deserialising things from/to specs.
      , serialiseBareSpecs
      , deserialiseBareSpecs

      -- * Combinators
      , withUnoptimisedCoreBinds

      -- * Aborting the plugin execution
      , pluginAbort
      ) where

import           GhcPlugins                              as GHC
import           Outputable                               ( SDoc
                                                          , showSDoc
                                                          )
import           GHC                                      ( DynFlags )
import           CoreMonad                                ( CoreM )
import           Panic                                    ( throwGhcExceptionIO, GhcException(..) )
import           HscTypes                                 ( ModIface )

import           Control.Monad.IO.Class

import qualified Data.Binary                             as B
import qualified Data.Binary.Get                         as B
import           Data.ByteString.Lazy                     ( ByteString )
import qualified Data.ByteString.Lazy                    as B
import           Data.Typeable
import           Data.Maybe                               ( listToMaybe, catMaybes )
import           Data.Data
import           Data.Either                              ( partitionEithers )

import           Language.Haskell.Liquid.GHC.Plugin.Types ( SpecComment
                                                          )
import           Language.Haskell.Liquid.Types.Specs      ( BareSpec )
import           Language.Haskell.Liquid.GHC.GhcMonadLike (GhcMonadLike)


pluginAbort :: MonadIO m => DynFlags -> SDoc -> m a
pluginAbort dynFlags msg =
  liftIO $ throwGhcExceptionIO $ ProgramError ("LiquidHaskell: " ++ showSDoc dynFlags msg)

-- | Courtesy of [inspection testing](https://github.com/nomeata/inspection-testing/blob/master/src/Test/Inspection/Plugin.hs)
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = partitionEithers . map (\x -> maybe (Left x) Right (f x))

-- | Extracts the spec comments from the Core 'Annotation's. It returns a
-- "cleaned" 'ModGuts' which doesn't contain the deserialised 'Annotation's.
-- This also means that these 'Annotation's /won't/ land into an interface file,
-- and we won't be able to retrieve them back later on.
extractSpecComments :: ModGuts -> (ModGuts, [SpecComment])
extractSpecComments = extractModuleAnnotations

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

--
-- Serialising and deserialising Specs
--

deserialiseBareSpecs :: Module -> ExternalPackageState -> [BareSpec]
deserialiseBareSpecs thisModule eps = extracted
  where
    extracted = findAnns deserialise (eps_ann_env eps) (ModuleTarget thisModule)

    deserialise :: [B.Word8] -> BareSpec
    deserialise payload = B.decode (B.pack payload)

serialiseBareSpecs :: [BareSpec] -> ModGuts -> ModGuts
serialiseBareSpecs specs modGuts = annotated
  where
    thisModule     = mg_module modGuts
    annotated      = modGuts { mg_anns = newAnnotations ++ mg_anns modGuts }
    newAnnotations = map serialise specs

    serialise :: BareSpec -> Annotation
    serialise spec = Annotation (ModuleTarget thisModule) (toSerialized (B.unpack . B.encode) spec)

--
-- Combinators
--

withUnoptimisedCoreBinds :: GhcMonadLike m => [CoreBind] -> ModGuts -> (ModGuts -> m ModGuts) -> m ModGuts
withUnoptimisedCoreBinds unoptimisedBinds oldGuts action = do
  let guts = oldGuts { mg_binds = unoptimisedBinds }
  new <- action guts
  pure $ new { mg_binds = mg_binds oldGuts }
