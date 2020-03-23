{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Language.Haskell.Liquid.GHC.Plugin.Util (
        partitionMaybe
      , extractSpecComments

      -- * Serialising and deserialising things from/to specs.
      , serialiseBareSpec
      , deserialiseBareSpec
      , serialiseLiquidLib
      , deserialiseLiquidLib

      -- * Aborting the plugin execution
      , pluginAbort
      ) where

import           GhcPlugins                              as GHC
import           Outputable                               ( SDoc
                                                          , showSDoc
                                                          , text
                                                          , (<+>)
                                                          , showSDocUnsafe
                                                          )
import           UniqDFM
import           IfaceSyn
import           GHC                                      ( DynFlags )
import           CoreMonad                                ( CoreM )
import           Panic                                    ( throwGhcExceptionIO, GhcException(..) )
import           HscTypes                                 ( ModIface )
import           Data.Foldable                            ( asum )

import           Control.Monad.IO.Class
import           Control.Monad

import qualified Data.Binary                             as B
import           Data.Binary                              ( Binary )
import qualified Data.Binary.Get                         as B
import           Data.ByteString.Lazy                     ( ByteString )
import qualified Data.ByteString.Lazy                    as B
import           Data.Typeable
import           Data.Maybe                               ( listToMaybe, catMaybes )
import           Data.Data
import           Data.Either                              ( partitionEithers )

import           Language.Haskell.Liquid.GHC.Plugin.Types ( SpecComment
                                                          , LiquidLib
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

deserialiseBinaryObject :: forall a. (Typeable a, Binary a) 
                        => Module 
                        -> ExternalPackageState 
                        -> HomePackageTable
                        -> Maybe a
deserialiseBinaryObject thisModule eps hpt = asum [extractFromHpt, extractFromEps]
  where
    extractFromEps :: Maybe a
    extractFromEps = listToMaybe $ findAnns deserialise (eps_ann_env eps) (ModuleTarget thisModule)

    extractFromHpt :: Maybe a
    extractFromHpt = do
      modInfo <- lookupUDFM hpt (moduleName thisModule)
      guard (thisModule == (mi_module . hm_iface $ modInfo))
      xs <- mapM (fromSerialized deserialise . ifAnnotatedValue) (mi_anns . hm_iface $ modInfo)
      listToMaybe xs

    deserialise :: [B.Word8] -> a
    deserialise payload = B.decode (B.pack payload)

serialiseBinaryObject :: forall a. (Binary a, Typeable a) => a -> ModGuts -> ModGuts
serialiseBinaryObject obj modGuts = annotated
  where
    thisModule     = mg_module modGuts
    annotated      = modGuts { mg_anns = newAnnotation : mg_anns modGuts }
    newAnnotation  = serialise

    serialise :: Annotation
    serialise = Annotation (ModuleTarget thisModule) (toSerialized (B.unpack . B.encode) obj)

deserialiseBareSpec :: Module -> ExternalPackageState -> HomePackageTable -> Maybe BareSpec
deserialiseBareSpec thisModule = deserialiseBinaryObject @BareSpec thisModule

serialiseBareSpec :: BareSpec -> ModGuts -> ModGuts
serialiseBareSpec specs = serialiseBinaryObject @BareSpec specs

-- | Serialise a 'LiquidLib', removing the termination checks from the target.
serialiseLiquidLib :: LiquidLib -> ModGuts -> ModGuts
serialiseLiquidLib lib = serialiseBinaryObject @LiquidLib lib

deserialiseLiquidLib :: Module -> ExternalPackageState -> HomePackageTable -> Maybe LiquidLib
deserialiseLiquidLib thisModule = deserialiseBinaryObject @LiquidLib thisModule
