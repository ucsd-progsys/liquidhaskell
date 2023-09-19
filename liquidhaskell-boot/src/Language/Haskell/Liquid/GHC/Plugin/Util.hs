{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.GHC.Plugin.Util (
      -- * Serialising and deserialising things from/to specs.
        serialiseLiquidLib
      , deserialiseLiquidLib
      , deserialiseLiquidLibFromEPS

      -- * Aborting the plugin execution
      , pluginAbort
      ) where

import           Data.Foldable                            ( asum )

import           Control.Monad.IO.Class
import           Control.Monad

import qualified Data.Binary                             as B
import           Data.Binary                              ( Binary )
import qualified Data.ByteString.Lazy                    as B
import           Data.Typeable
import           Data.Maybe                               ( listToMaybe )

import           Liquid.GHC.API
import           Language.Haskell.Liquid.GHC.Plugin.Types (LiquidLib)


pluginAbort :: MonadIO m => String -> m a
pluginAbort = liftIO . throwGhcExceptionIO . ProgramError

--
-- Serialising and deserialising Specs
--

deserialiseBinaryObjectFromEPS
  :: forall a. (Typeable a, Binary a)
  => Module
  -> ExternalPackageState
  -> Maybe a
deserialiseBinaryObjectFromEPS thisModule eps = extractFromEps
  where
    extractFromEps :: Maybe a
    extractFromEps = listToMaybe $ findAnns (B.decode . B.pack) (eps_ann_env eps) (ModuleTarget thisModule)

deserialiseBinaryObject :: forall a. (Typeable a, Binary a)
                        => Module
                        -> ExternalPackageState
                        -> HomePackageTable
                        -> Maybe a
deserialiseBinaryObject thisModule eps hpt =
    asum [extractFromHpt, deserialiseBinaryObjectFromEPS thisModule eps]
  where
    extractFromHpt :: Maybe a
    extractFromHpt = do
      modInfo <- lookupHpt hpt (moduleName thisModule)
      guard (thisModule == (mi_module . hm_iface $ modInfo))
      xs <- mapM (fromSerialized deserialise . ifAnnotatedValue) (mi_anns . hm_iface $ modInfo)
      listToMaybe xs

    deserialise :: [B.Word8] -> a
    deserialise payload = B.decode (B.pack payload)

serialiseBinaryObject :: forall a. (Binary a, Typeable a) => a -> Module -> Annotation
serialiseBinaryObject obj thisModule = serialised
  where
    serialised :: Annotation
    serialised = Annotation (ModuleTarget thisModule) (toSerialized (B.unpack . B.encode) obj)

-- | Serialise a 'LiquidLib', removing the termination checks from the target.
serialiseLiquidLib :: LiquidLib -> Module -> Annotation
serialiseLiquidLib lib = serialiseBinaryObject @LiquidLib lib

deserialiseLiquidLib :: Module -> ExternalPackageState -> HomePackageTable -> Maybe LiquidLib
deserialiseLiquidLib thisModule = deserialiseBinaryObject @LiquidLib thisModule

deserialiseLiquidLibFromEPS :: Module -> ExternalPackageState -> Maybe LiquidLib
deserialiseLiquidLibFromEPS = deserialiseBinaryObjectFromEPS @LiquidLib
