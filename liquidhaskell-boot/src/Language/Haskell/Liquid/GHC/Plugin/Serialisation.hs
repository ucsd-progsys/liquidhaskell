{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.GHC.Plugin.Serialisation (
      -- * Serialising and deserialising things from/to specs.
        serialiseLiquidLib
      , deserialiseLiquidLib
      , deserialiseLiquidLibFromEPS

      ) where

import qualified Data.Array                               as Array
import           Data.Foldable                            ( asum )

import           Control.Monad

import qualified Data.Binary                             as B
import qualified Data.Binary.Builder                     as Builder
import qualified Data.Binary.Put                         as B
import qualified Data.ByteString.Lazy                    as B
import           Data.Data (Data)
import           Data.Generics (ext0, gmapAccumT)
import           Data.HashMap.Strict                     as M
import           Data.Maybe                               ( listToMaybe )
import           Data.Word                               (Word8)

import qualified Liquid.GHC.API as GHC
import           Language.Haskell.Liquid.GHC.Plugin.Types (LiquidLib)
import           Language.Haskell.Liquid.Types.Names


--
-- Serialising and deserialising Specs
--

getLiquidLibBytesFromEPS
  :: GHC.Module
  -> GHC.ExternalPackageState
  -> Maybe LiquidLibBytes
getLiquidLibBytesFromEPS thisModule eps = extractFromEps
  where
    extractFromEps :: Maybe LiquidLibBytes
    extractFromEps = listToMaybe $ GHC.findAnns LiquidLibBytes (GHC.eps_ann_env eps) (GHC.ModuleTarget thisModule)

getLiquidLibBytes :: GHC.Module
                        -> GHC.ExternalPackageState
                        -> GHC.HomePackageTable
                        -> Maybe LiquidLibBytes
getLiquidLibBytes thisModule eps hpt =
    asum [extractFromHpt, getLiquidLibBytesFromEPS thisModule eps]
  where
    extractFromHpt :: Maybe LiquidLibBytes
    extractFromHpt = do
      modInfo <- GHC.lookupHpt hpt (GHC.moduleName thisModule)
      guard (thisModule == (GHC.mi_module . GHC.hm_iface $ modInfo))
      xs <- mapM (GHC.fromSerialized LiquidLibBytes . GHC.ifAnnotatedValue) (GHC.mi_anns . GHC.hm_iface $ modInfo)
      listToMaybe xs

newtype LiquidLibBytes = LiquidLibBytes { unLiquidLibBytes :: [Word8] }

-- | Serialise a 'LiquidLib', removing the termination checks from the target.
serialiseLiquidLib :: LiquidLib -> GHC.Module -> IO GHC.Annotation
serialiseLiquidLib lib thisModule = do
    bs <- encodeLiquidLib lib
    return $ GHC.Annotation
      (GHC.ModuleTarget thisModule)
      (GHC.toSerialized unLiquidLibBytes (LiquidLibBytes $ B.unpack bs))

deserialiseLiquidLib
  :: GHC.Module
  -> GHC.ExternalPackageState
  -> GHC.HomePackageTable
  -> GHC.NameCache
  -> IO (Maybe LiquidLib)
deserialiseLiquidLib thisModule eps hpt nameCache = do
    let mlibbs = getLiquidLibBytes thisModule eps hpt
    case mlibbs of
      Just (LiquidLibBytes ws) -> do
        let bs = B.pack ws
        Just <$> decodeLiquidLib nameCache bs
      _ -> return Nothing

deserialiseLiquidLibFromEPS
  :: GHC.Module
  -> GHC.ExternalPackageState
  -> GHC.NameCache
  -> IO (Maybe LiquidLib)
deserialiseLiquidLibFromEPS thisModule eps nameCache = do
    let mlibbs = getLiquidLibBytesFromEPS thisModule eps
    case mlibbs of
      Just (LiquidLibBytes ws) -> do
        let bs = B.pack ws
        Just <$> decodeLiquidLib nameCache bs
      _ -> return Nothing

encodeLiquidLib :: LiquidLib -> IO B.ByteString
encodeLiquidLib lib0 = do
    let (lib1, ns) = collectLHNames lib0
    bh <- GHC.openBinMem (1024*1024)
    GHC.putWithUserData GHC.QuietBinIFace bh ns
    GHC.withBinBuffer bh $ \bs ->
      return $ Builder.toLazyByteString $ B.execPut (B.put lib1) <> Builder.fromByteString bs

decodeLiquidLib :: GHC.NameCache -> B.ByteString -> IO LiquidLib
decodeLiquidLib nameCache bs0 = do
    case B.decodeOrFail bs0 of
      Left (_, _, err) -> error $ "decodeLiquidLib: decodeOrFail: " ++ err
      Right (bs1, _, lib) -> do
        bh <- GHC.unsafeUnpackBinBuffer $ B.toStrict bs1
        ns <- GHC.getWithUserData nameCache bh
        let n = fromIntegral $ length ns
            arr = Array.listArray (0, n - 1) ns
        return $ mapLHNames (resolveLHNameIndex arr) lib
  where
    resolveLHNameIndex :: Array.Array Word LHResolvedName -> LHName -> LHName
    resolveLHNameIndex arr lhname =
      case getLHNameResolved lhname of
        LHRIndex i ->
          if i <= snd (Array.bounds arr) then
            makeResolvedLHName (arr Array.! i) (getLHNameSymbol lhname)
          else
            error $ "decodeLiquidLib: index out of bounds: " ++ show (i, Array.bounds arr)
        _ ->
          lhname

newtype AccF a b = AccF { unAccF :: a -> b -> (a, b) }

collectLHNames :: Data a => a -> (a, [LHResolvedName])
collectLHNames t =
    let ((_, _, xs), t') = go (0, M.empty, []) t
     in (t', reverse xs)
  where
    go
      :: Data a
      => (Word, M.HashMap LHResolvedName Word, [LHResolvedName])
      -> a
      -> ((Word, M.HashMap LHResolvedName Word, [LHResolvedName]), a)
    go = gmapAccumT $ unAccF $ AccF go `ext0` AccF collectName

    collectName acc@(sz, m, xs) n = case M.lookup n m of
      Just i -> (acc, LHRIndex i)
      Nothing -> ((sz + 1, M.insert n sz m, n : xs), LHRIndex sz)
