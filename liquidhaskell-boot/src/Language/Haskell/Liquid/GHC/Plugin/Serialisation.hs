{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Liquid.GHC.Plugin.Serialisation (
      -- * Serialising and deserialising things from/to specs.
        serialiseLiquidLib
      , deserialiseLiquidLib

      ) where

import qualified Data.Array                               as Array

import           Control.Monad
import           Control.Concurrent.MVar

import qualified Data.Binary                             as B
import qualified Data.Binary.Builder                     as Builder
import qualified Data.Binary.Put                         as B
import qualified Data.ByteString.Lazy                    as B
import           Data.Data (Data)
import           Control.Exception
import           Control.Exception.Backtrace
import           Control.Exception.Context
import           Data.Generics (ext0, gmapAccumT)
import qualified Data.HashMap.Strict                     as M
import           Data.Maybe                               ( listToMaybe, mapMaybe )
import           Data.IORef
import           Data.Unique
import           GHC.Stack (HasCallStack)
import           System.IO.Unsafe (unsafePerformIO)
import           System.Mem.Weak (Weak, deRefWeak)

import qualified Liquid.GHC.API as GHC
import           Language.Haskell.Liquid.GHC.Plugin.Types (LiquidLib, SpecReference(..), libDeps)
import qualified Language.Haskell.Liquid.GHC.Plugin.Compact as Compact
import qualified Language.Haskell.Liquid.GHC.Plugin.Cache as Cache
import           Language.Haskell.Liquid.Types.Names


--
-- Serialising and deserialising Specs
--

serialiseLiquidLib :: GHC.HscEnv -> LiquidLib -> GHC.TcGblEnv -> IO GHC.Annotation
serialiseLiquidLib env lib tcg = do
    bytes <- B.toStrict <$> encodeLiquidLib lib
    ifaces <- forM (libDeps lib) $ \ref ->
      GHC.lookupIfaceByModuleHsc env (GHC.unStableModule $ specModule ref) >>=
        maybe (ioError $ userError "LiquidHaskell: dependency interface disappeared during verification") pure
    marker <- Compact.stageSpec tcg bytes ifaces
    pure $ GHC.Annotation (GHC.ModuleTarget $ GHC.tcg_mod tcg) $
      GHC.toSerialized Compact.markerBytes marker

-- GHC's interface cache holds encoded data; this cache holds canonical decoded
-- module specs, never merged transitive closures. Retain decoded libraries for
-- the most recently used session. Switching sessions replaces this cache;
-- returning to an earlier session starts a fresh cache. The EPS weak key also
-- releases the cache when its session is garbage collected.
type LibraryCache = Cache.Cache SpecReference LiquidLib
-- The unique identifier prevents a replaced session's finalizer from clearing
-- a newer cache. The weak EPS reference identifies the owning GHC session.
data SessionCache = SessionCache !Unique !(Weak (IORef GHC.ExternalPackageState)) !LibraryCache

{-# NOINLINE sessionCache #-}
sessionCache :: MVar (Maybe SessionCache)
sessionCache = unsafePerformIO $ newMVar Nothing

getLibraryCache :: GHC.HscEnv -> IO LibraryCache
getLibraryCache env = modifyMVar sessionCache $ \session -> do
    found <- case session of
      Nothing -> pure Nothing
      Just (SessionCache _ weak cache) -> do
        alive <- deRefWeak weak
        pure $ if alive == Just epsRef then Just cache else Nothing
    case found of
      Just cache -> pure (session, cache)
      Nothing -> do
        cache <- Cache.newCache
        key <- newUnique
        weak <- mkWeakIORef epsRef $ modifyMVar_ sessionCache $ \current ->
          case current of
            Just (SessionCache k _ _) | k == key -> pure Nothing
            _ -> pure current
        pure (Just (SessionCache key weak cache), cache)
  where
    epsRef = GHC.euc_eps $ GHC.ue_eps $ GHC.hsc_unit_env env

-- | Retrieve a module's specification from the interfaces already available
-- in the GHC session. The caller is responsible for loading the interface;
-- this function does not discover imports or search for assumption modules.
--
-- Returns 'Nothing' when no specification marker is found and no compact
-- payload field is present in the available interface. This also includes
-- an unavailable interface with no marker. Otherwise returns 'Just' the
-- module-and-fingerprint reference and its decoded library. A matching
-- session-cache entry is reused; on a miss the payload is read, checked
-- against the marker's fingerprint, decoded, and retained.
--
-- Raises an 'IOError' for a malformed or unsupported marker, or a compact
-- payload without a marker. On a cache miss it also raises an 'IOError' if
-- the interface or payload is missing, or the payload fingerprint disagrees
-- with the marker. GHC and binary-decoding exceptions propagate rather than
-- being converted to 'Nothing'. The returned library is not fully evaluated,
-- so errors in lazy name resolution may arise when its contents are used.
--
-- May populate the session's decoded-library cache and GHC name cache.
deserialiseLiquidLib
  :: GHC.HscEnv
  -- ^ Supplies home-module interfaces and external-package annotations and
  -- interfaces, the EPS 'IORef' identifying the session's decoded-library
  -- cache, and the 'GHC.NameCache' used to resolve serialized GHC names.
  -> GHC.Module
  -- ^ Full module identity, including the package/unit, whose spec is requested.
  -> IO (Maybe (SpecReference, LiquidLib))
deserialiseLiquidLib env thisModule = do
    eps <- readIORef $ GHC.euc_eps $ GHC.ue_eps $ GHC.hsc_unit_env env
    home <- GHC.lookupHugByModule thisModule (GHC.hsc_HUG env)
    let homeAnnotations = case home of
          Just info | GHC.mi_module (GHC.hm_iface info) == thisModule ->
            GHC.ifAnnotatedValue <$> GHC.mi_anns (GHC.hm_iface info)
          _ -> []
        annotations decoder =
          mapMaybe (GHC.fromSerialized decoder) homeAnnotations ++
          GHC.findAnns decoder (GHC.eps_ann_env eps) (GHC.ModuleTarget thisModule)
    case listToMaybe $ annotations Compact.PayloadMarker of
      Nothing -> do
        iface <- GHC.lookupIfaceByModuleHsc env thisModule
        -- A compact payload requires its marker for identification and validation.
        if maybe False Compact.hasPayload iface
          then ioError $ userError $ "LiquidHaskell: missing specification marker for " ++
            GHC.renderModule thisModule ++ ". Rebuild this dependency with the current LiquidHaskell plugin."
          else pure Nothing
      Just marker -> do
        fingerprint <- either (ioError . userError) pure $ Compact.decodeMarker marker
        let reference = SpecReference (GHC.toStableModule thisModule) fingerprint
        cache <- getLibraryCache env
        lib <- Cache.cached cache reference $ do
          iface <- GHC.lookupIfaceByModuleHsc env thisModule
          bytes <- maybe (pure Nothing) Compact.getPayload iface >>= maybe missingPayload pure
          actual <- Compact.payloadId bytes
          unless (actual == fingerprint) $
            ioError $ userError $ "LiquidHaskell: corrupt specification for " ++ GHC.renderModule thisModule
          -- Lazy name decoding must retain only the NameCache, not a selector
          -- thunk keeping the entire HscEnv (and our weak session key) alive.
          let nameCache = GHC.hsc_NC env
          nameCache `seq` decodeLiquidLib nameCache (B.fromStrict bytes)
        pure $ Just (reference, lib)
  where
    missingPayload = ioError $ userError $ "LiquidHaskell: missing compact specification for " ++
      GHC.renderModule thisModule ++ ". Rebuild this dependency with the current LiquidHaskell plugin."

encodeLiquidLib :: LiquidLib -> IO B.ByteString
encodeLiquidLib lib0 = rethrowWithCallStackIO $ do
    let (lib1, ns) = collectLHNames lib0
    bh <- GHC.openBinMem (1024*1024)
    GHC.putWithUserData GHC.QuietBinIFace GHC.SafeExtraCompression bh ns
    GHC.withBinBuffer bh $ \bs ->
      return $ Builder.toLazyByteString $ B.execPut (B.put lib1) <> Builder.fromByteString bs

decodeLiquidLib :: GHC.NameCache -> B.ByteString -> IO LiquidLib
decodeLiquidLib nameCache bs0 = rethrowWithCallStackIO $ do
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

-- | Rethrow an exception so we have an indication of where it was thrown in
-- the stack trace.
rethrowWithCallStackIO :: HasCallStack => IO a -> IO a
rethrowWithCallStackIO action = catchNoPropagate action $ \(ExceptionWithContext ctx (e :: SomeException)) -> do
    btAnn <- collectBacktraces
    rethrowIO $ ExceptionWithContext (addExceptionAnnotation btAnn ctx) e
