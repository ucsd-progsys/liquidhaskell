{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Large LH payloads live in an extensible interface field. Only their
-- version and fingerprint live in GHC's boxed-byte annotations. Keeping
-- the fingerprint in an annotation makes it participate in GHC's ordinary
-- interface fingerprinting and recompilation checks.
module Language.Haskell.Liquid.GHC.Plugin.Compact
  ( PayloadId
  , PayloadMarker(..)
  , payloadId
  , payloadMarker
  , decodeMarker
  , stageSpec
  , installInterfaceHook
  , readPayload
  , hasPayload
  , writePayload
  ) where

import qualified Data.Binary as B
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Dynamic
import Data.Typeable (typeOf, typeRep, Proxy(..))
import Data.IORef
import qualified Data.Map.Strict as M
import Data.Word
import Foreign.Ptr (castPtr)
import qualified Liquid.GHC.API as GHC


-- | Fingerprint of the encoded specification payload. The pair holds the two
-- 64-bit words of the 128-bit 'GHC.Fingerprint' produced by 'GHC.fingerprintData',
-- in the same order as that constructor's fields.
-- Stored in the interface marker and dependency references to detect payload
-- changes or mismatches. Together with the full module identity, it forms the
-- key used to reuse decoded specifications in the session cache.
type PayloadId = (Word64, Word64)

-- | 'B.encode' representation:
--
-- @
-- (version, (fingerprintWord1, fingerprintWord2))
--   :: (Word32, (Word64, Word64))
-- @
--
-- * @version@ is the marker format version, currently 1.
-- * The two fingerprint words form the 'PayloadId'
--
-- 'B.encode' writes these unsigned words consecutively in big-endian order:
--
-- @
-- Byte offsets   Contents
--  0..3          Format version (Word32)
--  4..11         First fingerprint word (Word64)
-- 12..19         Second fingerprint word (Word64)
-- @
--
newtype PayloadMarker = PayloadMarker { markerBytes :: [Word8] }

-- | One prepared specification waiting for interface publication: its encoded
-- bytes, their fingerprint, and the usages of the dependencies it consumed.
data PendingSpec = PendingSpec !BS.ByteString !PayloadId ![GHC.Usage]

fieldName :: GHC.FieldName
fieldName = "liquidhaskell.spec.v1"

payloadId :: BS.ByteString -> IO PayloadId
payloadId bytes = BS.useAsCStringLen bytes $ \(ptr, size) -> do
  GHC.Fingerprint a b <- GHC.fingerprintData (castPtr ptr) size
  pure (a, b)

payloadMarker :: PayloadId -> PayloadMarker
payloadMarker fingerprint =
  PayloadMarker $ BL.unpack $ B.encode (1 :: Word32, fingerprint)

decodeMarker :: PayloadMarker -> Either String PayloadId
decodeMarker (PayloadMarker bytes) = case B.decodeOrFail (BL.pack bytes) of
  Left (_, _, err) -> Left $ "Malformed LiquidHaskell interface marker: " ++ err
  Right (rest, _, (version :: Word32, fingerprint))
    | version /= 1 -> Left "Unsupported LiquidHaskell interface version; rebuild dependencies."
    | not (BL.null rest) -> Left "Malformed LiquidHaskell interface marker."
    | otherwise -> Right fingerprint

-- | Prepare the payload and its dependency usages in one update to the module's
-- typed TH-state map, returning the marker to attach as an annotation. The
-- fingerprint is retained for simple-interface rebuilding.
-- A private TypeRep key isolates this state and ties its lifetime to TcGblEnv.
--
-- GHC's entity-level home-module usages can overlook changes to module
-- annotations. LH consumes the whole specification, so record whole-module ABI
-- usages for home modules as well as package modules. GHC's checker resolves
-- these by full module identity in either interface table.
stageSpec :: GHC.TcGblEnv -> BS.ByteString -> [GHC.ModIface] -> IO PayloadMarker
stageSpec tcg bytes ifaces = do
  fingerprint <- payloadId bytes
  usages <- mapM usage ifaces
  let pending = PendingSpec bytes fingerprint usages
  atomicModifyIORef' (GHC.tcg_th_state tcg) $ \state ->
    (M.insert (typeOf pending) (toDyn pending) state, ())
  pure $ payloadMarker fingerprint
  where
    usage iface =
      let !mdl = GHC.mi_module iface
          !fingerprint = GHC.mi_mod_hash iface
      in pure (GHC.UsagePackageModule mdl fingerprint False)

addUsages :: [GHC.Usage] -> GHC.ModIface_ phase -> GHC.ModIface_ phase
addUsages usages iface =
    GHC.set_mi_self_recomp
      ((\info -> info { GHC.mi_sr_usages = usages ++ GHC.mi_sr_usages info }) <$> GHC.mi_self_recomp_info iface)
      iface

-- | Restore the marker in a simple interface and recompute its fingerprints.
--
--  For the simplified interface used with -fno-code, this happens:

--   1. LH supplies the marker. It puts it among the module’s annotations, in tcg_anns.
--   2. GHC constructs a simplified summary. That construction leaves out the annotations, including our marker.
--   3. GHC fingerprints that incomplete summary. It may also write it to disk.
--   4. Our hook receives the finished summary (HscUpdate) and restores the marker.
--   5. We recalculate its fingerprint, because adding information after fingerprinting would otherwise leave the fingerprint describing the previous contents.
--
rebuildSimpleIface :: GHC.HscEnv -> PayloadId -> GHC.ModIface -> IO GHC.ModIface
rebuildSimpleIface env fingerprint iface = do
    let marker = GHC.IfaceAnnotation (GHC.ModuleTarget $ GHC.mi_module iface) $
          GHC.toSerialized markerBytes (payloadMarker fingerprint)
    GHC.mkFullIface env (GHC.set_mi_anns (marker : GHC.mi_anns iface) partial) Nothing Nothing GHC.NoStubs []
  where
    partial =
      GHC.set_mi_decls (map snd $ GHC.mi_decls iface) $
      GHC.set_mi_simplified_core (GHC.mi_simplified_core iface) $
      GHC.set_mi_mod_info (GHC.mi_mod_info iface) $
      GHC.set_mi_deps (GHC.mi_deps iface) $
      GHC.set_mi_exports (GHC.mi_exports iface) $
      GHC.set_mi_fixities (GHC.mi_fixities iface) $
      GHC.set_mi_warns (GHC.mi_warns iface) $
      GHC.set_mi_anns (GHC.mi_anns iface) $
      GHC.set_mi_defaults (GHC.mi_defaults iface) $
      GHC.set_mi_insts (GHC.mi_insts iface) $
      GHC.set_mi_fam_insts (GHC.mi_fam_insts iface) $
      GHC.set_mi_rules (GHC.mi_rules iface) $
      GHC.set_mi_trust (GHC.mi_trust iface) $
      GHC.set_mi_trust_pkg (GHC.mi_trust_pkg iface) $
      GHC.set_mi_complete_matches (GHC.mi_complete_matches iface) $
      GHC.set_mi_docs (GHC.mi_docs iface) $
      GHC.set_mi_top_env (GHC.mi_top_env iface) $
      GHC.set_mi_ext_fields (GHC.mi_ext_fields iface) $
      GHC.set_mi_self_recomp (GHC.mi_self_recomp_info iface) $
      GHC.emptyPartialModIface (GHC.mi_module iface)

writePayload :: BS.ByteString -> GHC.ModIface_ phase -> IO (GHC.ModIface_ phase)
writePayload bytes iface = do
  fields <- GHC.writeField fieldName bytes (GHC.mi_ext_fields iface)
  pure $ GHC.set_mi_ext_fields fields iface

readPayload :: GHC.ModIface -> IO (Maybe BS.ByteString)
readPayload = GHC.readField fieldName . GHC.mi_ext_fields

hasPayload :: GHC.ModIface -> Bool
hasPayload = M.member fieldName . GHC.getExtensibleFields . GHC.mi_ext_fields

installInterfaceHook :: GHC.HscEnv -> GHC.HscEnv
installInterfaceHook env = env { GHC.hsc_hooks = hooks { GHC.runPhaseHook = Just $ GHC.PhaseHook run } }
  where
    hooks = GHC.hsc_hooks env
    previous :: GHC.TPhase a -> IO a
    previous = case GHC.runPhaseHook hooks of
      Nothing -> GHC.runPhase
      Just (GHC.PhaseHook hook) -> hook

    run :: GHC.TPhase a -> IO a
    run phase@(GHC.T_HscPostTc hscEnv summary (GHC.FrontendTypecheck tcg) _ _) = do
      state <- readIORef (GHC.tcg_th_state tcg)
      let pending = M.lookup (typeRep (Proxy :: Proxy PendingSpec)) state >>= fromDynamic
      result <- previous phase
      case pending of
        Nothing -> pure result
        Just (PendingSpec bytes fingerprint usages) -> case result of
          recomp@GHC.HscRecomp { GHC.hscs_partial_iface = iface } -> do
            iface' <- writePayload bytes $ addUsages usages iface
            pure recomp { GHC.hscs_partial_iface = iface' }
          GHC.HscUpdate iface -> do
            rebuilt <- rebuildSimpleIface hscEnv fingerprint $ addUsages usages iface
            iface' <- writePayload bytes rebuilt
            -- GHC writes simple (-fno-code/boot) interfaces inside PostTc.
            -- Rewrite with the field attached, respecting GHC's write flags
            -- and dynamic-too handling.
            GHC.hscMaybeWriteIface (GHC.hsc_logger hscEnv) (GHC.hsc_dflags hscEnv)
              True iface' Nothing (GHC.ms_location summary)
            pure $ GHC.HscUpdate iface'
    run phase = previous phase
