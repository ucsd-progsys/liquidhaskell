{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module provides functions to manage the serialized form of
-- LifterSpecs.
--
-- LiftedSpec payloads are kept in an extensible interface field. ('fieldName')
-- They are too large to keep in module annotations with an @[Word8]@
-- representation.
--
-- Their version and fingerprint live in module annotations, which makes it
-- participate in GHC's ordinary interface fingerprinting and recompilation
-- checks.
module Language.Haskell.Liquid.GHC.Plugin.Iface
  ( PayloadId
  , PayloadMarker(..)
  , payloadId
  , payloadMarker
  , decodeMarker
  , stageSpec
  , installInterfaceHook
  , getPayload
  , hasPayload
  ) where

import qualified Data.Binary as B
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Dynamic
import Data.Typeable (typeOf, typeRep, Proxy(..))
import Data.IORef
import qualified Data.Map.Strict as M
import Data.Word
import qualified Liquid.GHC.API as GHC


-- | Fingerprint of the encoded specification payload. The pair holds the two
-- 64-bit words of the 128-bit 'GHC.Fingerprint' produced by 'GHC.fingerprintByteString',
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

-- | Information needed to produce an interface file.
--
-- It contains the serialized LiftedSpec to store, the fingerprint of the
-- LiftedSpec, and its dependencies in the form of 'GHC.Usages'.
--
data PendingSpec = PendingSpec !BS.ByteString !PayloadId ![GHC.Usage]

-- | Name used to store the serialized LiftedSpec in an extensible interface
-- field.
fieldName :: GHC.FieldName
fieldName = "liquidhaskell.spec.v1"

-- | Computes the fingerprint of a bytestring
payloadId :: BS.ByteString -> PayloadId
payloadId bytes =
  let GHC.Fingerprint a b = GHC.fingerprintByteString bytes
   in (a, b)

payloadMarker :: PayloadId -> PayloadMarker
payloadMarker fingerprint =
  PayloadMarker $ BL.unpack $ B.encode (1 :: Word32, fingerprint)

-- | Checks that the marker has the expected version and extracts the
-- fingerprint.
decodeMarker :: PayloadMarker -> Either String PayloadId
decodeMarker (PayloadMarker bytes) = case B.decodeOrFail (BL.pack bytes) of
  Left (_, _, err) -> Left $ "Malformed LiquidHaskell interface marker: " ++ err
  Right (rest, _, (version :: Word32, fingerprint))
    | version /= 1 -> Left "Unsupported LiquidHaskell interface version; rebuild dependencies."
    | not (BL.null rest) -> Left "Malformed LiquidHaskell interface marker."
    | otherwise -> Right fingerprint

-- | Stores a bytestring in the 'GHC.TcGblEnv' in the TH-state map.
--
-- Returns the marker corresponding to the bytestring.
--
-- The given 'GHC.ModIface's are recorded as usages so they cause recompilation
-- when they change.
--
stageSpec :: GHC.TcGblEnv -> BS.ByteString -> [GHC.ModIface] -> IO PayloadMarker
stageSpec tcg bytes ifaces = do
    pending@(PendingSpec _ fingerprint _) <- mkPendingSpec
    atomicModifyIORef' (GHC.tcg_th_state tcg) $ \state ->
      (M.insert (typeOf pending) (toDyn pending) state, ())
    pure $ payloadMarker fingerprint
  where
    mkPendingSpec = do
      usages <- mapM asUsage ifaces
      return $ PendingSpec bytes (payloadId bytes) usages

    asUsage iface =
      let !mdl = GHC.mi_module iface
          !fingerprint = GHC.mi_mod_hash iface
      in pure (GHC.UsagePackageModule mdl fingerprint False)

-- | Add a payload marker to the ModIface, and recompute the hashes.
rebuildSimpleIface :: GHC.HscEnv -> PayloadMarker -> GHC.ModIface -> IO GHC.ModIface
rebuildSimpleIface env pmarker iface = do
    -- Recomputing the hashes of the interface requires rebuilding it, so we
    -- take measures in _arityGuard and _unused_fields to ensure that we don't
    -- forget to copy relevant fields.
    let marker = GHC.IfaceAnnotation (GHC.ModuleTarget $ GHC.mi_module iface) $
          GHC.toSerialized markerBytes pmarker
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

    {- HLINT ignore "Use record patterns" -}
    -- Compile-time guard to catch arity changes in ModIface when upgrading GHC.
    _arityGuard :: GHC.ModIface -> ()
    _arityGuard
      (GHC.ModIface
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _) = ()

    {- HLINT ignore "Evaluate" -}
    -- Compile-time guard to catch changes in the fields that are unused when
    -- upgrading GHC.
    _unused_fields :: ()
    _unused_fields =
       const
         ()
         ( GHC.mi_sig_of
         , GHC.mi_hsc_src
         , GHC.mi_iface_hash
         , GHC.mi_public
         , GHC.mi_abi_hashes
         , GHC.mi_hi_bytes
         , GHC.mi_fix_fn
         , GHC.mi_hash_fn
         , GHC.mi_decl_warn_fn
         , GHC.mi_export_warn_fn
         )

addPayloadToExtFields :: BS.ByteString -> GHC.ModIface_ phase -> IO (GHC.ModIface_ phase)
addPayloadToExtFields bytes iface = do
  fields <- GHC.writeField fieldName bytes (GHC.mi_ext_fields iface)
  pure $ GHC.set_mi_ext_fields fields iface

getPayload :: GHC.ModIface -> IO (Maybe BS.ByteString)
getPayload = GHC.readField fieldName . GHC.mi_ext_fields

hasPayload :: GHC.ModIface -> Bool
hasPayload = M.member fieldName . GHC.getExtensibleFields . GHC.mi_ext_fields

-- | Install a hook that inserts LiftedSpecs in interfaces.
--
-- There are two kinds of interface files that GHC can write: simple and full.
-- Simple interfaces are produced when using @-fno-code@.
-- See Note [Writing interface files] in "GHC.Driver.Main" for more details.
--
-- We need to insert LiftedSpecs in both kinds of interfaces, and we achieve
-- this with 'GHC.runPhaseHook'.
--
-- When a LiftedSpec is ready, @serialiseLiquidLib@ is called. This stages the
-- serialized spec with 'stageSpec' for inclusion in the interface.
--
-- When GHC produces the interface, the hook installed here adds the staged spec
-- to the interface.
--
installInterfaceHook :: GHC.HscEnv -> GHC.HscEnv
installInterfaceHook env =
    env { GHC.hsc_hooks = hooks { GHC.runPhaseHook = Just $ GHC.PhaseHook run } }
  where
    hooks = GHC.hsc_hooks env
    runPreviousHook :: GHC.TPhase a -> IO a
    runPreviousHook = case GHC.runPhaseHook hooks of
      Nothing -> GHC.runPhase
      Just (GHC.PhaseHook hook) -> hook

    run :: GHC.TPhase a -> IO a
    -- Typechecking has completed
    run phase@(GHC.T_HscPostTc hscEnv summary (GHC.FrontendTypecheck tcg) _ _) = do
      -- Retrieve the staged serialized LiftedSpec
      pendingSpec <- do
        state <- readIORef (GHC.tcg_th_state tcg)
        let md = M.lookup (typeRep (Proxy :: Proxy PendingSpec)) state
        return (md >>= fromDynamic)
      result <- runPreviousHook phase
      case pendingSpec of
        -- If there is no pending spec, there is no need to change the interface.
        Nothing -> pure result
        Just (PendingSpec bytes fingerprint usages) -> case result of
          -- The module needs recompilation so we add the serialized LiftedSpec.
          recomp@GHC.HscRecomp { GHC.hscs_partial_iface = iface } -> do
            iface' <- addPayloadToExtFields bytes $ addUsages usages iface
            pure recomp { GHC.hscs_partial_iface = iface' }
          -- The module does not need recompilation, but the interface needs
          -- updating. This case is entered when GHC is called with -fno-code.
          -- The interface file has been already written, so after updating the
          -- interface we write it to disk again.
          GHC.HscUpdate iface -> do
            -- Extra wart: in this path, GHC ignores tcg_anns and our payload
            -- marker in it. We use rebuildSimpleIface to still add the marker
            -- to the interface file.
            rebuilt <- rebuildSimpleIface
              hscEnv
              (payloadMarker fingerprint)
              (addUsages usages iface)
            iface' <- addPayloadToExtFields bytes rebuilt
            -- GHC writes simple (-fno-code/boot) interfaces inside PostTc.
            -- Rewrite with the field attached, respecting GHC's write flags
            -- and dynamic-too handling.
            GHC.hscMaybeWriteIface (GHC.hsc_logger hscEnv) (GHC.hsc_dflags hscEnv)
              True iface' Nothing (GHC.ms_location summary)
            pure $ GHC.HscUpdate iface'
    run phase = runPreviousHook phase

    addUsages :: [GHC.Usage] -> GHC.ModIface_ phase -> GHC.ModIface_ phase
    addUsages usages iface =
      let updateSRUsages info =
            info { GHC.mi_sr_usages = usages ++ GHC.mi_sr_usages info }
       in GHC.set_mi_self_recomp
            (updateSRUsages <$> GHC.mi_self_recomp_info iface)
            iface
