module

public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants
public meta import DY.Meta.CombineMacro

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProtocolInvariants`: the top-level instances of TreeSync and TreeKEM
(equational theories, trace entries, crypto predicates and usages, bytes and trace invariants),
built with `#combine`, and the bundles of invariants assumed by the proofs (MLS*'s `has_treesync_and_treekem_invariants`,
established by `treesync_treekem_protocol_invariants_correct`).
-/

namespace MLS.TreeKEM.ProtocolInvariants

open DY DY.PersistentLocalState
open DySlop DySlop.Signature DySlop.KdfExpand DySlop.Aead DySlop.Mac DySlop.HPKE
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.Map (Map)

/-! ## Equational theories -/

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  DY.Random,
  DY.Literal,
  DY.Concat,
  DY.Hash,
  DySlop.KdfExtract,
  DySlop.KdfExpand,
  DySlop.Kem,
  DySlop.Signature,
  DySlop.Aead,
  DySlop.Mac

public instance: HasSymbolicBytes where

/-! ## Trace entries -/

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  DY.Random,
  CompromisableState TreeSyncSignatureKeyState,
  CompromisableState (TreeSyncPublicState TreeKEM.tkt),
  CompromisableState (Map AsCacheKey AsCacheValue),
  CompromisableState (Map GroupManagerKey GroupManagerValue),
  CompromisableState (Map (KeyPackage Bytes TreeKEM.tkt) KeyPackageManagerValue),
  ProtocolEvent (LeafNodeSignedEvent TreeKEM.tkt),
  ProtocolEvent (GroupHasTreeEvent TreeKEM.tkt),
  CompromisableState TreeKEMNodeKeysState,
  CompromisableState TreeKEMEpochSecret,
  CompromisableState BareTreeSyncTreeKEMState,
  CompromisableState OnePskState,
  CompromisableState (Map PskStoreKey PskStoreValue),
  CompromisableState (Map ProposalCacheKey ProposalAndSender),
  CompromisableState (Map UpdateCacheKey UpdateCacheValue),
  CompromisableState BootstrapInitKeyState,
  CompromisableState KeyPackageStorePre,
  ProtocolEvent IAmInGroup,
  ProtocolEvent KeyPackageHasBeenVerified,
  ProtocolEvent (LeafNodeHasBeenVerified TreeKEM.tkt)

public instance: HasTreeSyncExecTrace TreeKEM.tkt where
public instance: HasTreeKEMExecTrace where

#combine +toplevel into ProofEntryT from
  Network,
  DY.Random,
  CompromisableState TreeSyncSignatureKeyState,
  CompromisableState (TreeSyncPublicState TreeKEM.tkt),
  CompromisableState (Map AsCacheKey AsCacheValue),
  CompromisableState (Map GroupManagerKey GroupManagerValue),
  CompromisableState (Map (KeyPackage Bytes TreeKEM.tkt) KeyPackageManagerValue),
  ProtocolEvent (LeafNodeSignedEvent TreeKEM.tkt),
  ProtocolEvent (GroupHasTreeEvent TreeKEM.tkt),
  CompromisableState TreeKEMNodeKeysState,
  CompromisableState TreeKEMEpochSecret,
  CompromisableState BareTreeSyncTreeKEMState,
  CompromisableState OnePskState,
  CompromisableState (Map PskStoreKey PskStoreValue),
  CompromisableState (Map ProposalCacheKey ProposalAndSender),
  CompromisableState (Map UpdateCacheKey UpdateCacheValue),
  CompromisableState BootstrapInitKeyState,
  CompromisableState KeyPackageStorePre,
  ProtocolEvent IAmInGroup,
  ProtocolEvent KeyPackageHasBeenVerified,
  ProtocolEvent (LeafNodeHasBeenVerified TreeKEM.tkt)

/-! ## Crypto usages and predicates -/

/-! ### KDF.Expand usages (ExpandWithLabel) -/

-- The sources of `#combine` are named `X.expandWithLabelUsage`.
namespace derivedPsk public abbrev expandWithLabelUsage := expandUsageExtractedkeyDerivedpsk end derivedPsk
namespace epoch public abbrev expandWithLabelUsage := expandUsageExtractedkeyEpoch end epoch
namespace joiner public abbrev expandWithLabelUsage := expandUsageExtractedkeyJoiner end joiner
namespace welcome public abbrev expandWithLabelUsage := expandUsageExtractedkeyWelcome end welcome
namespace welcomeKey public abbrev expandWithLabelUsage := expandUsageWelcomeKey end welcomeKey
namespace welcomeNonce public abbrev expandWithLabelUsage := expandUsageWelcomeNonce end welcomeNonce
namespace pathSecretNode public abbrev expandWithLabelUsage := expandUsagePathSecretNode end pathSecretNode
namespace pathSecretPath public abbrev expandWithLabelUsage := expandUsagePathSecretPath end pathSecretPath
namespace epochAuthentication public abbrev expandWithLabelUsage := expandUsageEpochAuthentication end epochAuthentication
namespace epochConfirmation public abbrev expandWithLabelUsage := expandUsageEpochConfirmation end epochConfirmation
namespace epochEncryption public abbrev expandWithLabelUsage := expandUsageEpochEncryption end epochEncryption
namespace epochExporter public abbrev expandWithLabelUsage := expandUsageEpochExporter end epochExporter
namespace epochExternal public abbrev expandWithLabelUsage := expandUsageEpochExternal end epochExternal
namespace epochInit public abbrev expandWithLabelUsage := expandUsageEpochInit end epochInit
namespace epochMembership public abbrev expandWithLabelUsage := expandUsageEpochMembership end epochMembership
namespace epochResumption public abbrev expandWithLabelUsage := expandUsageEpochResumption end epochResumption
namespace epochSenderdata public abbrev expandWithLabelUsage := expandUsageEpochSenderdata end epochSenderdata

-- Port of `extractedkey_kdf_expand_usage` (with `all_extractedkey_kdf_expand_usage`).
namespace extractedKey
#combine +toplevel into ExpandWithLabelUsage from derivedPsk, epoch, joiner, welcome
public abbrev kdfExpandUsage := ExpandWithLabelUsage.toKdfExpandUsage "KDF.ExtractedKey" expandWithLabelUsage
end extractedKey

-- Port of `welcome_kdf_expand_usage` (with `all_welcome_kdf_expand_usage`).
namespace welcomeSecret
#combine +toplevel into ExpandWithLabelUsage from welcomeKey, welcomeNonce
public abbrev kdfExpandUsage := ExpandWithLabelUsage.toKdfExpandUsage "MLS.Bootstrap.WelcomeSecret" expandWithLabelUsage
end welcomeSecret

-- Port of `path_kdf_expand_usage` (with `all_path_kdf_expand_usage`).
namespace pathSecret
#combine +toplevel into ExpandWithLabelUsage from pathSecretNode, pathSecretPath
public abbrev kdfExpandUsage := ExpandWithLabelUsage.toKdfExpandUsage "MLS.PathSecret" expandWithLabelUsage
end pathSecret

-- Port of `epoch_kdf_expand_usage` (with `all_epoch_kdf_expand_usage`).
namespace epochSecret
#combine +toplevel into ExpandWithLabelUsage from
  epochAuthentication,
  epochConfirmation,
  epochEncryption,
  epochExporter,
  epochExternal,
  epochInit,
  epochMembership,
  epochResumption,
  epochSenderdata
public abbrev kdfExpandUsage := ExpandWithLabelUsage.toKdfExpandUsage "MLS.TreeKEM.EpochSecret" expandWithLabelUsage
end epochSecret

namespace confirmationKey public abbrev kdfExpandUsage := expandUsageConfirmationTag end confirmationKey

/-! ### KDF.Expand usages (port of `all_kdf_expand_usage` and `treesync_treekem_crypto_usages`) -/

#combine +toplevel into KdfExpandUsage from
  DySlop.HPKE,
  confirmationKey,
  extractedKey,
  welcomeSecret,
  pathSecret,
  epochSecret

public instance: ExpandWithLabelUsage.Has "KDF.ExtractedKey" extractedKey.expandWithLabelUsage :=
  .ofToKdfExpandUsage _ _
public instance: ExpandWithLabelUsage.Has "MLS.Bootstrap.WelcomeSecret" welcomeSecret.expandWithLabelUsage :=
  .ofToKdfExpandUsage _ _
public instance: ExpandWithLabelUsage.Has "MLS.PathSecret" pathSecret.expandWithLabelUsage :=
  .ofToKdfExpandUsage _ _
public instance: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" epochSecret.expandWithLabelUsage :=
  .ofToKdfExpandUsage _ _

/-! ### HPKE predicates (EncryptWithLabel) -/

namespace welcomeHpke public abbrev encryptWithLabelPred := mlsHpkeWelcomePred end welcomeHpke
namespace updatePathNodeHpke public abbrev encryptWithLabelPred := mlsHpkeUpdatepathnodePred end updatePathNodeHpke

-- Port of `init_hpke_pred` (with `all_init_hpke_pred`).
namespace initHpkeKey
#combine +toplevel into EncryptWithLabelPred from welcomeHpke
public abbrev hpkePred := EncryptWithLabelPred.toHpkePred "MLS.InitHpkeKey" encryptWithLabelPred
end initHpkeKey

-- Port of `node_hpke_pred` (with `all_node_hpke_pred`).
namespace nodeHpkeKey
#combine +toplevel into EncryptWithLabelPred from updatePathNodeHpke
public abbrev hpkePred := EncryptWithLabelPred.toHpkePred "MLS.NodeHpkeKey" encryptWithLabelPred
end nodeHpkeKey

/-! ### HPKE predicate (port of `all_hpke_pred` and `hpke_pred`) -/

#combine +toplevel into HpkePred from initHpkeKey, nodeHpkeKey

public instance: EncryptWithLabelPred.Has "MLS.InitHpkeKey" initHpkeKey.encryptWithLabelPred := .ofToHpkePred _ _
public instance: EncryptWithLabelPred.Has "MLS.NodeHpkeKey" nodeHpkeKey.encryptWithLabelPred := .ofToHpkePred _ _

/-! ### AEAD predicate (port of `all_aead_pred`) -/

namespace welcomeAead public abbrev aeadPred := aeadGroupInfoPred end welcomeAead

#combine +toplevel into AeadPred from DySlop.HPKE, welcomeAead

/-! ### Signature predicate (port of `all_leafnode_signature_pred`, `leafnode_signature_pred` and `all_sign_pred`) -/

namespace groupInfoTbs public abbrev signWithLabelPred := groupInfoSignPred end groupInfoTbs
namespace keyPackageTbs public abbrev signWithLabelPred := keyPackageSignPred end keyPackageTbs
namespace leafNodeTbs public abbrev signWithLabelPred := leafNodeSignPred TreeKEM.tkt end leafNodeTbs

#combine +toplevel into SignWithLabelPred from groupInfoTbs, keyPackageTbs, leafNodeTbs

#combine +toplevel into SignPred from signWithLabelPred

/-! ### MAC predicate (port of `all_mac_pred`) -/

namespace confirmationMac public abbrev macPred := confirmationMacPred end confirmationMac

#combine +toplevel into MacPred from confirmationMac

/-! ## Bytes invariants -/

#combine +toplevel into BytesInvariants from
  DY.Random,
  DY.Literal,
  DY.Concat,
  DY.Hash,
  DySlop.KdfExtract,
  DySlop.KdfExpand,
  DySlop.Kem,
  DySlop.Signature,
  DySlop.Aead,
  DySlop.Mac

/-! ### The crypto predicates stay true when the trace grows -/

namespace groupInfoTbs public theorem signWithLabelPredProof: SignWithLabelPred.LocalProof signWithLabelPred := groupInfoSignPredProof end groupInfoTbs
namespace keyPackageTbs public theorem signWithLabelPredProof: SignWithLabelPred.LocalProof signWithLabelPred := keyPackageSignPredProof end keyPackageTbs
namespace leafNodeTbs public theorem signWithLabelPredProof: SignWithLabelPred.LocalProof signWithLabelPred := leafNodeSignPredProof TreeKEM.tkt end leafNodeTbs

#combine +toplevel into SignWithLabelPredProof from groupInfoTbs, keyPackageTbs, leafNodeTbs

#combine +toplevel into SignPredProof from signWithLabelPred

namespace welcomeHpke public theorem encryptWithLabelPredProof: EncryptWithLabelPred.LocalProof encryptWithLabelPred := mlsHpkeWelcomePredProof end welcomeHpke
namespace updatePathNodeHpke public theorem encryptWithLabelPredProof: EncryptWithLabelPred.LocalProof encryptWithLabelPred := mlsHpkeUpdatepathnodePredProof end updatePathNodeHpke

namespace initHpkeKey
#combine +toplevel into EncryptWithLabelPredProof from welcomeHpke
public theorem hpkePredProof: HpkePred.LocalProof hpkePred := EncryptWithLabelPred.LocalProof.toHpkePred _ encryptWithLabelPredProof
end initHpkeKey

namespace nodeHpkeKey
#combine +toplevel into EncryptWithLabelPredProof from updatePathNodeHpke
public theorem hpkePredProof: HpkePred.LocalProof hpkePred := EncryptWithLabelPred.LocalProof.toHpkePred _ encryptWithLabelPredProof
end nodeHpkeKey

#combine +toplevel into HpkePredProof from initHpkeKey, nodeHpkeKey

namespace welcomeAead public theorem aeadPredProof: AeadPred.LocalProof aeadPred := aeadGroupInfoPredProof end welcomeAead

#combine +toplevel into AeadPredProof from DySlop.HPKE, welcomeAead

namespace confirmationMac public theorem macPredProof: MacPred.LocalProof macPred := confirmationMacPredProof end confirmationMac

#combine +toplevel into MacPredProof from confirmationMac

#combine +toplevel into BytesInvariantsProofs from
  DY.Random,
  DY.Literal,
  DY.Concat,
  DY.Hash,
  DySlop.KdfExtract,
  DySlop.KdfExpand,
  DySlop.Kem,
  DySlop.Signature,
  DySlop.Aead,
  DySlop.Mac

public instance: HasSymbolicInvariants where

/-! ## Trace invariants -/

/-! ### Event predicates (port of `all_event_pred`) -/

public instance: ProtocolEvent.EventInv (LeafNodeHasBeenVerified TreeKEM.tkt) := ⟨leafNodeHasBeenVerifiedPred⟩
public instance: ProtocolEvent.EventInv (GroupHasTreeEvent TreeKEM.tkt) := ⟨groupHasTreeEventPred⟩
public instance: ProtocolEvent.EventInv IAmInGroup := ⟨iAmInGroupPred⟩
public instance: ProtocolEvent.EventInv KeyPackageHasBeenVerified := ⟨keyPackageHasBeenVerifiedPred⟩
public instance: ProtocolEvent.EventInv (LeafNodeSignedEvent TreeKEM.tkt) := ⟨leafNodeSignedEventPred⟩

public instance: ProtocolEvent.EventInv.Has (leafNodeHasBeenVerifiedPred (tkt := TreeKEM.tkt)) := ⟨fun _ _ => rfl⟩
public instance: ProtocolEvent.EventInv.Has groupHasTreeEventPred := ⟨fun _ _ => rfl⟩
public instance: ProtocolEvent.EventInv.Has iAmInGroupPred := ⟨fun _ _ => rfl⟩
public instance: ProtocolEvent.EventInv.Has keyPackageHasBeenVerifiedPred := ⟨fun _ _ => rfl⟩
public instance: ProtocolEvent.EventInv.Has leafNodeSignedEventPred := ⟨fun _ _ => rfl⟩

/-! ### Trace invariant (port of `all_local_state_pred` and `treesync_treekem_trace_invariants`) -/

-- The state predicates are the instances `CompromisableLocalStateInv X` (e.g. `treeSyncSignatureKeyStateInv`).
#combine +toplevel into SubTraceInvariant from
  Network,
  DY.Random,
  CompromisableState TreeSyncSignatureKeyState,
  CompromisableState (TreeSyncPublicState TreeKEM.tkt),
  CompromisableState (Map AsCacheKey AsCacheValue),
  CompromisableState (Map GroupManagerKey GroupManagerValue),
  CompromisableState (Map (KeyPackage Bytes TreeKEM.tkt) KeyPackageManagerValue),
  ProtocolEvent (LeafNodeSignedEvent TreeKEM.tkt),
  ProtocolEvent (GroupHasTreeEvent TreeKEM.tkt),
  CompromisableState TreeKEMNodeKeysState,
  CompromisableState TreeKEMEpochSecret,
  CompromisableState BareTreeSyncTreeKEMState,
  CompromisableState OnePskState,
  CompromisableState (Map PskStoreKey PskStoreValue),
  CompromisableState (Map ProposalCacheKey ProposalAndSender),
  CompromisableState (Map UpdateCacheKey UpdateCacheValue),
  CompromisableState BootstrapInitKeyState,
  CompromisableState KeyPackageStorePre,
  ProtocolEvent IAmInGroup,
  ProtocolEvent KeyPackageHasBeenVerified,
  ProtocolEvent (LeafNodeHasBeenVerified TreeKEM.tkt)

/-! ## Bundles of invariants (port of `treesync_treekem_protocol_invariants_correct`) -/

public instance: HasMlsPskInvariants where
public instance: HasMlsKeyscheduleInvariants where
public instance: HasKeyPackageInvariant where
public instance: HasTreesyncTreekemLinkInvariants where
public instance: HasBootstrapCryptoInvariants where
public instance: HasIAmInGroupInvariant where
public instance: HasMlsTreekemInvariants where
public instance: HasTreesyncInvariants TreeKEM.tkt where
public instance: HasTreeKEMProofTrace where

-- `has_group_info_tbs_invariant`
example: SignWithLabelPred.Has groupInfoSignPred := inferInstance

end MLS.TreeKEM.ProtocolInvariants
