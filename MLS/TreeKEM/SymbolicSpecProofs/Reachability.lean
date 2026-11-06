module

public import MLS.TreeKEM.SymbolicSpec.Reachability
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProtocolInvariants
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.CreateGroup
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.GenerateKeyPackage
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.GenerateUpdateProposal
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessProposal
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.GenerateCommitWelcome
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessCommit
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessWelcome
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeSync.SymbolicProofs.State.AuthServiceCache
public import MLS.Bootstrap.SymbolicProofs.State.KeyPackageStore
public import MLS.TreeKEM.SymbolicProofs.State.ProposalCache
public import MLS.TreeKEM.SymbolicProofs.State.UpdateCache
public import MLS.TreeKEM.SymbolicProofs.State.PSKStore
public import DY.Trace.ReachabilityTheorem
public meta import DY.Meta.CombineMacro

/-!
Reachable traces satisfy the trace invariant (not in MLS*, see `MLS.TreeKEM.SymbolicSpec.Reachability`):
every action of the reachability configuration `MLS.TreeKEM.reachability` preserves the trace invariant,
by the Hoare triples of the traceful functions (`createGroup.proof`, …).
Hence `Trace.Reachable_implies_Invariant MLS.TreeKEM.reachability` turns the security theorem
(stated on proof traces satisfying the invariant) into a theorem on reachable execution traces.

As the security theorem, it is stated on the top-level instances (`ProtocolInvariants.lean`).
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.Map (Map)

section ReachabilityImpliesInvariant

public instance: ReachableImpliesInvariant mkSignatureKey.reachability :=
  .mk (fun me => mkSignatureKey.proof me)
public instance: ReachableImpliesInvariant initializeAsCache.reachability :=
  .mk (fun me => initializeAsCache.proof me)
public instance: ReachableImpliesInvariant initializeKeyPackageStore.reachability :=
  .mk (fun me => initializeKeyPackageStore.proof me)
public instance: ReachableImpliesInvariant initializeProposalCache.reachability :=
  .mk (fun me => initializeProposalCache.proof me)
public instance: ReachableImpliesInvariant initializeUpdateCache.reachability :=
  .mk (fun me => initializeUpdateCache.proof me)
public instance: ReachableImpliesInvariant initializePskStore.reachability :=
  .mk (fun me => initializePskStore.proof me)
public instance: ReachableImpliesInvariant verifyCredential.reachability :=
  .mk (fun (me, authServiceSid, who, whoSignatureKeySid) => verifyCredential.proof me authServiceSid who whoSignatureKeySid)
public instance: ReachableImpliesInvariant createGroup.reachability :=
  .mk (fun (me, mySignatureKeySid, authServiceSid, leafNodeSkeletonTs) =>
    createGroup.proof me mySignatureKeySid authServiceSid leafNodeSkeletonTs)
public instance: ReachableImpliesInvariant generateKeyPackage.reachability :=
  .mk (fun (me, keyPackageSkeletonTs, signatureKeySid, keyPackageStoreSid) =>
    generateKeyPackage.proof me keyPackageSkeletonTs signatureKeySid keyPackageStoreSid)
public instance: ReachableImpliesInvariant generateUpdateProposal.reachability :=
  .mk (fun (me, updateCacheSid, groupStateSid, leafNodeSkeletonTs, signatureKeySid) =>
    generateUpdateProposal.proof me updateCacheSid groupStateSid leafNodeSkeletonTs signatureKeySid)
public instance: ReachableImpliesInvariant processProposal.reachability :=
  .mk (fun (me, proposalCacheSid, proposalTs, sender) => processProposal.proof me proposalCacheSid proposalTs sender)
public instance: ReachableImpliesInvariant createCommitAndWelcome.reachability :=
  .mk (fun (me, authServiceSid, proposalCacheSid, updateCacheSid, pskStoreSid, groupStateSid, messageSkeletonTs) =>
    createCommitAndWelcome.proof me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid
      messageSkeletonTs)
public instance: ReachableImpliesInvariant processCommit.reachability :=
  .mk (fun (me, authServiceSid, proposalCacheSid, updateCacheSid, pskStoreSid, groupStateSid, commitTs) =>
    processCommit.proof me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid commitTs)
public instance: ReachableImpliesInvariant processWelcome.reachability :=
  .mk (fun (me, keyPackageStoreSid, authServiceSid, pskStoreSid, welcomeTs, ratchetTreeTs) =>
    processWelcome.proof me keyPackageStoreSid authServiceSid pskStoreSid welcomeTs ratchetTreeTs)

public instance (StateT: Type) [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT StateT)]
  [ProofTraceTypes.Has (PersistentLocalState.CompromisableState.ProofEntryT StateT)]
  [PersistentLocalState.CompromisableLocalStateInv StateT]
  [TraceInvariant.Has (PersistentLocalState.CompromisableState.ProofEntryT StateT)]:
  ReachableImpliesInvariant (compromiseState.reachability StateT) :=
  .mk (fun handle => PersistentLocalState.compromise.proof handle)

#combine into ReachabilityTheorem from
  Network,
  mkSignatureKey,
  initializeAsCache,
  initializeKeyPackageStore,
  initializeProposalCache,
  initializeUpdateCache,
  initializePskStore,
  verifyCredential,
  createGroup,
  generateKeyPackage,
  generateUpdateProposal,
  processProposal,
  createCommitAndWelcome,
  processCommit,
  processWelcome,
  compromiseState TreeSyncSignatureKeyState,
  compromiseState (TreeSyncPublicState tkt),
  compromiseState (Map AsCacheKey AsCacheValue),
  compromiseState (Map GroupManagerKey GroupManagerValue),
  compromiseState (Map (KeyPackage Bytes tkt) KeyPackageManagerValue),
  compromiseState TreeKEMNodeKeysState,
  compromiseState TreeKEMEpochSecret,
  compromiseState BareTreeSyncTreeKEMState,
  compromiseState OnePskState,
  compromiseState (Map PskStoreKey PskStoreValue),
  compromiseState (Map ProposalCacheKey ProposalAndSender),
  compromiseState (Map UpdateCacheKey UpdateCacheValue),
  compromiseState BootstrapInitKeyState,
  compromiseState KeyPackageStorePre

end ReachabilityImpliesInvariant

end MLS.TreeKEM
