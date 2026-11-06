module

public import MLS.TreeKEM.SymbolicSpec.Traceful.CreateGroup
public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateKeyPackage
public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateUpdateProposal
public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessProposal
public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateCommitWelcome
public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessCommit
public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessWelcome
public import DY.Trace.Reachability
public meta import DY.Meta.CombineMacro

/-!
The reachability configuration of TreeKEM (not in MLS*, which states its security theorem on traces
satisfying the trace invariant): the actions that the attacker can trigger.

- The network: the attacker sends any message it knows (`Network`).
- The honest participants: they create their signature key (`mkSignatureKey`) and initialize their states
  (`initializeAsCache`, `initializeKeyPackageStore`, `initializeProposalCache`, `initializeUpdateCache`,
  `initializePskStore`), verify credentials (`MLS.TreeSync.verifyCredential`), and run the traceful functions of TreeKEM
  (`createGroup`, `generateKeyPackage`, `generateUpdateProposal`, `processProposal`, `createCommitAndWelcome`,
  `processCommit`, `processWelcome`). Their arguments (principal, handles of states and messages) are chosen
  by the attacker.
- The compromise of every state type of TreeSync and TreeKEM (`compromiseState`).

The other functions of the specifications (e.g. the TreeSync API, `storePsk`) are only called by these functions.
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.Map (Map)

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Reachability configuration -/

section Reachability

variable [BaseAttackerKnowledge] [AttackerKnowledge]

-- The reachability configurations are exposed, as in DyLean's examples:
-- `#combine` compiles them into the `ReachabilityConfig` instance, and
-- the proofs that reachable traces satisfy the invariant unfold them.
@[expose] public section

def mkSignatureKey.reachability: ReachabilityConfig :=
  .make (fun me => mkSignatureKey me)
def initializeAsCache.reachability: ReachabilityConfig :=
  .make (fun me => initializeAsCache me)
def initializeKeyPackageStore.reachability: ReachabilityConfig :=
  .make (fun me => initializeKeyPackageStore me)
def initializeProposalCache.reachability: ReachabilityConfig :=
  .make (fun me => initializeProposalCache me)
def initializeUpdateCache.reachability: ReachabilityConfig :=
  .make (fun me => initializeUpdateCache me)
def initializePskStore.reachability: ReachabilityConfig :=
  .make (fun me => initializePskStore me)
def verifyCredential.reachability: ReachabilityConfig :=
  .make (fun (me, authServiceSid, who, whoSignatureKeySid) => verifyCredential me authServiceSid who whoSignatureKeySid)
def createGroup.reachability: ReachabilityConfig :=
  .make (fun (me, mySignatureKeySid, authServiceSid, leafNodeSkeletonTs) =>
    createGroup me mySignatureKeySid authServiceSid leafNodeSkeletonTs)
def generateKeyPackage.reachability: ReachabilityConfig :=
  .make (fun (me, keyPackageSkeletonTs, signatureKeySid, keyPackageStoreSid) =>
    generateKeyPackage me keyPackageSkeletonTs signatureKeySid keyPackageStoreSid)
def generateUpdateProposal.reachability: ReachabilityConfig :=
  .make (fun (me, updateCacheSid, groupStateSid, leafNodeSkeletonTs, signatureKeySid) =>
    generateUpdateProposal me updateCacheSid groupStateSid leafNodeSkeletonTs signatureKeySid)
def processProposal.reachability: ReachabilityConfig :=
  .make (fun (me, proposalCacheSid, proposalTs, sender) => processProposal me proposalCacheSid proposalTs sender)
def createCommitAndWelcome.reachability: ReachabilityConfig :=
  .make (fun (me, authServiceSid, proposalCacheSid, updateCacheSid, pskStoreSid, groupStateSid, messageSkeletonTs) =>
    createCommitAndWelcome me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid messageSkeletonTs)
def processCommit.reachability: ReachabilityConfig :=
  .make (fun (me, authServiceSid, proposalCacheSid, updateCacheSid, pskStoreSid, groupStateSid, commitTs) =>
    processCommit me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid commitTs)
def processWelcome.reachability: ReachabilityConfig :=
  .make (fun (me, keyPackageStoreSid, authServiceSid, pskStoreSid, welcomeTs, ratchetTreeTs) =>
    processWelcome me keyPackageStoreSid authServiceSid pskStoreSid welcomeTs ratchetTreeTs)

/-- The attacker compromises a state of type `StateT` (given its handle). -/
def compromiseState.reachability (StateT: Type) [Comparse.ParseableSerializeable StateT]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT StateT)]: ReachabilityConfig :=
  .make (fun handle => PersistentLocalState.compromise StateT handle)

end

#combine into ReachabilityConfig from
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

end Reachability

end MLS.TreeKEM
