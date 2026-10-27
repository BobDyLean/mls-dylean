module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeSync.SymbolicProofs.API
public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.Bootstrap.SymbolicProofs.State.KeyPackageStore
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.GroupInfo
public import MLS.Bootstrap.SymbolicProofs.Welcome
public import MLS.TreeKEM.SymbolicProofs.State.API
public import MLS.TreeKEM.SymbolicProofs.State.NodeKey
public import MLS.TreeKEM.SymbolicProofs.State.EpochSecrets
public import MLS.TreeKEM.SymbolicProofs.State.OnePSKStore
public import MLS.TreeKEM.SymbolicProofs.State.PSKStore
public import MLS.TreeKEM.SymbolicProofs.State.ProposalCache
public import MLS.TreeKEM.SymbolicProofs.State.UpdateCache
public import MLS.TreeKEM.SymbolicProofs.Tree.Labels
public import MLS.TreeKEM.SymbolicProofs.Tree.Operations
public import MLS.TreeKEM.SymbolicProofs.EpochEvent
public import MLS.TreeKEM.SymbolicProofs.KeySchedule
public import MLS.TreeKEM.SymbolicProofs.PSK

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.AllInvariants`: the invariants assumed by the proofs of the traceful functions
of TreeKEM (`MLS.TreeKEM.SymbolicSpecProofs.Traceful.*`).

Port-specific differences:
- MLS*'s `has_treesync_and_treekem_invariants` is not a class: it conjoins invariants already bundled elsewhere,
  so the proofs assume these bundles:
  `[HasTreesyncInvariants TreeKEM.tkt]` (`has_treesync_invariants tkt`),
  `[HasKeyPackageInvariant]`, `[HasTreesyncTreekemLinkInvariants]`, `[HasIAmInGroupInvariant]`,
  `[HasBootstrapCryptoInvariants]` (which contains `has_mls_keyschedule_invariants`),
  `[HasMlsTreekemInvariants]`, `[HasMlsPskInvariants]`, `[SignWithLabelPred.Has groupInfoSignPred]`
  (`has_group_info_tbs_invariant`), and `[HasTreeKEMProofTrace]` below.
- The state invariants (`has_bootstrap_init_key_state_invariant`, …, `has_psk_store_invariant`) are DyLean state
  invariants (instances): what the proofs need are the proof trace entries of the states,
  bundled in `HasTreeKEMProofTrace` (with the one of the network), as the execution ones in `HasTreeKEMExecTrace`.
-/

namespace MLS.TreeKEM

open DY DY.PersistentLocalState
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.Map (Map)

/--
The proof trace entries of the states used by the traceful functions of TreeKEM (and of the network),
i.e. MLS*'s `has_*_state_invariant` conjuncts of `has_treesync_and_treekem_invariants`
(the entries of the events are in the bundles of their invariants, e.g. `HasIAmInGroupInvariant`).
The fields are scoped instances in the namespace `MLS.TreeKEM`; the top-level protocol provides them
(`instance: HasTreeKEMProofTrace where`).
-/
public
class HasTreeKEMProofTrace [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace] where
  [proofTrace0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [proofTrace1: ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]
  [traceInv1: TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]
  [proofTrace2: ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]
  [traceInv2: TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]
  [proofTrace3: ProofTraceTypes.Has (CompromisableState.ProofEntryT BareTreeSyncTreeKEMState)]
  [traceInv3: TraceInvariant.Has (CompromisableState.ProofEntryT BareTreeSyncTreeKEMState)]
  [proofTrace4: ProofTraceTypes.Has (CompromisableState.ProofEntryT OnePskState)]
  [traceInv4: TraceInvariant.Has (CompromisableState.ProofEntryT OnePskState)]
  [proofTrace5: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map PskStoreKey PskStoreValue))]
  [traceInv5: TraceInvariant.Has (CompromisableState.ProofEntryT (Map PskStoreKey PskStoreValue))]
  [proofTrace6: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map ProposalCacheKey ProposalAndSender))]
  [traceInv6: TraceInvariant.Has (CompromisableState.ProofEntryT (Map ProposalCacheKey ProposalAndSender))]
  [proofTrace7: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map UpdateCacheKey UpdateCacheValue))]
  [traceInv7: TraceInvariant.Has (CompromisableState.ProofEntryT (Map UpdateCacheKey UpdateCacheValue))]
  [proofTrace8: ProofTraceTypes.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]
  [traceInv8: TraceInvariant.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]
  [proofTrace9: ProofTraceTypes.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]
  [traceInv9: TraceInvariant.Has (CompromisableState.ProofEntryT KeyPackageStorePre)]

attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace0
attribute [scoped instance] HasTreeKEMProofTrace.traceInv0
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace1
attribute [scoped instance] HasTreeKEMProofTrace.traceInv1
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace2
attribute [scoped instance] HasTreeKEMProofTrace.traceInv2
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace3
attribute [scoped instance] HasTreeKEMProofTrace.traceInv3
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace4
attribute [scoped instance] HasTreeKEMProofTrace.traceInv4
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace5
attribute [scoped instance] HasTreeKEMProofTrace.traceInv5
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace6
attribute [scoped instance] HasTreeKEMProofTrace.traceInv6
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace7
attribute [scoped instance] HasTreeKEMProofTrace.traceInv7
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace8
attribute [scoped instance] HasTreeKEMProofTrace.traceInv8
attribute [reducible, scoped instance] HasTreeKEMProofTrace.proofTrace9
attribute [scoped instance] HasTreeKEMProofTrace.traceInv9

end MLS.TreeKEM
