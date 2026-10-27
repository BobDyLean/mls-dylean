module

public import MLS.TreeKEM.SymbolicSpec.EpochEvent
public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeKEM.SymbolicProofs.API.KeySchedule
public import MLS.TreeKEM.SymbolicProofs.Tree.Labels
public import MLS.TreeKEM.SymbolicProofs.PSK
public import MLS.TreeSync.Proofs.API.LeafAt
import all MLS.TreeKEM.SymbolicSpec.EpochEvent

/-!
Port of the event predicate of `MLS.TreeKEM.Symbolic.EpochEvent`, and lemmas about its predicates on traces.

Port-specific differences:
- `IHavePreviousEpochEvent_le` is not in MLS* (DY*'s SMT patterns on `event_triggered` give it).
- The principal who triggered the event is its field `prin` (MLS*'s `me`), and events are on `tr.erase`.
- MLS*'s `Some? (leaf_at …)` and `Some?.v` are existentials (`∃ ln, leafAt … = some ln ∧ …`).
  In `JustJoined`, MLS*'s `inviter < pow2 ev.tree_height` is dropped: it follows from `leafAt ev.tree inviter = some _`.
- MLS*'s `has_i_am_in_group_invariant` is the class `HasIAmInGroupInvariant`, whose fields are scoped instances
  in `MLS.TreeKEM`. MLS*'s `has_treekem_invariants` is not a class: it is
  `[HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant]`, which contain the predicates
  of the three events (`has_key_package_has_been_verified_invariant`, `has_leaf_node_has_been_verified_invariant`,
  `has_i_am_in_group_invariant`), so that the event instances are not duplicated in several bundles.
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync

section Lemmas

variable [HasSymbolicBytes] [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]

/-- The previous epoch event is still logged when the trace grows. -/
public
theorem IHavePreviousEpochEvent_le {previousTreeHeight: Nat} (tr1 tr2: ExecTrace) (me: Participant)
  (previousGroupContext: GroupContext Bytes) (previousInitSecret: Bytes) (previousTree: TreeSync Bytes tkt previousTreeHeight)
  : tr1 ≤ tr2 →
    IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree →
    IHavePreviousEpochEvent tr2 me previousGroupContext previousInitSecret previousTree
:= by
  intro hle ⟨previousEv, h⟩
  refine ⟨previousEv, ?_⟩
  grind [IHavePreviousEpochEventWithWitness]

grind_pattern IHavePreviousEpochEvent_le =>
  tr1 ≤ tr2,
  IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree
grind_pattern [grind_later] IHavePreviousEpochEvent_le =>
  tr1 ≤ tr2,
  IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree

end Lemmas

section EventPredicate

open MLS.TreeSync.API (treeAddOnlyRel)
open MLS.Bootstrap (IHaveVerifiedEveryKeyPackage)
open MLS.TreeKEM.Symbolic.API.KeySchedule (TreekemKeyscheduleStateGood TreekemKeyscheduleStateLabelGoodAux TreekemKeyscheduleStateLabelGood)

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `i_am_in_group_pred`. -/
@[expose]
public
def iAmInGroupPred (tr: ProofTrace) (ev: IAmInGroup): Prop :=
  TreeHasHash ev.tree ev.groupContext.treeHash.val ∧
  IHaveVerifiedEveryLeafNode tr.erase ev.prin ev.tree ev.groupContext.groupId ∧
  match ev.how with
  | .justCreated =>
    ev.groupContext.epoch = 0 ∧
    ev.treeHeight = 0 ∧
    (∃ ln, leafAt ev.tree 0 = some ln ∧ credentialToPrincipal ln.data.credential = some ev.prin) ∧
    TreekemKeyscheduleStateGood tr ev.epochKeys ev.groupContext ∧
    TreekemKeyscheduleStateLabelGoodAux tr Label.secret ev.epochKeys ev.groupContext
  | .justJoined { inviter } =>
    ∃ inviterLeafNode inviterId,
      leafAt ev.tree inviter = some inviterLeafNode ∧
      credentialToPrincipal inviterLeafNode.data.credential = some inviterId ∧ (
        (signatureKeyLabel inviterId inviterLeafNode.data.signatureKey.val).isCorrupt tr.erase ∨
        InviterHasSameEventAsMe tr.erase inviterId ev.groupContext ev.psks ev.epochKeys
      )
  | .processedCommit lastEpochLink =>
    lastEpochLink.previousInitSecret.Invariant tr ∧
    lastEpochLink.previousGroupContext.groupId = ev.groupContext.groupId ∧
    lastEpochLink.previousGroupContext.epoch + 1 = ev.groupContext.epoch ∧
    (lastEpochLink.commitTy = .addOnlyCommit → treeAddOnlyRel lastEpochLink.previousTree ev.tree) ∧
    PsksBytesInvariant tr ev.psks ∧
    IHaveVerifiedEveryKeyPackage tr.erase ev.prin lastEpochLink.joiners ∧
    IHavePreviousEpochEvent tr.erase ev.prin
      lastEpochLink.previousGroupContext lastEpochLink.previousInitSecret lastEpochLink.previousTree ∧
    let commitSecretLabel :=
      match lastEpochLink.commitTy with
      | .addOnlyCommit => Label.pub
      | .fullCommit => nodeSkLabel ev.tree ev.groupContext.groupId
    TreekemKeyscheduleStateGood tr ev.epochKeys ev.groupContext ∧
    TreekemKeyscheduleStateLabelGood tr lastEpochLink.previousInitSecret commitSecretLabel
      lastEpochLink.joiners ev.psks ev.epochKeys ev.groupContext

/--
Port of `has_i_am_in_group_invariant`: the event predicate of `IAmInGroup` is in the protocol invariants.
The fields are scoped instances in the namespace `MLS.TreeKEM`; the top-level protocol provides them
(`instance: HasIAmInGroupInvariant where`).
-/
public
class HasIAmInGroupInvariant [TraceInvariant] where
  [proofTrace0: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT IAmInGroup)]
  [eventInv0: ProtocolEvent.EventInv IAmInGroup]
  [traceInv0: TraceInvariant.Has (ProtocolEvent.ProofEntryT IAmInGroup)]
  [eventPred0: ProtocolEvent.EventInv.Has iAmInGroupPred]

attribute [reducible, scoped instance] HasIAmInGroupInvariant.proofTrace0
attribute [scoped instance] HasIAmInGroupInvariant.traceInv0
attribute [reducible, scoped instance] HasIAmInGroupInvariant.eventInv0
attribute [scoped instance] HasIAmInGroupInvariant.eventPred0

end EventPredicate

end MLS.TreeKEM
