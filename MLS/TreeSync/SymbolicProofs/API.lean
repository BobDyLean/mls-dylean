module

public import MLS.TreeSync.SymbolicSpec.API
public import MLS.TreeSync.Proofs.ParentHashGuarantees
public import MLS.TreeSync.SymbolicProofs.State.AuthServiceCache
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.Symbolic.SymbolicProofs.Symbolic
public import DySlop.Lib.Event
public import MLS.TreeSync.SymbolicProofs.State.Tree
public import MLS.TreeSync.SymbolicProofs.State.GroupManager
public import MLS.TreeSync.SymbolicProofs.State.KeyPackageManager
import all MLS.TreeSync.SymbolicSpec.API
import all MLS.TreeSync.SymbolicSpec.LeafNodeSignature
import DY.Meta.Step

/-!
Port of the predicates of `MLS.TreeSync.Symbolic.API`: the preconditions of the functions triggering events.

Port-specific differences:
- The namespace is `MLS.TreeSync.Symbolic.API` (MLS*'s module name), as in `MLS.TreeSync.SymbolicSpec.API`.
- DY*'s event predicates (`event_predicate`) take the principal in the event:
  they are functions `ProofTrace → Event → Prop`, as DyLean's event invariants.
- MLS*'s `match`es on results are hypotheses (`… = .success authP → …`).
- MLS*'s `has_treesync_invariants` is the class `HasTreesyncInvariants tkt`, whose fields (the proof trace entries
  of the states of TreeSync and of randomness, and the signature predicate of leaf nodes) are scoped instances
  in `MLS.TreeSync`, for the users of TreeSync (e.g. the traceful functions of TreeKEM).
  The proofs of this file assume the individual instances they need.
- The proofs of the traceful functions are DyLean Hoare triples (instances).
  MLS*'s event predicates given as arguments (`leaf_node_has_event_pred`, …) are the event invariants of the protocol
  (`ProtocolEvent.EventInv.invariant`, the precondition of DyLean's `logEvent.proof`), since a Hoare triple instance
  cannot find them: callers rewrite them with `ProtocolEvent.EventInv.Has.invariant_eq`
  (or `ProtocolEvent.EventInv.Has.invariant_eq_fun`).
- The `tr_out == tr` parts of the postconditions are not ported.
-/

namespace MLS.TreeSync.Symbolic.API

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}

/-- Port of `tree_event_pre`. -/
@[expose]
public
def TreeEventPre (tr: ProofTrace) (groupHasEventPred: ProofTrace → GroupHasTreeEvent tkt → Prop) (p: Participant)
  (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTreeSync Bytes tkt): Prop :=
  ∀ tr', tr ≤ tr' → groupHasEventPred tr' (mkGroupHasTreeEvent p groupId authentifierLeafIndex t)

/-- `tree_event_pre` stays true when the trace grows (MLS* uses `forall tr'`). -/
public
theorem TreeEventPre_later (tr1 tr2: ProofTrace) (groupHasEventPred: ProofTrace → GroupHasTreeEvent tkt → Prop)
  (p: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTreeSync Bytes tkt)
  : tr1 ≤ tr2 →
    TreeEventPre tr1 groupHasEventPred p groupId authentifierLeafIndex t →
    TreeEventPre tr2 groupHasEventPred p groupId authentifierLeafIndex t
:= by
  grind [TreeEventPre, Trace.le_trans]

grind_pattern TreeEventPre_later => tr1 ≤ tr2, TreeEventPre tr1 groupHasEventPred p groupId authentifierLeafIndex t
grind_pattern [grind_later] TreeEventPre_later =>
  tr1 ≤ tr2,
  TreeEventPre tr1 groupHasEventPred p groupId authentifierLeafIndex t

/--
Port of `external_path_has_event_pre`.
MLS*'s leaf index `li` (implicit in the path) is explicit.
-/
@[expose]
public
def ExternalPathHasEventPre {l: Nat}
  (leafNodeHasEventPred: ProofTrace → LeafNodeSignedEvent tkt → Prop)
  (groupHasEventPred: ProofTrace → GroupHasTreeEvent tkt → Prop)
  (tr: ProofTrace) (prin: Participant) (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes): Prop :=
  p.getPathLeaf.source = .update →
  li < 2^32 →
  ∀ authP, externalPathToPathNosig t li p = .success authP →
    let authLn := authP.getPathLeaf
    leafNodeHasEventPred tr
      { prin, lnTbs := { data := authLn.data, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 } } ∧
    PathToTreeListPre (TreeEventPre tr groupHasEventPred prin groupId li) t li authP

section Proofs

variable [TraceInvariant] [HasTreeSyncExecTrace tkt]

/-! ## Utility functions -/

section AuthService

open DySlop.Map (Map MapPred)
open PersistentLocalState

variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]

/-- Port of `get_token_for_proof`. -/
@[instance]
public
theorem getTokenFor.proof (p: Participant) (asSession: Nat) (inp: ASInput Bytes):
  HoareTriple
    (getTokenFor p asSession inp)
    (fun _ => True)
    (fun token tr => (dyAsp tr).credentialOk inp token)
:= by
  unfold getTokenFor
  dsimp only
  step
  step
  simp only [MapPred.pred] at *
  grind

omit [TraceInvariant] [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]
  [TraceInvariant.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))] in
/-- The tokens stay valid when the trace grows. -/
public
theorem TokensForAsInputs_dyAsp_later (tr1 tr2: ProofTrace) (inps: List (Option (ASInput Bytes)))
  (tokens: List (Option DyAsToken)):
  tr1 ≤ tr2 →
  TreeSync.API.TokensForAsInputs (dyAsp tr1) inps tokens →
  TreeSync.API.TokensForAsInputs (dyAsp tr2) inps tokens
:= by
  intro hle h li hli
  have := h li hli
  split at this <;> grind

grind_pattern TokensForAsInputs_dyAsp_later => tr1 ≤ tr2, TreeSync.API.TokensForAsInputs (dyAsp tr1) inps tokens
grind_pattern [grind_later] TokensForAsInputs_dyAsp_later => tr1 ≤ tr2, TreeSync.API.TokensForAsInputs (dyAsp tr1) inps tokens

/--
Port of `get_tokens_for_proof`.
The `tr_out == tr` part of the postcondition is not ported.
-/
@[instance]
public
theorem getTokensFor.proof (p: Participant) (asSession: Nat) (inps: List (Option (ASInput Bytes))):
  HoareTriple
    (getTokensFor p asSession inps)
    (fun _ => True)
    (fun tokens tr => tokens.length = inps.length ∧ TreeSync.API.TokensForAsInputs (dyAsp tr) inps tokens)
:= by
  induction inps with
  | nil =>
    unfold getTokensFor
    step
    subst_vars
    simp [TreeSync.API.TokensForAsInputs]
  | cons inp inps ih =>
    unfold getTokensFor
    dsimp -proj -iota only
    split
    · step
      step
      step
      step
      subst_vars
      refine ⟨by simpa using ‹_ = inps.length›, ?_⟩
      intro li hli
      cases li with
      | zero => simpa using ‹(dyAsp tr).credentialOk _ _›
      | succ li => simpa using ‹TreeSync.API.TokensForAsInputs _ inps _› li (by simpa using hli)
    · step
      step
      step
      subst_vars
      refine ⟨by simpa using ‹_ = inps.length›, ?_⟩
      intro li hli
      cases li with
      | zero => simp
      | succ li => simpa using ‹TreeSync.API.TokensForAsInputs _ inps _› li (by simpa using hli)

end AuthService

/-! ## Sign stuff -/

section Sign

open PersistentLocalState

variable [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
variable [BytesInvariants.Has DY.Random.invariants]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
variable [SignWithLabelPred.Has (leafNodeSignPred tkt)]

/--
Port of `authenticate_leaf_node_data_from_key_package_proof`.
MLS*'s `group_id = ()` and `leaf_index = ()` are `StaticOption.mk MlsBytes.empty` and `StaticOption.mk 0`.
-/
@[instance]
public
theorem authenticateLeafNodeDataFromKeyPackage.proof (p: Participant) (siPrivate: Nat) (lnData: LeafNodeData Bytes tkt):
  HoareTriple
    (authenticateLeafNodeDataFromKeyPackage p siPrivate lnData)
    (fun tr =>
      (LeafNodeData.mf tkt).wf (Bytes.Publishable · tr) lnData ∧
      LeafNodeHasEvent p tr.erase { data := lnData, groupId := StaticOption.mk MlsBytes.empty, leafIndex := StaticOption.mk 0 }
    )
    (fun ln tr =>
      (LeafNode.mf tkt).wf (Bytes.Publishable · tr) ln ∧
      ln.data = lnData
    )
:= by
  unfold authenticateLeafNodeDataFromKeyPackage
  step with ⟨ fun _ => Label.secret, Usage.sigNonce ⟩
  step
  step
  step
  constructor
  · apply signLeafNodeDataKeyPackage_wf p Label.pub tr lnData signatureKey signatureNonce <;> grind
  · revert ‹signLeafNodeDataKeyPackage lnData signatureKey signatureNonce = .success x›
    unfold signLeafNodeDataKeyPackage
    split
    · simp [Result.internalFailure]
    · simp only [Result.bind_eq_success, Result.pure_eq_success]
      grind

/-- Port of `authenticate_leaf_node_data_from_update_proof`. -/
@[instance]
public
theorem authenticateLeafNodeDataFromUpdate.proof (p: Participant) (siPrivate: Nat)
  (lnData: LeafNodeData Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: UInt32):
  HoareTriple
    (authenticateLeafNodeDataFromUpdate p siPrivate lnData groupId leafIndex)
    (fun tr =>
      (LeafNodeData.mf tkt).wf (Bytes.Publishable · tr) lnData ∧
      groupId.val.Publishable tr ∧
      LeafNodeHasEvent p tr.erase { data := lnData, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk leafIndex } ∧
      TreeHasEvent p tr.erase groupId leafIndex.toNat
        ⟨0, (ChildSiblingView.leaf (some { data := lnData, signature := MlsBytes.empty }) leafIndex.toNat).pack⟩
    )
    (fun ln tr =>
      (LeafNode.mf tkt).wf (Bytes.Publishable · tr) ln ∧
      ln.data = lnData
    )
:= by
  unfold authenticateLeafNodeDataFromUpdate
  step with ⟨ fun _ => Label.secret, Usage.sigNonce ⟩
  step
  step
  step
  constructor
  · apply signLeafNodeDataUpdate_wf p Label.pub tr lnData groupId leafIndex signatureKey signatureNonce <;> grind
  · revert ‹signLeafNodeDataUpdate lnData groupId leafIndex signatureKey signatureNonce = .success x›
    unfold signLeafNodeDataUpdate
    split
    · simp [Result.internalFailure]
    · simp only [Result.bind_eq_success, Result.pure_eq_success]
      grind

end Sign

/-! ## Trigger events -/

section Events

section LeafNode

variable [ProtocolEvent.EventInv (LeafNodeSignedEvent tkt)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]

/-- Port of `trigger_leaf_node_event_proof`. -/
@[instance]
public
theorem triggerLeafNodeEvent.proof (p: Participant) (lnTbs: LeafNodeTBS Bytes tkt):
  HoareTriple
    (triggerLeafNodeEvent p lnTbs)
    (fun tr => ProtocolEvent.EventInv.invariant tr ({ prin := p, lnTbs }: LeafNodeSignedEvent tkt))
    (fun _ tr => LeafNodeHasEvent p tr.erase lnTbs)
:= by
  exact ProtocolEvent.logEvent.proof ({ prin := p, lnTbs }: LeafNodeSignedEvent tkt)

end LeafNode

section Tree

variable [ProtocolEvent.EventInv (GroupHasTreeEvent tkt)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]

/-- Port of `trigger_tree_event_proof`. -/
@[instance]
public
theorem triggerTreeEvent.proof (p: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat)
  (t: OneTreeSync Bytes tkt):
  HoareTriple
    (triggerTreeEvent p groupId authentifierLeafIndex t)
    (fun tr => TreeEventPre tr ProtocolEvent.EventInv.invariant p groupId authentifierLeafIndex t)
    (fun _ tr => TreeHasEvent p tr.erase groupId authentifierLeafIndex t)
:= by
  unfold triggerTreeEvent
  step by
    grind [TreeEventPre]
  exact ‹_›

/-- Port of `trigger_tree_list_event_proof`. -/
@[instance]
public
theorem triggerTreeListEvent.proof (p: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat)
  (tl: TreeSyncList Bytes tkt):
  HoareTriple
    (triggerTreeListEvent p groupId authentifierLeafIndex tl)
    (fun tr => ∀ t ∈ tl, TreeEventPre tr ProtocolEvent.EventInv.invariant p groupId authentifierLeafIndex t)
    (fun _ tr => TreeListHasEvent p tr.erase groupId authentifierLeafIndex tl)
:= by
  induction tl with
  | nil =>
    unfold triggerTreeListEvent
    step
    simp [TreeListHasEvent]
  | cons h t ih =>
    unfold triggerTreeListEvent
    step
    step
    grind [TreeListHasEvent]

end Tree

variable [ProtocolEvent.EventInv (LeafNodeSignedEvent tkt)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
variable [ProtocolEvent.EventInv (GroupHasTreeEvent tkt)]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]

/--
`ExternalPathHasEventPre`, with the event invariants of the protocol, on all the traces extending `tr`:
the precondition of `triggerExternalPathEvents.proof` (not in MLS*).
The event invariants are not monotone in general, and the events are triggered after some (pure) actions:
callers prove it from the monotonicity of their event predicates.
-/
@[expose]
public
def ExternalPathHasEventPreLater {l: Nat} (tr: ProofTrace) (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes): Prop
:=
  ∀ tr', tr ≤ tr' →
    ExternalPathHasEventPre ProtocolEvent.EventInv.invariant ProtocolEvent.EventInv.invariant tr' prin t li p groupId

omit [TraceInvariant] [HasTreeSyncExecTrace tkt] [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
  [TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeSignedEvent tkt))]
  [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))]
  [TraceInvariant.Has (ProtocolEvent.ProofEntryT (GroupHasTreeEvent tkt))] in
/-- `ExternalPathHasEventPreLater` stays true when the trace grows. -/
public
theorem ExternalPathHasEventPreLater_later {l: Nat} (tr1 tr2: ProofTrace) (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes)
  : tr1 ≤ tr2 →
    ExternalPathHasEventPreLater tr1 prin t li p groupId →
    ExternalPathHasEventPreLater tr2 prin t li p groupId
:= by
  grind [ExternalPathHasEventPreLater, Trace.le_trans]

grind_pattern ExternalPathHasEventPreLater_later => tr1 ≤ tr2, ExternalPathHasEventPreLater tr1 prin t li p groupId
grind_pattern [grind_later] ExternalPathHasEventPreLater_later =>
  tr1 ≤ tr2,
  ExternalPathHasEventPreLater tr1 prin t li p groupId

/--
Port of `trigger_external_path_events_proof`.
MLS*'s leaf index `li` (implicit in the path) is explicit.
The precondition is `ExternalPathHasEventPreLater` (MLS*'s `external_path_has_event_pre` on all the later traces).
-/
@[instance]
public
theorem triggerExternalPathEvents.proof {l: Nat} (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes):
  HoareTriple
    (triggerExternalPathEvents prin t li p groupId)
    (fun tr => ExternalPathHasEventPreLater tr prin t li p groupId)
    (fun _ tr => ExternalPathHasEvent prin tr.erase t li p groupId)
:= by
  unfold triggerExternalPathEvents
  step
  step
  step
  step_intro
  step
  have hpre := ‹ExternalPathHasEventPreLater tr prin t li p groupId› tr (Trace.le_refl _)
  obtain ⟨hev, htl⟩ := hpre ‹_› ‹_› authP ‹_›
  clear hpre
  rw [pathToTreeListPre_iff _ t li authP tl ‹_›] at htl
  mark_non_monotone hev
  step
  step
  unfold ExternalPathHasEvent
  grind
end Events

end Proofs

end MLS.TreeSync.Symbolic.API

namespace MLS.TreeSync

open DY
open MLS

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}

/-! ## Invariants -/

section Invariants

open PersistentLocalState
open DySlop.Map (Map)
open MLS.Bootstrap (KeyPackage)

variable (tkt) in
/--
Port of `has_treesync_invariants`: the invariants of the states of TreeSync and of randomness
(their proof trace entries), and the signature predicate of leaf nodes.
The fields are scoped instances in the namespace `MLS.TreeSync`; the top-level protocol provides them
(`instance: HasTreesyncInvariants tkt where`).
-/
public
class HasTreesyncInvariants [TraceInvariant] [HasTreeSyncExecTrace tkt] where
  [proofTrace0: ProofTraceTypes.Has Random.ProofEntryT]
  [traceInv0: TraceInvariant.Has Random.ProofEntryT]
  [bytesInv0: BytesInvariants.Has DY.Random.invariants]
  [proofTrace1: ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
  [traceInv1: TraceInvariant.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
  [proofTrace2: ProofTraceTypes.Has (CompromisableState.ProofEntryT (TreeSyncPublicState tkt))]
  [traceInv2: TraceInvariant.Has (CompromisableState.ProofEntryT (TreeSyncPublicState tkt))]
  [proofTrace3: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]
  [traceInv3: TraceInvariant.Has (CompromisableState.ProofEntryT (Map AsCacheKey AsCacheValue))]
  [proofTrace4: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map GroupManagerKey GroupManagerValue))]
  [traceInv4: TraceInvariant.Has (CompromisableState.ProofEntryT (Map GroupManagerKey GroupManagerValue))]
  [proofTrace5: ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]
  [traceInv5: TraceInvariant.Has (CompromisableState.ProofEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]
  [leafNodeTbs: SignWithLabelPred.Has (leafNodeSignPred tkt)]

attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace0
attribute [scoped instance] HasTreesyncInvariants.traceInv0
attribute [scoped instance] HasTreesyncInvariants.bytesInv0
attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace1
attribute [scoped instance] HasTreesyncInvariants.traceInv1
attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace2
attribute [scoped instance] HasTreesyncInvariants.traceInv2
attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace3
attribute [scoped instance] HasTreesyncInvariants.traceInv3
attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace4
attribute [scoped instance] HasTreesyncInvariants.traceInv4
attribute [reducible, scoped instance] HasTreesyncInvariants.proofTrace5
attribute [scoped instance] HasTreesyncInvariants.traceInv5
attribute [scoped instance] HasTreesyncInvariants.leafNodeTbs

end Invariants

end MLS.TreeSync
