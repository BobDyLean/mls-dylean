module

public import MLS.TreeSync.SymbolicSpec.Event.LeafNodeHasBeenVerified
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.Symbolic.Code.Parsers
public import MLS.TreeSync.Code.Parsers
public import MLS.TreeSync.Proofs.Invariants.ValidLeaves
public import MLS.TreeSync.Proofs.Invariants.AuthService
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
public import DySlop.Lib.Event
import all MLS.TreeSync.SymbolicSpec.Event.LeafNodeHasBeenVerified
import DY.Meta.Step

/-!
Port of the predicate and lemmas of `MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified`:
the invariant of the event logged when a principal verifies a leaf node.

Port-specific differences:
- DY*'s `has_event_pred` is DySlop's `ProtocolEvent.EventInv.Has` (see `DySlop.Lib.Event`).
- The proofs of the traceful functions (`log_leaf_node_verification_event_proof`, …) are DyLean Hoare triples (instances),
  assuming the event invariant (`ProtocolEvent.EventInv.Has leafNodeHasBeenVerifiedPred`) and the proof trace entries of the event.
  The AS tokens (MLS*'s arguments `token` / `tokens`) are existentially quantified in the preconditions,
  as in the event predicate; the tokens of a tree have the same position as the tree (MLS*'s shared index `i`).
-/

namespace MLS.TreeSync

open DY
open MLS

section Predicate

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `leaf_node_has_been_verified_pred`. -/
@[expose]
public
def leafNodeHasBeenVerifiedPred (tr: ProofTrace) (ev: LeafNodeHasBeenVerified tkt): Prop :=
  -- preconditions of `verifyWithLabel.Invariant`
  ev.groupId.val.Invariant tr ∧
  (LeafNode.mf tkt).wf (Bytes.Invariant · tr) ev.leafNode ∧
  (∃ token, (dyAsp tr).credentialOk (leafNodeToAsInput ev.leafNode) token) ∧
  -- verification succeeded
  leafIsValid ev.leafNode ev.groupId ev.leafIndex

end Predicate

section Lemmas

variable [HasSymbolicBytes] [ExecTraceTypes] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt))]

public
theorem IHaveVerifiedEveryLeafNode_zero (tr: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt 0) (groupId: MlsBytes Bytes):
  IHaveVerifiedEveryLeafNode tr me t groupId ↔
    ∀ ln ∈ t.leafContent, IHaveVerifiedLeafNode tr me ln groupId t.position
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  rw [IHaveVerifiedEveryLeafNode.eq_def]
  grind

public
theorem IHaveVerifiedEveryLeafNode_succ {l: Nat} (tr: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt (l+1))
  (groupId: MlsBytes Bytes) (li: Nat):
  IHaveVerifiedEveryLeafNode tr me t groupId ↔
    IHaveVerifiedEveryLeafNode tr me (t.child li) groupId ∧ IHaveVerifiedEveryLeafNode tr me (t.sibling li) groupId
:= by
  have: IHaveVerifiedEveryLeafNode tr me t groupId ↔
    IHaveVerifiedEveryLeafNode tr me t.left groupId ∧ IHaveVerifiedEveryLeafNode tr me t.right groupId
  := by
    obtain ⟨_, ⟨⟩⟩ := t
    rw [IHaveVerifiedEveryLeafNode.eq_def]
    rfl
  grind

/--
Port of `leaf_at_i_have_verified_every_leaf_node`.
MLS* requires `li: leaf_index l i` (here `hli`); MLS*'s `match leaf_at t li` is the hypothesis `hln`.
-/
public
theorem IHaveVerifiedLeafNode_of_leafAt {l: Nat} (tr: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (li: Nat) (ln: LeafNode Bytes tkt)
  (h: IHaveVerifiedEveryLeafNode tr me t groupId) (hli: t.containsLeafIndex li) (hln: leafAt t li = some ln):
  IHaveVerifiedLeafNode tr me ln groupId li
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    have := eq_of_containsLeafIndex_zero t.containsLeafIndex_position hli
    rw [IHaveVerifiedEveryLeafNode_zero] at h
    grind [leafAt.eq_def]
  | node t ih =>
    rw [IHaveVerifiedEveryLeafNode_succ _ _ _ _ li] at h
    grind [leafAt.eq_def]

/--
Port of `intro_i_have_verified_every_leaf_node`.
MLS*'s `li: leaf_index l i` is the hypothesis `t.containsLeafIndex li`; MLS*'s `match leaf_at t li` is `leafAt t li = some ln`.
-/
public
theorem IHaveVerifiedEveryLeafNode_intro {l: Nat} (tr: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt l)
  (groupId: MlsBytes Bytes)
  (h: ∀ li ln, t.containsLeafIndex li → leafAt t li = some ln → IHaveVerifiedLeafNode tr me ln groupId li):
  IHaveVerifiedEveryLeafNode tr me t groupId
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    rw [IHaveVerifiedEveryLeafNode_zero]
    simp only [leafAt.eq_def, Tree.intoChildSiblingView_zero] at h
    grind [Option.mem_def]
  | node t ihl ihr =>
    rw [IHaveVerifiedEveryLeafNode_succ _ _ _ _ t.position]
    grind [leafAt.eq_def]

/-- Verified leaf nodes stay verified when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IHaveVerifiedLeafNode_le (tr1 tr2: ExecTrace) (me: Participant) (ln: LeafNode Bytes tkt)
  (groupId: MlsBytes Bytes) (leafIndex: Nat)
  : tr1 ≤ tr2 →
    IHaveVerifiedLeafNode tr1 me ln groupId leafIndex →
    IHaveVerifiedLeafNode tr2 me ln groupId leafIndex
:= by
  grind [IHaveVerifiedLeafNode]

grind_pattern IHaveVerifiedLeafNode_le => tr1 ≤ tr2, IHaveVerifiedLeafNode tr1 me ln groupId leafIndex
grind_pattern [grind_later] IHaveVerifiedLeafNode_le => tr1 ≤ tr2, IHaveVerifiedLeafNode tr1 me ln groupId leafIndex

/-- Port of `i_have_verified_every_leaf_node_later`. -/
public
theorem IHaveVerifiedEveryLeafNode_le {l: Nat} (tr1 tr2: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt l)
  (groupId: MlsBytes Bytes)
  : tr1 ≤ tr2 →
    IHaveVerifiedEveryLeafNode tr1 me t groupId →
    IHaveVerifiedEveryLeafNode tr2 me t groupId
:= by
  intro hle
  induction t using Tree.leftRightInduction with
  | leaf t => grind [IHaveVerifiedEveryLeafNode_zero, IHaveVerifiedLeafNode]
  | node t ihl ihr =>
    rw [IHaveVerifiedEveryLeafNode_succ _ _ _ _ t.position, IHaveVerifiedEveryLeafNode_succ _ _ _ _ t.position]
    grind

grind_pattern IHaveVerifiedEveryLeafNode_le => tr1 ≤ tr2, IHaveVerifiedEveryLeafNode tr1 me t groupId
grind_pattern [grind_later] IHaveVerifiedEveryLeafNode_le => tr1 ≤ tr2, IHaveVerifiedEveryLeafNode tr1 me t groupId

theorem logLeafNodeVerificationEvents_zero (me: Participant) (t: TreeSync Bytes tkt 0) (groupId: MlsBytes Bytes):
  logLeafNodeVerificationEvents me t groupId = (
    match t.leafContent with
    | none => pure ()
    | some ln => logLeafNodeVerificationEvent me ln groupId t.position)
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  rw [logLeafNodeVerificationEvents.eq_def]
  cases c <;> rfl

theorem logLeafNodeVerificationEvents_left_right {l: Nat} (me: Participant) (t: TreeSync Bytes tkt (l+1))
  (groupId: MlsBytes Bytes):
  logLeafNodeVerificationEvents me t groupId = (do
    logLeafNodeVerificationEvents me t.left groupId
    logLeafNodeVerificationEvents me t.right groupId)
:= by
  obtain ⟨_, ⟨⟩⟩ := t
  rw [logLeafNodeVerificationEvents.eq_def]
  rfl

end Lemmas

section Proofs

variable [HasSymbolicInvariants] [TraceInvariant] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt))]
variable [ProofTraceTypes.Has (ProtocolEvent.ProofEntryT (LeafNodeHasBeenVerified tkt))]
variable [ProtocolEvent.EventInv (LeafNodeHasBeenVerified tkt)]
variable [TraceInvariant.Has (ProtocolEvent.ProofEntryT (LeafNodeHasBeenVerified tkt))]
variable [ProtocolEvent.EventInv.Has (leafNodeHasBeenVerifiedPred (tkt := tkt))]

/-- Port of `log_leaf_node_verification_event_proof`. -/
@[instance]
public
theorem logLeafNodeVerificationEvent.proof (me: Participant)
  (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat):
  HoareTriple
    (logLeafNodeVerificationEvent me leafNode groupId leafIndex)
    (fun tr =>
      groupId.val.Invariant tr ∧
      (LeafNode.mf tkt).wf (Bytes.Invariant · tr) leafNode ∧
      (∃ token, (dyAsp tr).credentialOk (leafNodeToAsInput leafNode) token) ∧
      leafIsValid leafNode groupId leafIndex
    )
    (fun _ tr => IHaveVerifiedLeafNode tr.erase me leafNode groupId leafIndex)
:= by
  unfold logLeafNodeVerificationEvent
  step by
    rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := leafNodeHasBeenVerifiedPred)]
    simp only [leafNodeHasBeenVerifiedPred]
    grind
  grind [IHaveVerifiedLeafNode]

/-- Port of `log_leaf_node_verification_events_proof`. -/
@[instance]
public
theorem logLeafNodeVerificationEvents.proof {l: Nat} (me: Participant)
  (t: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes):
  HoareTriple
    (logLeafNodeVerificationEvents me t groupId)
    (fun tr =>
      groupId.val.Invariant tr ∧
      (TreeSync.mf tkt l).wf (Bytes.Invariant · tr) t ∧
      (∃ tokens: ASTokens DyAsToken l, t.position = tokens.position ∧ allCredentialsOk (dyAsp tr) t tokens) ∧
      validLeavesInvariant groupId t
    )
    (fun _ tr => IHaveVerifiedEveryLeafNode tr.erase me t groupId)
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    rw [logLeafNodeVerificationEvents_zero]
    split
    · step
      grind [IHaveVerifiedEveryLeafNode_zero]
    · step by
        obtain ⟨hgid, hwf, ⟨tokens, hpos, hcred⟩, hvalid⟩ := ‹_ ∧ _›
        have := allCredentialsOk_elim t tokens t.position hpos hcred
        rw [Tree.mf.wf_zero] at hwf
        simp only [oneCredentialOk] at this
        grind [MlsOption.mf.wf_eq, leafAt.eq_def, validLeavesInvariant_zero]
      grind [IHaveVerifiedEveryLeafNode_zero]
  | node t ihl ihr =>
    rw [logLeafNodeVerificationEvents_left_right]
    step by
      obtain ⟨hgid, hwf, ⟨tokens, hpos, hcred⟩, hvalid⟩ := ‹_ ∧ _›
      rw [Tree.mf.wf_succ] at hwf
      rw [allCredentialsOk_succ _ _ t.position hpos] at hcred
      rw [validLeavesInvariant_succ _ _ t.position] at hvalid
      refine ⟨hgid, ?_, ⟨tokens.left, ?_⟩, ?_⟩ <;> grind
    step by
      obtain ⟨hgid, hwf, ⟨tokens, hpos, hcred⟩, hvalid⟩ := ‹_ ∧ _›
      rw [Tree.mf.wf_succ] at hwf
      rw [allCredentialsOk_succ _ _ t.position hpos] at hcred
      rw [validLeavesInvariant_succ _ _ t.position] at hvalid
      refine ⟨hgid, ?_, ⟨tokens.right, ?_⟩, ?_⟩ <;> grind
    rw [IHaveVerifiedEveryLeafNode_succ _ _ _ _ t.position]
    grind

end Proofs

end MLS.TreeSync
