module

public import MLS.TreeSync.SymbolicSpec.Event.LeafNodeHasBeenVerified
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.Symbolic.Code.Parsers
public import MLS.TreeSync.Code.Parsers
import all MLS.TreeSync.SymbolicSpec.Event.LeafNodeHasBeenVerified

/-!
Port of the predicate and lemmas of `MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified`:
the invariant of the event logged when a principal verifies a leaf node.

Port-specific differences:
- DY*'s `has_event_pred` is DySlop's `ProtocolEvent.EventInv.Has` (see `DySlop.Lib.Event`).
- The proofs of the traceful functions (`log_leaf_node_verification_event_proof`, …) are not ported yet.
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

end Lemmas

end MLS.TreeSync
