module

public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified
public import MLS.TreeSync.Proofs.API.LeafAt

/-!
Port of `MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified.Invariant`:
the `finalize_*` functions of the TreeSync API preserve `i_have_verified_every_leaf_node`.

Port-specific differences:
- The tree of a state is not at position `0` (MLS*'s `treesync bytes tkt l 0`):
  the leaves are stated with `leafAtNat` (see `MLS.TreeSync.API.LeafAt`).
- The implicit leaf indices `li: treesync_index st` of the pending states are hypotheses `st.tree.containsLeafIndex li`.
- MLS*'s `match`es on results are hypotheses (`finalizeAdd pend token = .success (newState, addLi) → …`).
-/

namespace MLS.TreeSync

open DY
open MLS MLS.TreeSync.API

variable [HasSymbolicBytes] [ExecTraceTypes] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt))]
variable {groupId: MlsBytes Bytes}

/-- `IHaveVerifiedEveryLeafNode`, stated with `leafAtNat`. -/
theorem IHaveVerifiedEveryLeafNode_iff_leafAtNat {l: Nat} (tr: ExecTrace) (me: Participant) (t: TreeSync Bytes tkt l):
  IHaveVerifiedEveryLeafNode tr me t groupId ↔
    ∀ li ln, leafAtNat t li = some ln → IHaveVerifiedLeafNode tr me ln groupId li
:= by
  constructor
  · intro h li ln hln
    apply IHaveVerifiedLeafNode_of_leafAt tr me t groupId li ln h <;> grind [leafAtNat]
  · intro h
    apply IHaveVerifiedEveryLeafNode_intro
    grind [leafAtNat]

/-- Port of `i_have_verified_every_leaf_node_finalize_create`. -/
public
theorem IHaveVerifiedEveryLeafNode_finalizeCreate {ln: LeafNode Bytes tkt} (tr: ExecTrace) (me: Participant)
  (pend: PendingCreate groupId ln) (token: DyAsToken)
  (h: IHaveVerifiedLeafNode tr me ln groupId 0):
  IHaveVerifiedEveryLeafNode tr me (finalizeCreate pend token).tree groupId
:= by
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat]
  intro li
  have := leafAtNat_finalizeCreate pend token li
  grind

/--
Port of `i_have_verified_every_leaf_node_finalize_welcome`.
MLS* requires `List.Tot.length tokens == pow2 l`, which the proof does not need.
-/
public
theorem IHaveVerifiedEveryLeafNode_finalizeWelcome {l: Nat} {t: TreeSync Bytes tkt l} (tr: ExecTrace) (me: Participant)
  (pend: PendingWelcome groupId t) (tokens: List (Option DyAsToken))
  (h: IHaveVerifiedEveryLeafNode tr me t groupId):
  IHaveVerifiedEveryLeafNode tr me (finalizeWelcome pend tokens).tree groupId
:= by
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat] at h ⊢
  intro li
  have := leafAtNat_finalizeWelcome pend tokens li
  grind

/-- Port of `i_have_verified_every_leaf_node_finalize_add`. -/
public
theorem IHaveVerifiedEveryLeafNode_finalizeAdd {st: TreeSyncState Bytes tkt DyAsToken groupId} {ln: LeafNode Bytes tkt}
  (tr: ExecTrace) (me: Participant) (pend: PendingAdd st ln) (token: DyAsToken)
  (newState: TreeSyncState Bytes tkt DyAsToken groupId) (addLi: Nat) (h: finalizeAdd pend token = .success (newState, addLi))
  (hst: IHaveVerifiedEveryLeafNode tr me st.tree groupId):
  IHaveVerifiedLeafNode tr me ln groupId addLi →
  IHaveVerifiedEveryLeafNode tr me newState.tree groupId
:= by
  intro hln
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat] at hst ⊢
  intro li
  have := leafAtNat_finalizeAdd pend token li newState addLi h
  grind

/-- Port of `i_have_verified_every_leaf_node_finalize_update`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem IHaveVerifiedEveryLeafNode_finalizeUpdate {st: TreeSyncState Bytes tkt DyAsToken groupId}
  {ln: LeafNode Bytes tkt} {li: Nat}
  (tr: ExecTrace) (me: Participant) (pend: PendingUpdate st ln li) (token: DyAsToken)
  (hli: st.tree.containsLeafIndex li)
  (hst: IHaveVerifiedEveryLeafNode tr me st.tree groupId) (hln: IHaveVerifiedLeafNode tr me ln groupId li):
  IHaveVerifiedEveryLeafNode tr me (finalizeUpdate pend token).tree groupId
:= by
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat] at hst ⊢
  intro li'
  have := leafAtNat_finalizeUpdate pend token li' hli
  grind

/-- Port of `i_have_verified_every_leaf_node_finalize_remove`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem IHaveVerifiedEveryLeafNode_finalizeRemove {st: TreeSyncState Bytes tkt DyAsToken groupId} {li: Nat}
  (tr: ExecTrace) (me: Participant) (pend: PendingRemove st li)
  (hli: st.tree.containsLeafIndex li)
  (hst: IHaveVerifiedEveryLeafNode tr me st.tree groupId):
  IHaveVerifiedEveryLeafNode tr me (finalizeRemove pend).tree groupId
:= by
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat] at hst ⊢
  intro li'
  have := leafAtNat_finalizeRemove pend li' hli
  grind

/-- Port of `i_have_verified_every_leaf_node_finalize_commit`. MLS* requires `li: treesync_index st` (here `hli`). -/
public
theorem IHaveVerifiedEveryLeafNode_finalizeCommit {st: TreeSyncState Bytes tkt DyAsToken groupId} {li: Nat}
  {p: PathSync Bytes tkt st.levels}
  (tr: ExecTrace) (me: Participant) (pend: PendingCommit st li p) (token: DyAsToken)
  (newState: TreeSyncState Bytes tkt DyAsToken groupId) (h: finalizeCommit pend token = .success newState)
  (hli: st.tree.containsLeafIndex li)
  (hst: IHaveVerifiedEveryLeafNode tr me st.tree groupId) (hln: IHaveVerifiedLeafNode tr me p.getPathLeaf groupId li):
  IHaveVerifiedEveryLeafNode tr me newState.tree groupId
:= by
  rw [IHaveVerifiedEveryLeafNode_iff_leafAtNat] at hst ⊢
  intro li'
  have := leafAtNat_finalizeCommit pend token li' newState h hli
  grind

end MLS.TreeSync
