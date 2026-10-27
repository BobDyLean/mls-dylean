module

public import MLS.TreeSync.SymbolicSpec.State.Tree
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.TreeSync.Proofs.API
public import MLS.Symbolic.SymbolicProofs.MiscLemmas

/-!
Port of the invariant of `MLS.TreeSync.Symbolic.State.Tree`: the invariant of the public state of TreeSync.

Port-specific differences:
- The predicate of `treesync_public_state_pred` is the `Prop` definition `TreeSyncPublicStatePred`,
  also used by the invariant of the TreeKEM states (which contain a public state of TreeSync).
- The refinements of `treesync_state` that MLS*'s invariant states (`unmerged_leaves_ok`, `parent_hash_invariant`,
  `valid_leaves_invariant`) are `TreeSyncState.TreeValid`, and `all_credentials_ok` is `treesyncStateValid (dyAsp tr)`
  (which also states that the tree and the tokens have the same position).
- The state predicate (`treesync_public_state_pred`) is the DyLean state invariant `treeSyncPublicStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_treesync_public_state_invariant` is not needed.
- MLS*'s `new_public_treesync_state`, `set_public_treesync_state` and `get_public_treesync_state` are not ported
  (the state is stored with `storeLocalState`, see `MLS.TreeSync.SymbolicSpec.State.Tree`):
  their proofs are `TreeSyncPublicState.invariant_iff`, which states the invariant of a stored state
  (the precondition of DyLean's `storeLocalState.proof`, the postcondition of `getLocalState.proof`).
-/

namespace MLS.TreeSync

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.TreeSync.API

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}

/-- Port of `ps_dy_as_tokens_is_well_formed`: tokens contain no bytes. -/
theorem ASTokens.mf_wf {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred] (tokens: ASTokens DyAsToken l):
  (ASTokens.mf DyAsToken.mf l).wf pred tokens
:= by
  rw [Tree.mf.wf_eq]
  obtain ⟨_, bt⟩ := tokens
  induction bt with
  | leaf x => cases x <;> simp [MlsOption.mf.wf_eq]
  | node c L R ihL ihR => simp_all

variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- The credentials of a TreeSync state stay valid when the trace grows (MLS* uses SMT patterns). -/
public
theorem treesyncStateValid_dyAsp_later {groupId: MlsBytes Bytes} (tr1 tr2: ProofTrace)
  (st: TreeSyncState Bytes tkt DyAsToken groupId)
  : tr1 ≤ tr2 →
    treesyncStateValid (dyAsp tr1) st →
    treesyncStateValid (dyAsp tr2) st
:= by
  grind [treesyncStateValid]

grind_pattern treesyncStateValid_dyAsp_later => tr1 ≤ tr2, treesyncStateValid (dyAsp tr1) st
grind_pattern [grind_later] treesyncStateValid_dyAsp_later => tr1 ≤ tr2, treesyncStateValid (dyAsp tr1) st

/-- Port of `treesync_public_state_pred` (its predicate). -/
@[expose]
public
def TreeSyncPublicStatePred (tr: ProofTrace) (x: TreeSyncPublicState tkt): Prop :=
  x.groupId.val.Publishable tr ∧
  (TreeSync.mf tkt x.st.levels).wf (Bytes.Publishable · tr) x.st.tree ∧
  x.st.TreeValid ∧
  treesyncStateValid (dyAsp tr) x.st

/-- Port of `treesync_public_state_pred` (its `pred_later`). -/
public
theorem TreeSyncPublicStatePred_later (tr1 tr2: ProofTrace) (x: TreeSyncPublicState tkt)
  : tr1 ≤ tr2 →
    TreeSyncPublicStatePred tr1 x →
    TreeSyncPublicStatePred tr2 x
:= by
  grind [TreeSyncPublicStatePred, treesyncStateValid]

grind_pattern TreeSyncPublicStatePred_later => tr1 ≤ tr2, TreeSyncPublicStatePred tr1 x
grind_pattern [grind_later] TreeSyncPublicStatePred_later => tr1 ≤ tr2, TreeSyncPublicStatePred tr1 x

/--
Public states of TreeSync are publishable
(MLS* proves it in `pred_knowable` of `treesync_public_state_pred` and of `treesync_treekem_state_pred`).
-/
public
theorem TreeSyncPublicStatePred.wf (tr: ProofTrace) (x: TreeSyncPublicState tkt) (h: TreeSyncPublicStatePred tr x):
  (TreeSyncPublicState.mf tkt).wf (Bytes.Publishable · tr) x
:= by
  rw [TreeSyncPublicState.mf.wf_eq]
  exact ⟨h.1, h.2.1, ASTokens.mf_wf _ _⟩

variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (TreeSyncPublicState tkt))]

variable (tkt) in
/--
The invariant of the public states of TreeSync (MLS*'s `treesync_public_state_pred`):
`TreeSyncPublicStatePred`. MLS*'s `has_treesync_public_state_invariant` is this instance.
-/
public
instance treeSyncPublicStateInv: CompromisableLocalStateInv (TreeSyncPublicState tkt) where
  invariant _ x tr := TreeSyncPublicStatePred tr x
  invariant_later prin x tr1 tr2 := by
    grind
  invariant_implies_KnowableBy prin x tr h := by
    simp only [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq]
    exact wf_knowableBy_of_publishable (TreeSyncPublicState.mf tkt) (label prin x) tr x (TreeSyncPublicStatePred.wf tr x h)

/--
Port of `new_public_treesync_state_proof`, `set_public_treesync_state_proof` and `get_public_treesync_state_proof`:
the invariant of a public state of TreeSync.
-/
public
theorem TreeSyncPublicState.invariant_iff (prin: Participant) (x: TreeSyncPublicState tkt) (tr: ProofTrace):
  LocalStateInv.invariant prin x tr ↔ (
    x.groupId.val.Publishable tr ∧
    (TreeSync.mf tkt x.st.levels).wf (Bytes.Publishable · tr) x.st.tree ∧
    x.st.TreeValid ∧
    treesyncStateValid (dyAsp tr) x.st
  )
:= by
  rfl

end MLS.TreeSync
