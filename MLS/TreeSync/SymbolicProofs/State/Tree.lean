module

public import MLS.TreeSync.SymbolicSpec.State.Tree
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.TreeSync.Proofs.API
public import MLS.Symbolic.SymbolicProofs.MiscLemmas

/-!
Port of the invariant of `MLS.TreeSync.Symbolic.State.Tree`: the invariant of the public state of TreeSync.

Port-specific differences:
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
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (TreeSyncPublicState tkt))]

variable (tkt) in
/--
Port of `treesync_public_state_pred`: the invariant of the public states of TreeSync
(MLS*'s `has_treesync_public_state_invariant` is this instance).
-/
public
instance treeSyncPublicStateInv: CompromisableLocalStateInv (TreeSyncPublicState tkt) where
  invariant _ x tr :=
    x.groupId.val.Publishable tr ∧
    (TreeSync.mf tkt x.st.levels).wf (Bytes.Publishable · tr) x.st.tree ∧
    x.st.TreeValid ∧
    treesyncStateValid (dyAsp tr) x.st
  invariant_later prin x tr1 tr2 := by
    grind [treesyncStateValid]
  invariant_implies_KnowableBy prin x tr h := by
    simp only [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq, TreeSyncPublicState.mf.wf_eq]
    have := wf_knowableBy_of_publishable (TreeSync.mf tkt x.st.levels) (label prin x) tr x.st.tree
    grind [Bytes.Publishable, Bytes.KnowableBy, canFlowTrans, ASTokens.mf_wf]

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
