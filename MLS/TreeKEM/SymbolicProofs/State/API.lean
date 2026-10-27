module

public import MLS.TreeKEM.SymbolicSpec.State.API
public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeKEM.SymbolicProofs.State.NodeKey
public import MLS.TreeKEM.SymbolicProofs.State.EpochSecrets
public import MLS.TreeKEM.SymbolicProofs.API.KeySchedule
public import MLS.TreeKEM.SymbolicProofs.EpochEvent
public import MLS.TreeKEM.Proofs.API
public import MLS.TreeSync.SymbolicProofs.State.Tree
public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified
public import MLS.Glue.Proofs.TreeSyncTreeKEMBinder
import all MLS.TreeKEM.SymbolicSpec.State.API
import all MLS.TreeKEM.SymbolicSpec.State.EpochSecrets
import DY.Meta.Step

/-!
Port of the invariants and proofs of `MLS.TreeKEM.Symbolic.State.API`: the invariant of the state of a principal
in a group, and the proofs of `store_treesync_treekem_state` and `get_treesync_treekem_state`.

Port-specific differences:
- The state predicate (`treesync_treekem_state_pred`) is the DyLean state invariant `treesyncTreekemStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_treesync_treekem_state_invariant` is not needed.
  The proofs assume the proof trace entries of the states (`TreeKEMEpochSecret`, `TreeKEMNodeKeysState`,
  `BareTreeSyncTreeKEMState`).
- `getTreesyncTreekemState` does not check the refinements of MLS*'s types (see `MLS.TreeKEM.SymbolicSpec.State.API`):
  the state invariant states them. Its TreeSync part is `TreeSyncPublicStatePred` (MLS*'s `treesync_public_state_pred`),
  which contains the refinements of `treesync_state` (`TreeSyncState.TreeValid`), and it states that the trees
  are at position `0`, that the TreeKEM tree contains the leaf index (MLS*'s `leaf_index < pow2 levels`)
  and that the heights and trees are related (as `treesync_treekem_state_rel`, comparing dependent pairs).
  Likewise, `TreesyncTreekemStateInvariantAux` also states the refinements of the TreeSync and TreeKEM states
  (`TreeSyncState.TreeValid`, `TreeKEMTreeState.Valid`).
- MLS*'s `opaque_to_smt` invariants are plain definitions.
- The `tr_out == tr` part of the postcondition of `get_treesync_treekem_state_proof` is not ported.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.TreeSync MLS.TreeKEM.Symbolic.API.KeySchedule

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-! ## Invariants -/

/--
Port of `treesync_treekem_state_invariant_aux`.
It also states the refinements of MLS*'s `treesync_state` and `treekem_tree_state`.
-/
@[expose]
public
def TreesyncTreekemStateInvariantAux {leafIndex: Nat} (tr: ProofTrace) (me: Participant)
  (groupContext: GroupContext Bytes) (treesync: TreeSyncState Bytes tkt DyAsToken groupContext.groupId)
  (treekem: TreeKEMTreeState Bytes leafIndex): Prop
:=
  treesync.TreeValid ∧
  treekem.Valid ∧
  treesyncTreekemStateRel treesync treekem ∧

  IAmInTreeAt me treesync.tree leafIndex ∧
  GroupContext.mf.wf (Bytes.Publishable · tr) groupContext ∧

  (TreeSync.mf tkt treesync.levels).wf (Bytes.Publishable · tr) treesync.tree ∧
  treesyncStateValid (dyAsp tr) treesync ∧
  IHaveVerifiedEveryLeafNode tr.erase me treesync.tree groupContext.groupId ∧

  TreekemPrivStatePred tr me treekem.priv

/-- Port of `treesync_treekem_state_invariant`. -/
@[expose]
public
def TreesyncTreekemStateInvariant (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState): Prop :=
  TreesyncTreekemStateInvariantAux tr me st.groupContext st.treesync st.treekem.treeState

/-- Port of `treesync_treekem_state_coarse_invariant`. -/
@[expose]
public
def TreesyncTreekemStateCoarseInvariant (tr: ProofTrace) (_me: Participant) (st: TreeSyncTreeKEMState): Prop :=
  TreekemKeyscheduleStateGood tr st.treekem.keyscheduleState st.groupContext ∧
  TreekemKeyscheduleStateAuthWeakExists st.treekem.keyscheduleState ∧
  TreeHasHash st.treesync.tree st.groupContext.treeHash.val

/-- Port of `treesync_treekem_state_very_coarse_invariant`. -/
@[expose]
public
def TreesyncTreekemStateVeryCoarseInvariant (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState): Prop :=
  IHavePreviousEpochEvent tr.erase me st.groupContext st.treekem.keyscheduleState.initSecret st.treesync.tree

/-- Port of `treesync_treekem_state_all_invariants`. -/
@[expose]
public
def TreesyncTreekemStateAllInvariants (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState): Prop :=
  TreesyncTreekemStateInvariant tr me st ∧
  TreesyncTreekemStateCoarseInvariant tr me st ∧
  TreesyncTreekemStateVeryCoarseInvariant tr me st

/-- Port of `treesync_treekem_state_invariant_later`. -/
public
theorem TreesyncTreekemStateInvariant_later (tr1 tr2: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  : tr1 ≤ tr2 →
    TreesyncTreekemStateInvariant tr1 me st →
    TreesyncTreekemStateInvariant tr2 me st
:= by
  grind [TreesyncTreekemStateInvariant, TreesyncTreekemStateInvariantAux, treesyncStateValid]

grind_pattern TreesyncTreekemStateInvariant_later => tr1 ≤ tr2, TreesyncTreekemStateInvariant tr1 me st
grind_pattern [grind_later] TreesyncTreekemStateInvariant_later => tr1 ≤ tr2, TreesyncTreekemStateInvariant tr1 me st

omit [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
/-- Port of `treesync_treekem_state_coarse_invariant_later`. -/
public
theorem TreesyncTreekemStateCoarseInvariant_later (tr1 tr2: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  : tr1 ≤ tr2 →
    TreesyncTreekemStateCoarseInvariant tr1 me st →
    TreesyncTreekemStateCoarseInvariant tr2 me st
:= by
  grind [TreesyncTreekemStateCoarseInvariant, TreekemKeyscheduleStateGood]

grind_pattern TreesyncTreekemStateCoarseInvariant_later => tr1 ≤ tr2, TreesyncTreekemStateCoarseInvariant tr1 me st
grind_pattern [grind_later] TreesyncTreekemStateCoarseInvariant_later =>
  tr1 ≤ tr2,
  TreesyncTreekemStateCoarseInvariant tr1 me st

omit [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
/-- Port of `treesync_treekem_state_very_coarse_invariant_later`. -/
public
theorem TreesyncTreekemStateVeryCoarseInvariant_later (tr1 tr2: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  : tr1 ≤ tr2 →
    TreesyncTreekemStateVeryCoarseInvariant tr1 me st →
    TreesyncTreekemStateVeryCoarseInvariant tr2 me st
:= by
  grind [TreesyncTreekemStateVeryCoarseInvariant]

grind_pattern TreesyncTreekemStateVeryCoarseInvariant_later =>
  tr1 ≤ tr2,
  TreesyncTreekemStateVeryCoarseInvariant tr1 me st
grind_pattern [grind_later] TreesyncTreekemStateVeryCoarseInvariant_later =>
  tr1 ≤ tr2,
  TreesyncTreekemStateVeryCoarseInvariant tr1 me st

/-- `treesync_treekem_state_all_invariants` stay true when the trace grows (MLS* uses SMT patterns). -/
public
theorem TreesyncTreekemStateAllInvariants_later (tr1 tr2: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  : tr1 ≤ tr2 →
    TreesyncTreekemStateAllInvariants tr1 me st →
    TreesyncTreekemStateAllInvariants tr2 me st
:= by
  grind [TreesyncTreekemStateAllInvariants]

grind_pattern TreesyncTreekemStateAllInvariants_later => tr1 ≤ tr2, TreesyncTreekemStateAllInvariants tr1 me st
grind_pattern [grind_later] TreesyncTreekemStateAllInvariants_later =>
  tr1 ≤ tr2,
  TreesyncTreekemStateAllInvariants tr1 me st

/-! ## Authentication of the secrets by the confirmation tag -/

/-- The secrets of a key schedule state authenticated by its confirmation tag (both directions are lemmas of MLS*). -/
@[expose]
public
def KeyscheduleStateKeysAreAuthenticated (st: TreeKEMKeyscheduleState Bytes): Prop :=
  KeyIsAuthenticatedByConfirmationTag .senderDataSecret st.epochKeys.confirmationTag st.epochKeys.senderDataSecret ∧
  KeyIsAuthenticatedByConfirmationTag .exporterSecret st.epochKeys.confirmationTag st.epochKeys.exporterSecret ∧
  KeyIsAuthenticatedByConfirmationTag .externalSecret st.epochKeys.confirmationTag st.epochKeys.externalSecret ∧
  KeyIsAuthenticatedByConfirmationTag .membershipKey st.epochKeys.confirmationTag st.epochKeys.membershipKey ∧
  KeyIsAuthenticatedByConfirmationTag .resumptionPsk st.epochKeys.confirmationTag st.epochKeys.resumptionPsk ∧
  KeyIsAuthenticatedByConfirmationTag .epochAuthenticator st.epochKeys.confirmationTag st.epochKeys.epochAuthenticator ∧
  KeyIsAuthenticatedByConfirmationTag .initSecret st.epochKeys.confirmationTag st.initSecret

omit [HasTreeKEMExecTrace] [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
/-- Port of `treekem_keyschedule_state_auth_weak_exists_implies_key_is_authenticated_by_confirmation_tag`. -/
public
theorem TreekemKeyscheduleStateAuthWeakExists.keysAreAuthenticated (st: TreeKEMKeyscheduleState Bytes)
  (h: TreekemKeyscheduleStateAuthWeakExists st):
  KeyscheduleStateKeysAreAuthenticated st
:= by
  exact ⟨⟨st, h, rfl, rfl⟩, ⟨st, h, rfl, rfl⟩, ⟨st, h, rfl, rfl⟩, ⟨st, h, rfl, rfl⟩,
    ⟨st, h, rfl, rfl⟩, ⟨st, h, rfl, rfl⟩, ⟨st, h, rfl, rfl⟩⟩

omit [HasTreeKEMExecTrace] [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
/-- Port of `key_is_authenticated_by_confirmation_tag_implies_treekem_keyschedule_state_auth_weak_exists`. -/
public
theorem TreekemKeyscheduleStateAuthWeakExists.of_keysAreAuthenticated (st: TreeKEMKeyscheduleState Bytes)
  (h: KeyscheduleStateKeysAreAuthenticated st):
  TreekemKeyscheduleStateAuthWeakExists st
:= by
  simp only [KeyscheduleStateKeysAreAuthenticated, KeyIsAuthenticatedByConfirmationTag,
    KeyIsAuthenticatedByConfirmationTagWithWitness] at h
  obtain ⟨⟨st1, h1, htag1, hk1⟩, ⟨st2, h2, htag2, hk2⟩, ⟨st3, h3, htag3, hk3⟩, ⟨st4, h4, htag4, hk4⟩,
    ⟨st5, h5, htag5, hk5⟩, ⟨st6, h6, htag6, hk6⟩, ⟨st7, h7, htag7, hk7⟩⟩ := h
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st2 h1 h2 (by grind)
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st3 h1 h3 (by grind)
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st4 h1 h4 (by grind)
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st5 h1 h5 (by grind)
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st6 h1 h6 (by grind)
  obtain rfl := TreekemKeyscheduleStateAuthWeakExists.inj st1 st7 h1 h7 (by grind)
  have: st1 = st := by
    obtain ⟨⟨_, _, _, _, _, _, _⟩, _⟩ := st
    obtain ⟨⟨_, _, _, _, _, _, _⟩, _⟩ := st1
    simp only [keyscheduleStateToKey] at *
    grind
  rw [← this]
  exact h1

/-! ## State invariant -/

/-- Port of `treesync_treekem_state_pred`: the invariant of the states of a principal in a group. -/
public
instance treesyncTreekemStateInv: CompromisableLocalStateInv BareTreeSyncTreeKEMState where
  invariant me st tr :=
    TreeSyncPublicStatePred tr st.treesync ∧
    TreeHasHash st.treesync.st.tree st.groupContext.treeHash.val ∧

    st.treesync.groupId = st.groupContext.groupId ∧
    (⟨st.treesync.st.levels, treesyncToTreekem st.treesync.st.tree⟩: (l: Nat) × TreeKEM Bytes l) =
      ⟨st.treekem.levels, st.treekem.tree⟩ ∧
    st.treesync.st.tree.position = 0 ∧
    st.treekem.tree.containsLeafIndex st.leafIndex ∧
    (leafAt st.treekem.tree st.leafIndex).isSome ∧
    IAmInTreeAt me st.treesync.st.tree st.leafIndex ∧

    GroupContext.mf.wf (Bytes.Publishable · tr) st.groupContext ∧
    st.treekem.confirmationTag.Publishable tr ∧

    (∃ initSecret,
      KeyIsAuthenticatedByConfirmationTag .initSecret st.treekem.confirmationTag initSecret ∧
      IHavePreviousEpochEvent tr.erase me st.groupContext initSecret st.treesync.st.tree
    ) ∧
    IHaveVerifiedEveryLeafNode tr.erase me st.treesync.st.tree st.groupContext.groupId
  invariant_later me st tr1 tr2 := by
    grind
  invariant_implies_KnowableBy me st tr h := by
    obtain ⟨_, _, _, _, ⟨levels, tree⟩⟩ := st
    obtain ⟨hts, -, -, hrel, -, -, -, -, hgc, htag, -, -⟩ := h
    dsimp only at hrel
    obtain ⟨rfl, rfl⟩ := Sigma.mk.inj hrel
    simp only [DY.Comparse.IsWellFormed, DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq]
    apply wf_knowableBy_of_publishable
    rw [BareTreeSyncTreeKEMState.mf.wf_eq, BareTreeKEMState.mf.wf_eq]
    exact ⟨hgc, TreeSyncPublicStatePred.wf tr _ hts, treesyncToTreekem_wf _ _ hts.2.1, htag⟩

/-! ## Proofs -/

section Proofs

attribute [local grind] TreekemKeyscheduleStateGood KeyscheduleStateKeysAreAuthenticated
attribute [local grind] TreesyncTreekemStateAllInvariants TreesyncTreekemStateInvariant TreesyncTreekemStateInvariantAux
attribute [local grind] TreesyncTreekemStateCoarseInvariant

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMNodeKeysState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT BareTreeSyncTreeKEMState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT BareTreeSyncTreeKEMState)]

/-- Port of `store_treesync_treekem_state_proof`. -/
@[instance]
public
theorem storeTreesyncTreekemState.proof (me: Participant) (st: TreeSyncTreeKEMState):
  HoareTriple
    (storeTreesyncTreekemState me st)
    (fun tr => TreesyncTreekemStateAllInvariants tr me st)
    (fun _ _ => True)
:= by
  unfold storeTreesyncTreekemState
  step_intro
  step_intro
  step by
    grind [IAmInGroupContext.intro me st.groupContext st.treesync.tree st.leafIndex,
      IAmInGroupContextWithWitness, TreeHashFullTreeRel, → TreekemKeyscheduleStateAuthWeakExists.keysAreAuthenticated]
  have h := ‹TreesyncTreekemStateAllInvariants tr me st›
  have := IAmInGroupContext.intro me st.groupContext st.treesync.tree st.leafIndex ⟨h.2.1.2.2, h.1.2.2.2.1⟩
  have := TreekemKeyscheduleStateAuthWeakExists.keysAreAuthenticated _ h.2.1.2.1
  step
  step
  step
  step
  step
  step
  step
  step_intro
  step by
    simp only [LocalStateInv.invariant, bareSt, confirmationTag, epochKeys, TreeSyncPublicStatePred]
    refine ⟨?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨st.treekem.keyscheduleState.initSecret, ?_, ?_⟩, ?_⟩
      <;> grind [GroupContext.mf.wf_eq, TreesyncTreekemStateVeryCoarseInvariant, TreeKEMTreeState.Valid,
        treekemPrivInvariant, treesyncTreekemStateRel]
  trivial

/-- Port of `get_treesync_treekem_state_proof`. -/
@[instance]
public
theorem getTreesyncTreekemState.proof (me: Participant) (sid: Nat):
  HoareTriple
    (getTreesyncTreekemState me sid)
    (fun _ => True)
    (fun st tr => TreesyncTreekemStateAllInvariants tr me st)
:= by
  unfold getTreesyncTreekemState
  step
  step_intro
  step
  step
  step
  step
  step
  step
  step
  split
  · step
    step
    subst x
    obtain ⟨leafIndex, groupContext, mySignatureKeySid, ⟨groupId, ⟨levels, tree, tokens⟩⟩,
      ⟨_, _, _, _, _, _, _, _, _, _, _⟩⟩ := bareSt
    simp only [confirmationTag, LocalStateInv.invariant] at *
    obtain ⟨-, -, rfl, hrel, -⟩ := ‹TreeSyncPublicStatePred tr _ ∧ _›
    obtain ⟨rfl, rfl⟩ := Sigma.mk.inj hrel
    cases ‹groupContext.groupId = groupContext.groupId›
    grind [TreesyncTreekemStateVeryCoarseInvariant, TreeKEMTreeState.Valid,
      treekemPrivInvariant, treesyncTreekemStateRel, TreeSyncPublicStatePred, TreeSyncState.TreeValid,
      treesyncToTreekem_invariant, TreekemKeyscheduleStateAuthWeakExists.of_keysAreAuthenticated,
      KeyIsAuthenticatedByConfirmationTag.inj]
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

end Proofs

end MLS.TreeKEM
