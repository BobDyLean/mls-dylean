module

public import MLS.TreeKEM.Code.API
public import MLS.TreeKEM.Proofs.API.Tree

/-!
Proofs about `MLS.TreeKEM.API`.

The refinements of MLS*'s types (`treekem_state` through its `tree_state`, `full_commit_args`,
`continue_create_commit_result`) and of the pending states are predicates (`*.Valid`),
established or preserved by the functions of the API, under the preconditions of MLS*.
-/

namespace MLS.TreeKEM.API

open Comparse
open MLS

variable {Bytes: Type}

/-! ## Predicates -/

/-- The refinements of `treekem_state` (those of its `tree_state`). -/
@[expose]
public
def _root_.MLS.TreeKEM.TreeKEMState.Valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd): Prop :=
  st.treeState.Valid

/--
The refinements of `full_commit_args`: `commit_leaf_ind < pow2 st.levels`, `commit_leaf_ind <> leaf_ind`,
`path_filtering_ok st.tree path` and `~(List.Tot.memP leaf_ind excluded_leaves)`.
-/
@[expose]
public
def FullCommitArgs.Valid [CryptoBytes Bytes] {leafInd: Nat} {st: TreeKEMTreeState Bytes leafInd} (args: FullCommitArgs st): Prop :=
  st.tree.containsLeafIndex args.commitLeafInd ∧ args.commitLeafInd ≠ leafInd ∧
  pathFilteringOk st.tree args.commitLeafInd args.path ∧ leafInd ∉ args.excludedLeaves

/-- The refinements of `pending_process_commit` (those of its `next_tree_state`). -/
@[expose]
public
def PendingProcessCommit.Valid {leafInd: Nat} {st: TreeKEMState Bytes leafInd} (pend: PendingProcessCommit st): Prop :=
  pend.nextTreeState.Valid

/-- The refinements of `pending_create_commit` (those of its `pend`). -/
@[expose]
public
def PendingCreateCommit.Valid [CryptoBytes Bytes] {leafInd: Nat} {st: TreeKEMState Bytes leafInd} (pend: PendingCreateCommit st): Prop :=
  pend.pend.Valid

/-- The refinements of `pending_create_commit_2` (those of its `new_state`). -/
@[expose]
public
def PendingCreateCommit2.Valid {leafInd: Nat} (pend: PendingCreateCommit2 Bytes leafInd): Prop :=
  pend.newState.Valid

/-- The refinement `path_filtering_ok st.tree_state.tree update_path` of `continue_create_commit_result`. -/
@[expose]
public
def ContinueCreateCommitResult.Valid [CryptoBytes Bytes] {leafInd: Nat} {st: TreeKEMState Bytes leafInd} (res: ContinueCreateCommitResult st): Prop :=
  pathFilteringOk st.treeState.tree leafInd res.updatePath

/-- The refinements of `create_commit_result` (those of its `new_state`). -/
@[expose]
public
def CreateCommitResult.Valid {leafInd: Nat} (res: CreateCommitResult Bytes leafInd): Prop :=
  res.newState.Valid

/-! ## Create, welcome, add, update, remove -/

section CryptoBytes

variable [CryptoBytes Bytes]

public
theorem create_valid (decKey encKey epochSecret: Bytes) (groupContext: GroupContext Bytes)
  (st: TreeKEMState Bytes 0) (encryptionSecret: Bytes)
  (h: create decKey encKey epochSecret groupContext = .success (st, encryptionSecret)):
  st.Valid
:= by
  simp only [create, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨_, -, rfl, -⟩ := h
  exact Tree.create_valid decKey encKey

/--
MLS* requires `treekem_invariant t`, `leaf_ind < pow2 l` and `Some? (leaf_at t leaf_ind)`,
with `t` at position `0` (MLS*'s `treekem bytes l 0`).
-/
public
theorem welcome_valid {l: Nat} (t: TreeKEM Bytes l) (leafDecryptionKey: Bytes) (optPathSecretAndInviterInd: Option (Bytes × Nat))
  (leafInd: Nat) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes)
  (st: TreeKEMState Bytes leafInd) (encryptionSecret: Bytes)
  (h: welcome t leafDecryptionKey optPathSecretAndInviterInd leafInd joinerSecret psks groupContext = .success (st, encryptionSecret))
  (hpos: t.position = 0) (hinv: treekemInvariant t) (hli: t.containsLeafIndex leafInd) (hleaf: (leafAt t leafInd).isSome):
  st.Valid
:= by
  simp only [welcome, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨treeState, h1, _, -, rfl, -⟩ := h
  exact Tree.welcome_valid t _ _ leafInd treeState h1 hpos hinv hli hleaf

end CryptoBytes

public
theorem add_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (kp: TreeKEMLeaf Bytes) (hst: st.Valid):
  (add st kp).1.Valid
:=
  Tree.add_valid st.treeState kp hst

public
theorem updateMyself_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes)
  (hst: st.Valid):
  (updateMyself st lp leafDecryptionKey).Valid
:=
  Tree.updateMyself_valid st.treeState lp leafDecryptionKey hst

/-- MLS* requires `i < pow2 st.tree_state.levels` (here `hi`) and `i <> leaf_ind`. -/
public
theorem updateOther_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (i: Nat)
  (hi: st.treeState.tree.containsLeafIndex i) (hne: i ≠ leafInd) (hst: st.Valid):
  (updateOther st lp i).Valid
:=
  Tree.updateOther_valid st.treeState lp i hi hne hst

/-- MLS* requires `i < pow2 st.tree_state.levels` (here `hi`) and `i <> leaf_ind`. -/
public
theorem remove_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (i: Nat)
  (hi: st.treeState.tree.containsLeafIndex i) (hne: i ≠ leafInd) (hst: st.Valid):
  (remove st i).Valid
:=
  Tree.remove_valid st.treeState i hi hne hst

/-! ## Process commit -/

section CryptoBytes

variable [CryptoBytes Bytes]

public
theorem prepareProcessFullCommit_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (args: FullCommitArgs st.treeState)
  (pend: PendingProcessCommit st) (h: prepareProcessFullCommit st args = .success pend)
  (hargs: args.Valid) (hst: st.Valid):
  pend.Valid
:= by
  simp only [prepareProcessFullCommit, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨⟨nextTreeState, _⟩, h1, rfl⟩ := h
  exact Tree.commit_valid st.treeState _ _ _ _ _ _ h1 hargs.1 hargs.2.1 hargs.2.2.1 hargs.2.2.2 hst

omit [CryptoBytes Bytes] in
public
theorem prepareProcessAddOnlyCommit_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd)
  (pend: PendingProcessCommit st) (h: prepareProcessAddOnlyCommit st = .success pend) (hst: st.Valid):
  pend.Valid
:= by
  simp only [prepareProcessAddOnlyCommit, Result.pure_eq_success] at h
  subst h
  exact hst

public
theorem finalizeProcessCommit_valid {leafInd: Nat} {st: TreeKEMState Bytes leafInd}
  (pend: PendingProcessCommit st) (psks: List (PreSharedKeyId Bytes × Bytes)) (newGroupContext: GroupContext Bytes)
  (res: TreeKEMState Bytes leafInd) (encryptionSecret: Bytes)
  (h: finalizeProcessCommit pend psks newGroupContext = .success (res, encryptionSecret))
  (hpend: pend.Valid):
  res.Valid
:= by
  simp only [finalizeProcessCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨_, -, rfl, -⟩ := h
  exact hpend

/-! ## Create commit -/

public
theorem prepareCreateCommit_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd) (rand: Randomness Bytes)
  (pend: PendingCreateCommit st) (prePath: PrePathKEM Bytes st.treeState.levels)
  (h: prepareCreateCommit st rand = .success (pend, prePath)):
  pend.Valid
:= by
  simp only [prepareCreateCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨⟨treePend, _⟩, h1, rfl, -⟩ := h
  exact Tree.prepareCreateCommit_valid _ _ _ _ h1

public
theorem continueCreateCommit_valid {leafInd: Nat} {st: TreeKEMState Bytes leafInd}
  (pending: PendingCreateCommit st) (addedLeaves: List Nat) (provisionalGroupContext: GroupContext Bytes)
  (randomness: Randomness Bytes) (pend: PendingCreateCommit2 Bytes leafInd) (res: ContinueCreateCommitResult st)
  (h: continueCreateCommit pending addedLeaves provisionalGroupContext randomness = .success (pend, res))
  (hpend: pending.Valid) (hst: st.Valid):
  pend.Valid ∧ res.Valid
:= by
  simp only [continueCreateCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨treeCommitResult, h1, rfl, rfl⟩ := h
  exact Tree.finalizeCreateCommit_valid _ _ _ _ _ h1 hpend hst

omit [CryptoBytes Bytes] in
public
theorem prepareCreateAddOnlyCommit_valid {leafInd: Nat} (st: TreeKEMState Bytes leafInd)
  (pend: PendingCreateCommit2 Bytes leafInd) (h: prepareCreateAddOnlyCommit st = .success pend) (hst: st.Valid):
  pend.Valid
:= by
  simp only [prepareCreateAddOnlyCommit, Result.pure_eq_success] at h
  subst h
  exact hst

public
theorem finalizeCreateCommit_valid {leafInd: Nat} (pending: PendingCreateCommit2 Bytes leafInd)
  (newGroupContext: GroupContext Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (res: CreateCommitResult Bytes leafInd)
  (h: finalizeCreateCommit pending newGroupContext psks = .success res) (hpend: pending.Valid):
  res.Valid
:= by
  simp only [finalizeCreateCommit, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨_, -, rfl⟩ := h
  exact hpend

end CryptoBytes

end MLS.TreeKEM.API
