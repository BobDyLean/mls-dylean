import MLS.TreeKEM.Code.API.Tree
import MLS.TreeKEM.Proofs.Invariants

/-!
Proofs about `MLS.TreeKEM.API.Tree`.

MLS*'s tree API is written with refinement types. Here:
- the refinements of `treekem_tree_state` are the predicate `TreeKEMTreeState.Valid`,
  preserved by every function of the API (`*_valid`), under the preconditions of MLS*;
- the refinements of `pending_commit` and `create_commit_result` (`path_filtering_ok`) are the predicates
  `PendingCommit.Valid` and `CreateCommitResult.Valid`, established by the functions building them.
  The refinement `forget_path_secrets path_secrets == generate_forgotten_path_secrets st.tree leaf_ind` is not ported.

MLS*'s preconditions that the proofs do not need are kept as hypotheses (with names starting with `_`).
-/

namespace MLS.TreeKEM.API.Tree

open Comparse
open MLS

variable {Bytes: Type}

/-! ## Predicates -/

/--
The refinements of `treekem_tree_state`: `treekem_invariant tree` and `treekem_priv_invariant tree priv`
(which includes `leaf_ind < pow2 levels`), with the tree at position `0` (MLS*'s `treekem bytes levels 0`).
-/
def _root_.MLS.TreeKEM.TreeKEMTreeState.Valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd): Prop :=
  st.tree.position = 0 ∧ treekemInvariant st.tree ∧ treekemPrivInvariant st.tree leafInd st.priv

/-- The refinement `path_filtering_ok st.tree path_secrets` of `pending_commit`. -/
def PendingCommit.Valid [CryptoBytes Bytes] {leafInd: Nat} {st: TreeKEMTreeState Bytes leafInd} (pend: PendingCommit st): Prop :=
  pathFilteringOk st.tree leafInd pend.pathSecrets

/--
The refinement `path_filtering_ok st.tree update_path` of `create_commit_result`,
and the refinements of its `new_state` (a `treekem_tree_state`).
-/
def CreateCommitResult.Valid [CryptoBytes Bytes] {leafInd: Nat} {st: TreeKEMTreeState Bytes leafInd} (res: CreateCommitResult st): Prop :=
  res.newState.Valid ∧ pathFilteringOk st.tree leafInd res.updatePath

/-! ## Create, welcome, add, update -/

section NoCrypto

theorem create_valid (decKey encKey: Bytes):
  (create decKey encKey).Valid
:= by
  simp [TreeKEMTreeState.Valid, create, treeCreate, treekemInvariant_zero, treekemPrivInvariant, leafAt.eq_def,
    Tree.containsLeafIndex]

theorem add_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (kp: TreeKEMLeaf Bytes) (hst: st.Valid):
  (add st kp).1.Valid
:= by
  unfold add
  split
  · rename_i i hi
    have := findEmptyLeaf_spec _ _ hi
    grind [TreeKEMTreeState.Valid, treeAdd_position, treekemInvariant_treeAdd, treekemPrivInvariant_treeAdd]
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (findEmptyLeaf_treeExtend st.tree)
    have := findEmptyLeaf_spec _ _ hi
    grind [TreeKEMTreeState.Valid, treeAdd_position, treeExtend, treekemInvariant_treeAdd, treekemPrivInvariant_treeAdd,
      treekemInvariant_treeExtend, treekemPrivInvariant_treeExtend]

theorem updateMyself_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes)
  (hst: st.Valid):
  (updateMyself st lp leafDecryptionKey).Valid
:= by
  unfold TreeKEMTreeState.Valid treekemPrivInvariant at *
  grind [updateMyself, treeUpdate, treekemInvariant_treeChangePath, leafAt_treeChangePath, Tree.containsLeafIndex]

/-- MLS* requires `i < pow2 st.levels` (here `hi`) and `i <> leaf_ind`. -/
theorem updateOther_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (lp: TreeKEMLeaf Bytes) (i: Nat)
  (hi: st.tree.containsLeafIndex i) (hne: i ≠ leafInd) (hst: st.Valid):
  (updateOther st lp i).Valid
:= by
  unfold TreeKEMTreeState.Valid treekemPrivInvariant at *
  simp only [updateOther, treeUpdate]
  grind [treekemInvariant_treeChangePath, leafAt_treeChangePath, Tree.containsLeafIndex]

/-! ## Remove -/

theorem truncateOne_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (st': {res: TreeKEMTreeState Bytes leafInd // res.levels + 1 = st.levels})
  (h: truncateOne st = some st') (hst: st.Valid):
  st'.val.Valid
:= by
  unfold truncateOne at h
  split at h
  · simp at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      unfold TreeKEMTreeState.Valid at *
      grind [treeTruncate, treekemInvariant_treeTruncate, treekemPrivInvariant_treeTruncate]
    · simp at h

theorem fullyTruncate_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (hst: st.Valid):
  (fullyTruncate st).Valid
:= by
  rw [fullyTruncate]
  split
  · rename_i st' hst' h
    exact fullyTruncate_valid st' (truncateOne_valid st ⟨st', hst'⟩ h hst)
  · exact hst
termination_by st.levels
decreasing_by grind

/-- MLS* requires `i < pow2 st.levels` (here `hi`) and `i <> leaf_ind`. -/
theorem remove_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (i: Nat)
  (hi: st.tree.containsLeafIndex i) (hne: i ≠ leafInd) (hst: st.Valid):
  (remove st i).Valid
:= by
  apply fullyTruncate_valid
  unfold TreeKEMTreeState.Valid treekemPrivInvariant at *
  simp only [removeAux, treeRemove]
  grind [treekemInvariant_treeChangePath, leafAt_treeChangePath, Tree.containsLeafIndex]

end NoCrypto

section CryptoBytes

variable [CryptoBytes Bytes]

/-! ## Welcome -/

/--
MLS* requires `treekem_invariant t`, `leaf_ind < pow2 l` and `Some? (leaf_at t leaf_ind)`,
with `t` at position `0` (MLS*'s `treekem bytes l 0`).
-/
theorem welcome_valid {l: Nat} (t: TreeKEM Bytes l) (leafDecryptionKey: Bytes) (optPathSecretAndInviterInd: Option (Bytes × Nat))
  (leafInd: Nat) (st: TreeKEMTreeState Bytes leafInd)
  (h: welcome t leafDecryptionKey optPathSecretAndInviterInd leafInd = .success st)
  (hpos: t.position = 0) (hinv: treekemInvariant t) (hli: t.containsLeafIndex leafInd) (hleaf: (leafAt t leafInd).isSome):
  st.Valid
:= by
  unfold welcome at h
  have: ∃ priv, { levels := l, tree := t, priv } = st := by
    split at h
    · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
      grind
    · split at h
      · simp [Result.error] at h
      · split at h
        · simp [Result.error] at h
        · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
          grind
  obtain ⟨priv, rfl⟩ := this
  exact ⟨hpos, hinv, hli, hleaf⟩

/-! ## Process commit -/

/--
MLS* requires `li < pow2 st.levels` (here `hli`), `li <> leaf_ind`, `path_filtering_ok st.tree p`
and `~(List.Tot.memP leaf_ind excluded_leaves)`.
-/
theorem commit_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (li: Nat) (p: PathKEM Bytes st.levels)
  (excludedLeaves: List Nat) (groupContext: GroupContext Bytes) (res: TreeKEMTreeState Bytes leafInd) (commitSecret: Bytes)
  (h: commit st li p excludedLeaves groupContext = .success (res, commitSecret))
  (hli: st.tree.containsLeafIndex li) (_hne: li ≠ leafInd) (_hfilter: pathFilteringOk st.tree li p)
  (_hexcluded: leafInd ∉ excludedLeaves) (hst: st.Valid):
  res.Valid
:= by
  unfold commit at h
  dsimp only at h
  split at h
  · simp [Result.error] at h
  · simp only [Result.bind_eq_success] at h
    obtain ⟨⟨_, _⟩, -, h⟩ := h
    obtain ⟨⟨newPriv, _⟩, -, rfl, -⟩ := h
    unfold TreeKEMTreeState.Valid treekemPrivInvariant at *
    grind [treeApplyPath_position, treekemInvariant_treeApplyPath, leafAt_treeApplyPath, Tree.containsLeafIndex]

/-! ## Create commit -/

theorem prepareCreateCommit_valid {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (rand: Randomness Bytes)
  (pend: PendingCommit st) (prePath: PrePathKEM Bytes st.levels)
  (h: prepareCreateCommit st rand = .success (pend, prePath)):
  pend.Valid
:= by
  simp only [prepareCreateCommit, Result.bind_eq_success] at h
  obtain ⟨_, -, _, -, ⟨pathSecrets, commitSecret⟩, h1, _, -, rfl, -⟩ := h
  exact pathFilteringOk_generatePathSecrets _ _ _ _ _ _ h1

theorem finalizeCreateCommit_valid {leafInd: Nat} {st: TreeKEMTreeState Bytes leafInd}
  (pending: PendingCommit st) (addedLeaves: List Nat) (groupContext: GroupContext Bytes) (randomness: Randomness Bytes)
  (res: CreateCommitResult st)
  (h: finalizeCreateCommit pending addedLeaves groupContext randomness = .success res)
  (hpend: pending.Valid) (hst: st.Valid):
  res.Valid
:= by
  simp only [finalizeCreateCommit, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨⟨updatePath, newPriv⟩, h1, _, -, rfl⟩ := h
  have := pathFilteringOk_encryptPathSecrets st.tree _ leafInd _ _ _ _ _ h1 (by simp [unAdd]) hpend
  unfold CreateCommitResult.Valid TreeKEMTreeState.Valid at *
  grind [treeApplyPath_position, treekemInvariant_treeApplyPath, treekemPrivInvariant_treeApplyPath, treekemPrivInvariant]

end CryptoBytes

end MLS.TreeKEM.API.Tree
