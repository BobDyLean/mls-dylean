module

public import MLS.TreeSync.Code.Invariants.ValidLeaves
public import MLS.TreeSync.Proofs.Operations
import all MLS.TreeSync.Code.Invariants.ValidLeaves
import all MLS.TreeSync.Code.Operations
import all MLS.Common.Code.TreeCommon

/-!
Port of `MLS.TreeSync.Invariants.ValidLeaves.Proofs`.

Port-specific differences:
- `validLeavesInvariant_succ` unfolds the invariant on a node through the child / sibling view for any leaf index `li`,
  so that proofs follow the functions recursing on this view (with `Tree.childInduction li`).
- Leaf signatures depend on the leaf index: lemmas adding a leaf at `li` take a `t.containsLeafIndex li` hypothesis
  (implicit in MLS*'s `li: leaf_index l i`).
- `validLeavesInvariant_treeChangePath` factors the proofs for `treeUpdate` and `treeRemove`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

public
theorem validLeavesInvariant_zero (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt 0):
  validLeavesInvariant groupId t = (
    match t.leafContent with
    | none => true
    | some ln => leafIsValid ln groupId t.position)
:= by
  grind [validLeavesInvariant.eq_def]

public
theorem validLeavesInvariant_succ (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  validLeavesInvariant groupId t =
    (validLeavesInvariant groupId (t.child li) && validLeavesInvariant groupId (t.sibling li))
:= by
  grind [validLeavesInvariant.eq_def]

/-- Port of `valid_leaves_invariant_tree_create`. -/
public
theorem validLeavesInvariant_treeCreate (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt)
  (h: leafIsValid ln groupId 0):
  validLeavesInvariant groupId (treeCreate ln: TreeSync Bytes tkt 0)
:= by
  grind [validLeavesInvariant_zero, treeCreate]

theorem validLeavesInvariant_treeChangePath (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (oln: Option (LeafNode Bytes tkt))
  (hli: t.containsLeafIndex li) (hln: ∀ ln ∈ oln, leafIsValid ln groupId li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId (treeChangePath t li oln none)
:= by
  induction t using Tree.childInduction li with
  | leaf t => grind [treeChangePath.eq_def, validLeavesInvariant_zero, Tree.containsLeafIndex]
  | node t ih => grind [treeChangePath.eq_def, validLeavesInvariant_succ _ _ li]

/--
Port of `valid_leaves_invariant_tree_update`.
MLS* requires `ln.data.source == LNS_update`; this hypothesis is not needed here.
-/
public
theorem validLeavesInvariant_treeUpdate (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ln: LeafNode Bytes tkt)
  (hli: t.containsLeafIndex li) (hln: leafIsValid ln groupId li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId (treeUpdate t li ln)
:= by
  apply validLeavesInvariant_treeChangePath groupId t li (some ln) <;> grind

/-- Port of `valid_leaves_invariant_tree_remove`. -/
public
theorem validLeavesInvariant_treeRemove (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (hli: t.containsLeafIndex li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId (treeRemove t li)
:= by
  apply validLeavesInvariant_treeChangePath groupId t li none <;> grind

/--
Port of `valid_leaves_invariant_tree_add`.
MLS* requires `ln.data.source == LNS_key_package`; this hypothesis is not needed here.
-/
public
theorem validLeavesInvariant_treeAdd (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ln: LeafNode Bytes tkt) (t': TreeSync Bytes tkt l) (h: treeAdd t li ln = .success t')
  (hli: t.containsLeafIndex li) (hln: leafIsValid ln groupId li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId t'
:= by
  induction t using Tree.childInduction li with
  | leaf t => grind [treeAdd_zero t li ln t' h, validLeavesInvariant_zero, Tree.containsLeafIndex]
  | node t ih =>
    obtain ⟨_, _, h1, rfl, -⟩ := treeAdd_succ t li ln t' h
    grind [validLeavesInvariant_succ _ _ li]

/-- Port of `valid_leaves_invariant_apply_path_aux`. -/
theorem validLeavesInvariant_applyPathAux (groupId: MlsBytes Bytes) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t')
  (hli: t.containsLeafIndex li) (hln: leafIsValid p.getPathLeaf groupId li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId t'
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p
    grind [applyPathAux_zero t li _ parentParentHash t' h, validLeavesInvariant_zero, Tree.containsLeafIndex, Path.getPathLeaf]
  | node t ih =>
    cases p with | node optExtContent pNext =>
    obtain ⟨_, _, _, -, h1, rfl⟩ := applyPathAux_node t li optExtContent pNext parentParentHash t' h
    grind [validLeavesInvariant_succ _ _ li, Path.getPathLeaf]

/-- Port of `valid_leaves_invariant_apply_path`. -/
public
theorem validLeavesInvariant_applyPath (groupId: MlsBytes Bytes) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (t': TreeSync Bytes tkt l)
  (h: applyPath t li p = .success t')
  (hli: t.containsLeafIndex li) (hln: leafIsValid p.getPathLeaf groupId li) (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId t'
:=
  validLeavesInvariant_applyPathAux groupId t li p _ t' h hli hln hinv

/-- Port of `valid_leaves_invariant_mk_blank_tree`. -/
theorem validLeavesInvariant_mkBlankTree (groupId: MlsBytes Bytes) (l p: Nat):
  validLeavesInvariant groupId (mkBlankTree l p: TreeSync Bytes tkt l)
:= by
  induction l generalizing p with
  | zero => grind [validLeavesInvariant_zero, mkBlankTree, mkBlankTreeGeneral]
  | succ l ih =>
    unfold mkBlankTree mkBlankTreeGeneral
    rw [validLeavesInvariant.eq_def]
    simp_all [mkBlankTree]

/-- Port of `valid_leaves_invariant_tree_extend`. -/
public
theorem validLeavesInvariant_treeExtend (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l)
  (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId (treeExtend t)
:= by
  grind [treeExtend, validLeavesInvariant_succ _ _ t.position, validLeavesInvariant_mkBlankTree, mkBlankTree]

/--
Port of `valid_leaves_invariant_tree_truncate`.
MLS* requires `is_tree_empty (TNode?.right t)`; this hypothesis is not needed here.
-/
public
theorem validLeavesInvariant_treeTruncate (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt (l+1))
  (hinv: validLeavesInvariant groupId t):
  validLeavesInvariant groupId (treeTruncate t)
:= by
  grind [treeTruncate, validLeavesInvariant.eq_def]

end MLS.TreeSync
