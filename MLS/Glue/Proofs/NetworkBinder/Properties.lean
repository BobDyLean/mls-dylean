import MLS.Common.Proofs.Result
import MLS.Common.Proofs.TreeCommon
import MLS.Glue.Code.NetworkBinder

/-!
Port of `MLS.NetworkBinder.Properties` and `MLS.NetworkBinder.Properties.Proofs`.

Port-specific differences:
- Both modules are in this file (`MLS.NetworkBinder.Properties.Proofs` would also be `Proofs/NetworkBinder/Properties.lean`).
- The well-formedness lemmas of `MLS.NetworkBinder.Properties.Proofs` (`*_pre`, about Comparse's `is_well_formed`,
  used by the symbolic proofs) are not ported.
-/

namespace MLS

open Comparse
open MLS.TreeSync

/-! ## Path filtering definition -/

/--
Port of `path_filtering_ok`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def pathFilteringOk {TreeLeaf TreeNode PathLeaf PathNode: Type} {l: Nat}
  (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat) (p: Path PathLeaf (Option PathNode) l): Bool
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf _ => true
  | .node _ child sibling, .node newOpn pNext =>
    let nodeOk := newOpn.isNone == isTreeEmpty sibling
    nodeOk && pathFilteringOk child li pNext
termination_by l

section

variable {TreeLeaf TreeNode PathLeaf PathNode: Type}

@[simp] theorem pathFilteringOk_zero (t: Tree (Option TreeLeaf) (Option TreeNode) 0) (li: Nat)
  (p: Path PathLeaf (Option PathNode) 0):
  pathFilteringOk t li p
:= by
  cases p
  rw [pathFilteringOk.eq_def]
  simp

@[simp] theorem pathFilteringOk_succ {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) (l+1)) (li: Nat)
  (opn: Option PathNode) (pNext: Path PathLeaf (Option PathNode) l):
  pathFilteringOk t li (.node opn pNext) = ((opn.isNone == isTreeEmpty (t.sibling li)) && pathFilteringOk (t.child li) li pNext)
:= by
  rw [pathFilteringOk.eq_def]
  simp

/-- Port of `path_filtering_ok_set_path_leaf`. -/
theorem pathFilteringOk_setPathLeaf {PathLeaf': Type} {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: Path PathLeaf (Option PathNode) l) (lp: PathLeaf')
  (h: pathFilteringOk t li p):
  pathFilteringOk t li (p.setPathLeaf lp)
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih => cases p; simp_all [Path.setPathLeaf]

end

section

variable {Bytes: Type} [BytesLike Bytes] {TreeLeaf TreeNode: Type}

/-! ## Path filtering invariants -/

/-- Port of `path_filtering_ok_uncompress_update_path_aux`. -/
theorem pathFilteringOk_uncompressUpdatePathAux {l: Nat} (li: Nat) (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (leafNode: LeafNode Bytes TreeKEM.tkt) (nodes: List (TreeKEM.UpdatePathNode Bytes)) (res: SparseUpdatePath Bytes l)
  (h: uncompressUpdatePathAux li t (leafNode, nodes) = .success res):
  pathFilteringOk t li res
:= by
  induction t using Tree.childInduction li generalizing nodes with
  | leaf t => simp
  | node t ih =>
    rw [uncompressUpdatePathAux.eq_def] at h
    simp only [Tree.intoChildSiblingView_eq] at h
    split at h
    · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
      obtain ⟨pNext, h1, rfl⟩ := h
      simp_all [ih _ _ h1]
    · split at h
      · simp [Result.error] at h
      · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
        obtain ⟨pNext, h1, rfl⟩ := h
        simp_all [ih _ _ h1]

/-- Port of `path_filtering_ok_uncompress_update_path`. -/
theorem pathFilteringOk_uncompressUpdatePath {l: Nat} (li: Nat) (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (updatePath: TreeKEM.UpdatePath Bytes) (res: SparseUpdatePath Bytes l)
  (h: uncompressUpdatePath li t updatePath = .success res):
  pathFilteringOk t li res
:=
  pathFilteringOk_uncompressUpdatePathAux li t _ _ res h

/-- Port of `path_filtering_ok_update_path_to_treesync`. -/
theorem pathFilteringOk_updatePathToTreesync {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: SparseUpdatePath Bytes l) (h: pathFilteringOk t li p):
  pathFilteringOk t li (updatePathToTreesync p)
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih => cases p with | node opn pNext => cases opn <;> simp_all [updatePathToTreesync] <;> rfl

/-- Port of `path_filtering_ok_update_path_to_treekem`. -/
theorem pathFilteringOk_updatePathToTreekem {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: SparseUpdatePath Bytes l) (h: pathFilteringOk t li p):
  pathFilteringOk t li (updatePathToTreekem p)
:=
  pathFilteringOk_setPathLeaf t li p _ h

/-! ## Correctness of compression / decompression -/

/-- Port of `compress_uncompress_update_path_aux`. -/
theorem compress_uncompress_updatePathAux {l: Nat} (li: Nat) (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (leafNode: LeafNode Bytes TreeKEM.tkt) (nodes: List (TreeKEM.UpdatePathNode Bytes)) (p: SparseUpdatePath Bytes l)
  (h: uncompressUpdatePathAux li t (leafNode, nodes) = .success p):
  compressUpdatePathAux p = (leafNode, nodes)
:= by
  induction t using Tree.childInduction li generalizing nodes with
  | leaf t =>
    rw [uncompressUpdatePathAux.eq_def] at h
    simp only [Tree.intoChildSiblingView_zero] at h
    split at h
    · simp [Result.error] at h
    · simp only [Result.pure_eq_success] at h
      subst h
      simp_all [compressUpdatePathAux]
  | node t ih =>
    rw [uncompressUpdatePathAux.eq_def] at h
    simp only [Tree.intoChildSiblingView_eq] at h
    split at h
    · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
      obtain ⟨pNext, h1, rfl⟩ := h
      simp [compressUpdatePathAux, ih _ _ h1]
    · split at h
      · simp [Result.error] at h
      · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
        obtain ⟨pNext, h1, rfl⟩ := h
        simp [compressUpdatePathAux]
        grind [List.getLast?_eq_some_iff]

/-- Port of `compress_uncompress_update_path`. -/
theorem compress_uncompress_updatePath {l: Nat} (li: Nat) (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (updatePath: TreeKEM.UpdatePath Bytes) (p: SparseUpdatePath Bytes l)
  (h: uncompressUpdatePath li t updatePath = .success p):
  compressUpdatePath p = .success updatePath
:= by
  have := compress_uncompress_updatePathAux li t _ _ p h
  obtain ⟨leafNode, ⟨nodes, hnodes⟩⟩ := updatePath
  simp_all [compressUpdatePath, mkMlsList]

/-- Port of `uncompress_compress_update_path_aux`. -/
theorem uncompress_compress_updatePathAux {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: SparseUpdatePath Bytes l) (h: pathFilteringOk t li p):
  uncompressUpdatePathAux li t (compressUpdatePathAux p) = .success p
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    cases p
    rw [uncompressUpdatePathAux.eq_def]
    simp [compressUpdatePathAux]
  | node t ih =>
    cases p with | node opn pNext =>
    simp only [pathFilteringOk_succ, Bool.and_eq_true] at h
    rw [uncompressUpdatePathAux.eq_def]
    cases opn <;> simp_all [compressUpdatePathAux, Bind.bind, Result.bind]

/-- Port of `uncompress_compress_update_path`. -/
theorem uncompress_compress_updatePath {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: SparseUpdatePath Bytes l) (updatePath: TreeKEM.UpdatePath Bytes)
  (h: pathFilteringOk t li p) (hc: compressUpdatePath p = .success updatePath):
  uncompressUpdatePath li t updatePath = .success p
:= by
  simp only [compressUpdatePath, Result.bind_eq_success, Result.pure_eq_success, mkMlsList] at hc
  split at hc
  · obtain ⟨_, h1, rfl⟩ := hc
    simp only [Result.pure_eq_success] at h1
    subst h1
    exact uncompress_compress_updatePathAux t li p h
  · simp [Result.error] at hc

end

end MLS
