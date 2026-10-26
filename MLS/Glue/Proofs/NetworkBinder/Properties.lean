module

public import MLS.Common.Proofs.Result
public import MLS.Common.Proofs.TreeCommon
public import MLS.Glue.Code.NetworkBinder
public import MLS.Common.Proofs.Crypto.Derived
public import MLS.TreeSync.Symbolic.Parsers
public import MLS.TreeKEM.Code.Parsers

/-!
Port of `MLS.NetworkBinder.Properties` and `MLS.NetworkBinder.Properties.Proofs`.

Port-specific differences:
- Both modules are in this file (`MLS.NetworkBinder.Properties.Proofs` would also be `Proofs/NetworkBinder/Properties.lean`).
- The well-formedness lemmas (MLS*'s `*_pre`, about Comparse's `is_well_formed`) are named `*_wf`;
  the `for_allP` lemmas they use are `List` lemmas in Lean, and are not ported.
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
@[expose]
public
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

@[simp]
public
theorem pathFilteringOk_zero (t: Tree (Option TreeLeaf) (Option TreeNode) 0) (li: Nat)
  (p: Path PathLeaf (Option PathNode) 0):
  pathFilteringOk t li p
:= by
  cases p
  rw [pathFilteringOk.eq_def]
  simp

@[simp]
public
theorem pathFilteringOk_succ {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) (l+1)) (li: Nat)
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
public
theorem pathFilteringOk_uncompressUpdatePath {l: Nat} (li: Nat) (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (updatePath: TreeKEM.UpdatePath Bytes) (res: SparseUpdatePath Bytes l)
  (h: uncompressUpdatePath li t updatePath = .success res):
  pathFilteringOk t li res
:=
  pathFilteringOk_uncompressUpdatePathAux li t _ _ res h

/-- Port of `path_filtering_ok_update_path_to_treesync`. -/
public
theorem pathFilteringOk_updatePathToTreesync {l: Nat} (t: Tree (Option TreeLeaf) (Option TreeNode) l) (li: Nat)
  (p: SparseUpdatePath Bytes l) (h: pathFilteringOk t li p):
  pathFilteringOk t li (updatePathToTreesync p)
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih => cases p with | node opn pNext => cases opn <;> simp_all [updatePathToTreesync] <;> rfl

/-- Port of `path_filtering_ok_update_path_to_treekem`. -/
public
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
public
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
public
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

/-! ## Well-formedness -/

section

variable {Bytes: Type} [BytesLike Bytes] (pred: Bytes → Prop) [BytesCompatiblePred pred]

/-- Port of `ratchet_tree_l_pre`. -/
theorem ratchetTreeL_wf {tkt: TreeKEMTypes Bytes} (nodes: List (Option (Node Bytes tkt)))
  (res: (l: Nat) × {newNodes: List (Option (Node Bytes tkt)) // newNodes.length = 2^(l+1) - 1})
  (hnodes: ∀ n ∈ nodes, (MlsOption.mf (Node.mf tkt)).wf pred n)
  (h: ratchetTreeL nodes = .success res):
  ∀ n ∈ res.2.val, (MlsOption.mf (Node.mf tkt)).wf pred n
:= by
  unfold ratchetTreeL at h
  grind [Result.pure_eq_success, Result.error, Result.internalFailure, MlsOption.mf.wf_eq]

/-- Port of `ratchet_tree_to_treesync_aux_pre`. -/
theorem ratchetTreeToTreesyncAux_wf {tkt: TreeKEMTypes Bytes} (l position: Nat) (nodes: List (Option (Node Bytes tkt)))
  (t: TreeSync Bytes tkt l)
  (hnodes: ∀ n ∈ nodes, (MlsOption.mf (Node.mf tkt)).wf pred n)
  (h: ratchetTreeToTreesyncAux l position nodes = .success t):
  (TreeSync.mf tkt l).wf pred t
:= by
  induction l generalizing position nodes with
  | zero =>
    unfold ratchetTreeToTreesyncAux at h
    split at h <;> grind [Result.pure_eq_success, Result.error, Result.internalFailure, Tree.mf.wf_pack_leaf,
      MlsOption.mf.wf_eq, Node.mf.wf_eq, List.mem_cons_self]
  | succ l ih =>
    unfold ratchetTreeToTreesyncAux at h
    split at h
    · simp only [Result.bind_eq_success] at h
      obtain ⟨left, hleft, right, hright, h⟩ := h
      split at h <;> grind [Result.pure_eq_success, Result.error, Tree.mf.wf_pack_node, MlsOption.mf.wf_eq,
        Node.mf.wf_eq, List.mem_of_mem_take, List.mem_of_mem_drop, List.mem_cons_self]
    · grind [Result.internalFailure]

/-- Port of `ratchet_tree_to_treesync_pre`. -/
public
theorem ratchetTreeToTreesync_wf {tkt: TreeKEMTypes Bytes} (nodes: RatchetTree Bytes tkt)
  (res: (l: Nat) × TreeSync Bytes tkt l)
  (hnodes: (RatchetTree.mf tkt).wf pred nodes)
  (h: ratchetTreeToTreesync nodes = .success res):
  (TreeSync.mf tkt res.1).wf pred res.2
:= by
  simp only [ratchetTreeToTreesync, Result.bind_eq_success, Result.pure_eq_success] at h
  obtain ⟨⟨l, newNodes⟩, hl, t, ht, rfl⟩ := h
  grind [RatchetTree.mf.wf_eq, ratchetTreeL_wf, ratchetTreeToTreesyncAux_wf]

/-- Port of `treesync_to_ratchet_tree_aux_pre`. -/
theorem treesyncToRatchetTreeAux_wf {tkt: TreeKEMTypes Bytes} {l: Nat} (t: TreeSync Bytes tkt l)
  (nodes: List (Option (Node Bytes tkt)))
  (ht: (TreeSync.mf tkt l).wf pred t)
  (h: treesyncToRatchetTreeAux t = .success nodes):
  ∀ n ∈ nodes, (MlsOption.mf (Node.mf tkt)).wf pred n
:= by
  induction l generalizing nodes with
  | zero =>
    rw [Tree.mf.wf_zero] at ht
    unfold treesyncToRatchetTreeAux at h
    rw [Tree.intoLeftRightView_zero] at h
    split at h <;> simp only [Result.pure_eq_success] at h <;> grind [MlsOption.mf.wf_eq, Node.mf.wf_eq]
  | succ l ih =>
    unfold treesyncToRatchetTreeAux at h
    grind [Tree.mf.wf_succ, Result.bind_eq_success, Result.pure_eq_success, MlsOption.mf.wf_eq, Node.mf.wf_eq]

omit [BytesCompatiblePred pred] in
/-- Port of `shrink_ratchet_tree_aux_pre`. -/
theorem shrinkRatchetTreeAux_wf {tkt: TreeKEMTypes Bytes} (nodes shrinkedNodes: List (Option (Node Bytes tkt)))
  (hnodes: ∀ n ∈ nodes, (MlsOption.mf (Node.mf tkt)).wf pred n)
  (h: shrinkRatchetTreeAux nodes = some shrinkedNodes):
  ∀ n ∈ shrinkedNodes, (MlsOption.mf (Node.mf tkt)).wf pred n
:= by
  induction nodes generalizing shrinkedNodes with
  | nil => simp [shrinkRatchetTreeAux] at h
  | cons optH t ih =>
    unfold shrinkRatchetTreeAux at h
    split at h <;> grind

/-- Port of `shrink_ratchet_tree_pre`. -/
theorem shrinkRatchetTree_wf {tkt: TreeKEMTypes Bytes} (nodes: List (Option (Node Bytes tkt)))
  (ratchetTree: RatchetTree Bytes tkt)
  (hnodes: ∀ n ∈ nodes, (MlsOption.mf (Node.mf tkt)).wf pred n)
  (h: shrinkRatchetTree nodes = .success ratchetTree):
  (RatchetTree.mf tkt).wf pred ratchetTree
:= by
  unfold shrinkRatchetTree at h
  split at h <;> grind [mkMlsList_eq_success, RatchetTree.mf.wf_eq, shrinkRatchetTreeAux_wf]

/-- Port of `treesync_to_ratchet_tree_pre`. -/
public
theorem treesyncToRatchetTree_wf {tkt: TreeKEMTypes Bytes} {l: Nat} (t: TreeSync Bytes tkt l)
  (ratchetTree: RatchetTree Bytes tkt)
  (ht: (TreeSync.mf tkt l).wf pred t)
  (h: treesyncToRatchetTree t = .success ratchetTree):
  (RatchetTree.mf tkt).wf pred ratchetTree
:= by
  simp only [treesyncToRatchetTree, Result.bind_eq_success] at h
  grind [shrinkRatchetTree_wf, treesyncToRatchetTreeAux_wf]

/-- Port of `uncompress_update_path_aux_pre`. -/
theorem uncompressUpdatePathAux_wf {TreeLeaf TreeNode: Type} {l: Nat} (li: Nat)
  (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (leafNode: LeafNode Bytes TreeKEM.tkt) (nodes: List (TreeKEM.UpdatePathNode Bytes)) (p: SparseUpdatePath Bytes l)
  (hleafNode: (LeafNode.mf TreeKEM.tkt).wf pred leafNode)
  (hnodes: ∀ n ∈ nodes, TreeKEM.UpdatePathNode.mf.wf pred n)
  (h: uncompressUpdatePathAux li t (leafNode, nodes) = .success p):
  (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p
:= by
  induction t using Tree.childInduction li generalizing nodes with
  | leaf t =>
    rw [uncompressUpdatePathAux.eq_def] at h
    simp only [Tree.intoChildSiblingView_zero] at h
    grind [Result.pure_eq_success, Result.error, Path.mf.wf_leaf]
  | node t ih =>
    rw [uncompressUpdatePathAux.eq_def] at h
    simp only [Tree.intoChildSiblingView_eq] at h
    grind [Result.bind_eq_success, Result.pure_eq_success, Result.error, Path.mf.wf_node, MlsOption.mf.wf_eq,
      List.dropLast_subset, List.mem_of_getLast?]

/-- Port of `uncompress_update_path_pre`. -/
public
theorem uncompressUpdatePath_wf {TreeLeaf TreeNode: Type} {l: Nat} (li: Nat)
  (t: Tree (Option TreeLeaf) (Option TreeNode) l)
  (updatePath: TreeKEM.UpdatePath Bytes) (p: SparseUpdatePath Bytes l)
  (hupdatePath: TreeKEM.UpdatePath.mf.wf pred updatePath)
  (h: uncompressUpdatePath li t updatePath = .success p):
  (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p
:= by
  grind [TreeKEM.UpdatePath.mf.wf_eq, uncompressUpdatePath, uncompressUpdatePathAux_wf]

/-- Port of `update_path_to_treesync_pre`. -/
public
theorem updatePathToTreesync_wf {l: Nat} (p: SparseUpdatePath Bytes l)
  (hp: (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p):
  (PathSync.mf TreeKEM.tkt l).wf pred (updatePathToTreesync p)
:= by
  induction p with
  | leaf ln => simp_all [updatePathToTreesync]
  | node onp pNext ih =>
    cases onp <;> grind [updatePathToTreesync, Path.mf.wf_node, MlsOption.mf.wf_eq, TreeKEM.UpdatePathNode.mf.wf_eq,
      TreeKEM.tkt.mfNodeContent.wf_eq]

/-- Port of `get_path_leaf_pre`. -/
theorem getPathLeaf_wf {Leaf Node: Type} {l: Nat}
  (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node)
  (p: Path Leaf Node l)
  (hp: (Path.mf mfLeaf mfNode l).wf pred p):
  mfLeaf.wf pred p.getPathLeaf
:= by
  induction p <;> grind [Path.getPathLeaf, Path.mf.wf_leaf, Path.mf.wf_node]

/-- Port of `set_path_leaf_pre`. -/
theorem setPathLeaf_wf {LeafIn LeafOut Node: Type} {l: Nat}
  (mfLeafIn: NonExtensibleMessageFormat Bytes LeafIn) (mfLeafOut: NonExtensibleMessageFormat Bytes LeafOut)
  (mfNode: NonExtensibleMessageFormat Bytes Node)
  (p: Path LeafIn Node l) (leaf: LeafOut)
  (hp: (Path.mf mfLeafIn mfNode l).wf pred p)
  (hleaf: mfLeafOut.wf pred leaf):
  (Path.mf mfLeafOut mfNode l).wf pred (p.setPathLeaf leaf)
:= by
  induction p <;> grind [Path.setPathLeaf, Path.mf.wf_leaf, Path.mf.wf_node]

/-- Port of `update_path_to_treekem_pre`. -/
public
theorem updatePathToTreekem_wf {l: Nat} (p: SparseUpdatePath Bytes l)
  (hp: (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p):
  (Path.mf TreeKEM.TreeKEMLeaf.mf (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred (updatePathToTreekem p)
:= by
  have := getPathLeaf_wf pred _ _ p hp
  grind [updatePathToTreekem, setPathLeaf_wf, leafNodeToTreekem, TreeKEM.TreeKEMLeaf.mf.wf_eq,
    LeafNode.mf.wf_eq, LeafNodeData.mf.wf_eq, TreeKEM.tkt.mfLeafContent.wf_eq]

/-- Port of `compress_update_path_aux_pre`. -/
theorem compressUpdatePathAux_wf {l: Nat} (p: SparseUpdatePath Bytes l)
  (hp: (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p):
  (LeafNode.mf TreeKEM.tkt).wf pred (compressUpdatePathAux p).1 ∧
  ∀ n ∈ (compressUpdatePathAux p).2, TreeKEM.UpdatePathNode.mf.wf pred n
:= by
  induction p with
  | leaf => simp_all [compressUpdatePathAux]
  | node pOptData pNext ih => cases pOptData <;> grind [compressUpdatePathAux, Path.mf.wf_node, MlsOption.mf.wf_eq]

/-- Port of `compress_update_path_pre`. -/
public
theorem compressUpdatePath_wf {l: Nat} (p: SparseUpdatePath Bytes l) (updatePath: TreeKEM.UpdatePath Bytes)
  (hp: (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred p)
  (h: compressUpdatePath p = .success updatePath):
  TreeKEM.UpdatePath.mf.wf pred updatePath
:= by
  simp only [compressUpdatePath, Result.bind_eq_success, Result.pure_eq_success, mkMlsList_eq_success] at h
  grind [TreeKEM.UpdatePath.mf.wf_eq, compressUpdatePathAux_wf]

/-- Port of `mls_star_paths_to_update_path_pre`. -/
public
theorem mlsStarPathsToUpdatePath_wf {l: Nat} (psync: PathSync Bytes TreeKEM.tkt l) (pkem: TreeKEM.PathKEM Bytes l)
  (hpsync: (PathSync.mf TreeKEM.tkt l).wf pred psync)
  (hpkem: (Path.mf TreeKEM.TreeKEMLeaf.mf (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred pkem):
  (Path.mf (LeafNode.mf TreeKEM.tkt) (MlsOption.mf TreeKEM.UpdatePathNode.mf) l).wf pred (mlsStarPathsToUpdatePath psync pkem)
:= by
  grind [mlsStarPathsToUpdatePath, setPathLeaf_wf, getPathLeaf_wf]

end

end MLS
