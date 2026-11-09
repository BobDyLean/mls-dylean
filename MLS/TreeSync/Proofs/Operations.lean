module

public import MLS.Common.Proofs.Crypto.Derived
public import MLS.Common.Proofs.TreeCommon
public import MLS.TreeSync.Code.Operations
import all MLS.TreeSync.Code.Operations

/-!
Port of `MLS.TreeSync.Operations.Lemmas`, and lemmas unfolding the operations of `MLS.TreeSync.Operations`.

Port-specific differences:
- `treeAdd` and `applyPathAux` return a `Result`: lemmas take the resulting tree `t'`
  with an hypothesis `treeAdd t li lp = .success t'` (MLS*'s `Success? (tree_add t li lp)`).
- `treeAdd_succ` and `applyPathAux_succ` unfold one step of these functions on a node,
  so that proofs by `Tree.childInduction` do not need to reason on the `do` blocks.
-/

namespace MLS.TreeSync

open Comparse
open MLS

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

public
theorem treeAdd_zero (t: TreeSync Bytes tkt 0) (li: Nat) (lp: LeafNode Bytes tkt) (t': TreeSync Bytes tkt 0)
  (h: treeAdd t li lp = .success t'):
  t' = (ChildSiblingView.leaf (some lp) t.position).pack
:= by
  unfold treeAdd at h
  simp_all

public
theorem treeAdd_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (lp: LeafNode Bytes tkt) (t': TreeSync Bytes tkt (l+1))
  (h: treeAdd t li lp = .success t'):
  ∃ newContent newChild,
    treeAdd (t.child li) li lp = .success newChild ∧
    t' = (ChildSiblingView.node newContent newChild (t.sibling li)).pack ∧
    newContent.map (·.unmergedLeaves.val) = t.nodeContent.map (insertSorted li.toUInt32 ·.unmergedLeaves.val) ∧
    (t.nodeContent.isSome → li < 2^32) ∧
    newContent.map (fun c => (c.content, c.parentHash)) = t.nodeContent.map (fun c => (c.content, c.parentHash))
:= by
  unfold treeAdd at h
  simp only [Tree.intoChildSiblingView_eq] at h
  split at h <;> simp at h <;> grind

public
theorem treeAdd_position {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: treeAdd t li lp = .success t'):
  t'.position = t.position
:= by
  induction t using Tree.childInduction li with
  | leaf t => grind [treeAdd_zero t li lp t' h]
  | node t ih =>
    obtain ⟨_, _, h1, rfl, -⟩ := treeAdd_succ t li lp t' h
    grind

grind_pattern treeAdd_position => treeAdd t li lp, t'.position

/-- Port of `leaf_at_tree_add`. -/
public
theorem leafAt_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt) (li': Nat)
  (t': TreeSync Bytes tkt l) (h: treeAdd t li lp = .success t')
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt t' li' = if li = li' then some lp else leafAt t li'
:= by
  induction t, hli, hli' using Tree.commonPathInduction li li' with
  | leaf t => rw [treeAdd_zero t li lp t' h]; unfold leafAt; simp_all
  | _ t =>
    obtain ⟨_, _, h1, rfl, -⟩ := treeAdd_succ t li lp t' h
    grind [leafAt.eq_def]

@[simp]
public
theorem unAddP_position {l: Nat} (t: TreeSync Bytes tkt l) (pred: Nat → Bool):
  (unAddP t pred).position = t.position
:= by
  induction t using Tree.leftRightInduction <;> unfold unAddP <;> simp_all

grind_pattern unAddP_position => (unAddP t pred).position

public
theorem unAddP_zero (t: TreeSync Bytes tkt 0) (pred: Nat → Bool):
  unAddP t pred = (LeftRightView.leaf (if pred t.position then t.leafContent else none) t.position).pack
:= by
  grind [unAddP.eq_def]

/-- `unAddP` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem unAddP_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (pred: Nat → Bool):
  (unAddP t pred).child li = unAddP (t.child li) pred ∧
  (unAddP t pred).sibling li = unAddP (t.sibling li) pred ∧
  (unAddP t pred).nodeContent.map (·.unmergedLeaves.val) =
    t.nodeContent.map (·.unmergedLeaves.val.filter (fun x => pred x.toNat)) ∧
  (unAddP t pred).nodeContent.map (fun c => (c.content, c.parentHash)) =
    t.nodeContent.map (fun c => (c.content, c.parentHash))
:= by
  have e := unAddP.eq_def t pred
  simp only [Tree.intoLeftRightView_eq] at e
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · grind [LeftRightView.child_pack]
  · grind [LeftRightView.child_pack]
  · cases t.nodeContent <;> simp
  · cases t.nodeContent <;> simp

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

theorem computeNewNpAndPh_unmergedLeaves {l: Nat}
  (optExtContent: Option tkt.NodeContent) (sibling: TreeSync Bytes tkt l) (parentParentHash: Bytes)
  (newOptContent: Option (ParentNode Bytes tkt)) (newParentParentHash: Bytes)
  (h: computeNewNpAndPh optExtContent sibling parentParentHash = .success (newOptContent, newParentParentHash)):
  ∀ content ∈ newOptContent, content.unmergedLeaves.val = []
:= by
  unfold computeNewNpAndPh mkMlsBytes Result.error at h
  split at h <;> cases optExtContent <;> simp at h <;> grind

public
theorem computeNewNpAndPh_spec {l: Nat}
  (optExtContent: Option tkt.NodeContent) (sibling: TreeSync Bytes tkt l) (parentParentHash: Bytes)
  (newOptContent: Option (ParentNode Bytes tkt)) (newParentParentHash: Bytes)
  (h: computeNewNpAndPh optExtContent sibling parentParentHash = .success (newOptContent, newParentParentHash)):
  match optExtContent with
  | none => newOptContent = none ∧ newParentParentHash = parentParentHash
  | some extContent =>
    ∃ content, newOptContent = some content ∧
      content.content = extContent ∧ content.parentHash.val = parentParentHash ∧ content.unmergedLeaves.val = [] ∧
      computeParentHash extContent parentParentHash sibling = .success newParentParentHash
:= by
  unfold computeNewNpAndPh mkMlsBytes Result.error at h
  split at h <;> cases optExtContent <;> simp at h <;> grind

public
theorem computeLeafParentHashFromPath_node {PathLeaf: Type} {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent)
  (pNext: Path PathLeaf (Option tkt.NodeContent) l) (parentParentHash: Bytes)
  (newOptContent: Option (ParentNode Bytes tkt)) (newParentParentHash: Bytes)
  (h: computeNewNpAndPh optExtContent (t.sibling li) parentParentHash = .success (newOptContent, newParentParentHash)):
  computeLeafParentHashFromPath t li (.node optExtContent pNext) parentParentHash =
    computeLeafParentHashFromPath (t.child li) li pNext newParentParentHash
:= by
  conv => lhs; unfold computeLeafParentHashFromPath
  simp [h, Bind.bind, Result.bind]

public
theorem computeLeafParentHashFromPath_zero {PathLeaf: Type}
  (t: TreeSync Bytes tkt 0) (li: Nat) (lp: PathLeaf) (parentParentHash: Bytes):
  computeLeafParentHashFromPath t li (.leaf lp) parentParentHash = .success parentParentHash
:= by
  obtain ⟨_, ⟨_⟩⟩ := t
  rfl

public
theorem computeLeafParentHashFromPath_node_eq {PathLeaf: Type} {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent)
  (pNext: Path PathLeaf (Option tkt.NodeContent) l) (parentParentHash: Bytes):
  computeLeafParentHashFromPath t li (.node optExtContent pNext) parentParentHash = (do
    let (_, newParentParentHash) ← computeNewNpAndPh optExtContent (t.sibling li) parentParentHash
    computeLeafParentHashFromPath (t.child li) li pNext newParentParentHash)
:= by
  conv => lhs; unfold computeLeafParentHashFromPath
  simp [Tree.intoChildSiblingView_eq]

public
theorem applyPathAux_node_eq {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes):
  applyPathAux t li (.node optExtContent pNext) parentParentHash = (do
    let (newOptContent, newParentParentHash) ← computeNewNpAndPh optExtContent (t.sibling li) parentParentHash
    let newChild ← applyPathAux (t.child li) li pNext newParentParentHash
    pure (ChildSiblingView.node newOptContent newChild (t.sibling li)).pack)
:= by
  conv => lhs; unfold applyPathAux
  simp [Tree.intoChildSiblingView_eq]

public
theorem pathIsFilterValid_node {PathLeaf: Type} {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent)
  (pNext: Path PathLeaf (Option tkt.NodeContent) l):
  pathIsFilterValid t li (.node optExtContent pNext) =
    ((optExtContent.isSome || isTreeEmpty (t.sibling li)) && pathIsFilterValid (t.child li) li pNext)
:= by
  conv => lhs; unfold pathIsFilterValid
  simp

public
theorem applyPathAux_zero
  (t: TreeSync Bytes tkt 0) (li: Nat) (lp: LeafNode Bytes tkt) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt 0) (h: applyPathAux t li (.leaf lp) parentParentHash = .success t'):
  t' = (ChildSiblingView.leaf (some lp) t.position).pack
:= by
  unfold applyPathAux at h
  simp_all

public
theorem applyPathAux_node {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt (l+1)) (h: applyPathAux t li (.node optExtContent pNext) parentParentHash = .success t'):
  ∃ newOptContent newParentParentHash newChild,
    computeNewNpAndPh optExtContent (t.sibling li) parentParentHash = .success (newOptContent, newParentParentHash) ∧
    applyPathAux (t.child li) li pNext newParentParentHash = .success newChild ∧
    t' = (ChildSiblingView.node newOptContent newChild (t.sibling li)).pack
:= by
  unfold applyPathAux at h
  simp at h
  grind

public
theorem applyPathAux_succ {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (p: PathSync Bytes tkt (l+1)) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt (l+1)) (h: applyPathAux t li p parentParentHash = .success t'):
  ∃ newOptContent newChild pNext newParentParentHash,
    applyPathAux (t.child li) li pNext newParentParentHash = .success newChild ∧
    t' = (ChildSiblingView.node newOptContent newChild (t.sibling li)).pack ∧
    ∀ content ∈ newOptContent, content.unmergedLeaves.val = []
:= by
  cases p
  unfold applyPathAux at h
  simp at h
  grind [computeNewNpAndPh_unmergedLeaves]

public
theorem applyPathAux_position {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t'):
  t'.position = t.position
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t => cases p; unfold applyPathAux at h; simp at h; grind
  | node t ih =>
    obtain ⟨_, _, _, _, h1, rfl, -⟩ := applyPathAux_succ t li p parentParentHash t' h
    grind

grind_pattern applyPathAux_position => applyPathAux t li p parentParentHash, t'.position

/-- Port of `leaf_at_apply_path_aux`. -/
public
theorem leafAt_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes) (li': Nat)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t')
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt t' li' = if li = li' then some p.getPathLeaf else leafAt t li'
:= by
  induction t, hli, hli' using Tree.commonPathInduction li li' generalizing parentParentHash with
  | leaf t =>
    cases p
    rw [applyPathAux_zero t li _ parentParentHash t' h]
    unfold leafAt
    simp_all [Path.getPathLeaf]
  | _ t =>
    cases p with
    | node optExtContent pNext =>
      obtain ⟨_, _, _, -, h1, rfl⟩ := applyPathAux_node t li optExtContent pNext parentParentHash t' h
      grind [leafAt.eq_def, Path.getPathLeaf]

end CryptoBytes

end MLS.TreeSync
