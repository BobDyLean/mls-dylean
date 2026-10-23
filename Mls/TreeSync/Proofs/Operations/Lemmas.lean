import Mls.Common.Proofs.Result.Lemmas
import Mls.Common.Proofs.TreeCommon.Lemmas
import Mls.TreeSync.Code.Operations

/-!
Port of `MLS.TreeSync.Operations.Lemmas`, and lemmas unfolding the operations of `Mls.TreeSync.Operations`.

Port-specific differences:
- `treeAdd` and `applyPathAux` return a `Result`: lemmas take the resulting tree `t'`
  with an hypothesis `treeAdd t li lp = .success t'` (MLS*'s `Success? (tree_add t li lp)`).
- `treeAdd_succ` and `applyPathAux_succ` unfold one step of these functions on a node,
  so that proofs by `Tree.childInduction` do not need to reason on the `do` blocks.
-/

namespace Mls.TreeSync

open Comparse
open Mls

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

theorem treeAdd_zero (t: TreeSync Bytes tkt 0) (li: Nat) (lp: LeafNode Bytes tkt) (t': TreeSync Bytes tkt 0)
  (h: treeAdd t li lp = .success t'):
  t' = (ChildSiblingView.leaf (some lp) t.position).pack
:= by
  unfold treeAdd at h
  simp_all

theorem treeAdd_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (lp: LeafNode Bytes tkt) (t': TreeSync Bytes tkt (l+1))
  (h: treeAdd t li lp = .success t'):
  ∃ newContent newChild,
    treeAdd (t.child li) li lp = .success newChild ∧
    t' = (ChildSiblingView.node newContent newChild (t.sibling li)).pack ∧
    newContent.map (·.unmergedLeaves.val) = t.nodeContent.map (insertSorted li.toUInt32 ·.unmergedLeaves.val) ∧
    (t.nodeContent.isSome → li < 2^32)
:= by
  unfold treeAdd at h
  simp only [Tree.intoChildSiblingView_eq] at h
  split at h <;> simp at h <;> grind

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

end CryptoBytes

end Mls.TreeSync
