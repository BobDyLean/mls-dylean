import MLS.TreeSync.Code.Invariants.UnmergedLeaves
import MLS.TreeSync.Proofs.Operations.Lemmas

/-!
Port of `MLS.TreeSync.Invariants.UnmergedLeaves.Proofs`.

Port-specific differences:
- `unmergedLeavesOk_succ` and `unmergedLeafConsistent_succ` unfold the invariants on a node
  through the child / sibling view for any leaf index `li`,
  so that proofs follow the functions recursing on this view (with `Tree.childInduction li`).
- `leaf_at_tree_add` is in `MLS.TreeSync.Operations.Lemmas` (MLS* has it in both modules).
- The un-add lemmas are commented out in MLS*, and are not ported.
-/

namespace MLS.TreeSync

open Comparse
open MLS

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

@[simp] theorem unmergedLeavesOk_zero (t: TreeSync Bytes tkt 0): unmergedLeavesOk t := by
  simp [unmergedLeavesOk.eq_def]

@[simp] theorem unmergedLeafConsistent_zero (t: TreeSync Bytes tkt 0) (x: UInt32): unmergedLeafConsistent t x := by
  simp [unmergedLeafConsistent.eq_def]

theorem unmergedLeavesOk_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  unmergedLeavesOk t = (
    (match t.nodeContent with
      | none => true
      | some content =>
        content.unmergedLeaves.val.all (fun li => unmergedLeafExists t li.toNat) &&
        content.unmergedLeaves.val.all (unmergedLeafConsistent t) &&
        unmergedLeavesSorted content.unmergedLeaves.val) &&
    unmergedLeavesOk (t.child li) && unmergedLeavesOk (t.sibling li))
:= by
  grind [unmergedLeavesOk.eq_def]

theorem unmergedLeafConsistent_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (x: UInt32):
  unmergedLeafConsistent t x = (
    (match t.nodeContent with
      | none => true
      | some content => !(t.containsLeafIndex x.toNat) || content.unmergedLeaves.val.contains x) &&
    unmergedLeafConsistent (t.child li) x && unmergedLeafConsistent (t.sibling li) x)
:= by
  grind [unmergedLeafConsistent.eq_def]

/-- Port of `unmerged_leaves_ok_tree_create`. -/
theorem unmergedLeavesOk_treeCreate (ln: LeafNode Bytes tkt):
  unmergedLeavesOk (treeCreate ln: TreeSync Bytes tkt 0)
:= by
  simp

/-- Port of `unmerged_leaves_ok_tree_change_path`. -/
theorem unmergedLeavesOk_treeChangePath {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (oln: Option (LeafNode Bytes tkt))
  (h: unmergedLeavesOk t):
  unmergedLeavesOk (treeChangePath t li oln none)
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih => grind [treeChangePath.eq_def, unmergedLeavesOk_succ _ li]

/-- Port of `unmerged_leaves_ok_tree_update`. -/
theorem unmergedLeavesOk_treeUpdate {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt)
  (h: unmergedLeavesOk t):
  unmergedLeavesOk (treeUpdate t li ln)
:=
  unmergedLeavesOk_treeChangePath t li (some ln) h

/-- Port of `unmerged_leaves_ok_tree_remove`. -/
theorem unmergedLeavesOk_treeRemove {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (h: unmergedLeavesOk t):
  unmergedLeavesOk (treeRemove t li)
:=
  unmergedLeavesOk_treeChangePath t li none h

/-- Port of `unmerged_leaves_ok_mk_blank_tree`. -/
theorem unmergedLeavesOk_mkBlankTree (l p: Nat):
  unmergedLeavesOk (mkBlankTree l p: TreeSync Bytes tkt l)
:= by
  induction l generalizing p with
  | zero => simp
  | succ l ih =>
    unfold mkBlankTree mkBlankTreeGeneral
    rw [unmergedLeavesOk.eq_def]
    simp_all [mkBlankTree]

/-- Port of `unmerged_leaves_ok_tree_extend`. -/
theorem unmergedLeavesOk_treeExtend {l: Nat} (t: TreeSync Bytes tkt l) (h: unmergedLeavesOk t):
  unmergedLeavesOk (treeExtend t)
:= by
  grind [treeExtend, unmergedLeavesOk.eq_def, unmergedLeavesOk_mkBlankTree, mkBlankTree]

/-- Port of `unmerged_leaves_ok_tree_truncate`. -/
theorem unmergedLeavesOk_treeTruncate {l: Nat} (t: TreeSync Bytes tkt (l+1)) (h: unmergedLeavesOk t):
  unmergedLeavesOk (treeTruncate t)
:= by
  grind [unmergedLeavesOk.eq_def, treeTruncate]

/-- Port of `unmerged_leaves_sorted_insert_sorted`. -/
theorem unmergedLeavesSorted_insertSorted (x: UInt32) (l: List UInt32) (h: unmergedLeavesSorted l):
  unmergedLeavesSorted (insertSorted x l)
:= by
  induction l <;> grind [unmergedLeavesSorted, insertSorted, List.pairwise_cons]

/-- Port of `unmerged_leaf_consistent_not_in_tree`. -/
theorem unmergedLeafConsistent_of_not_mem {l: Nat} (t: TreeSync Bytes tkt l) (li: UInt32)
  (h: ¬ t.containsLeafIndex li.toNat):
  unmergedLeafConsistent t li
:= by
  induction t using Tree.leftRightInduction <;> grind [unmergedLeafConsistent.eq_def, Tree.containsLeafIndex]

/-- Port of `unmerged_leaf_consistent_tree_add_self`. -/
theorem unmergedLeafConsistent_treeAdd_self {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt l) (h: treeAdd t li lp = .success t') (hli: li < 2^32):
  unmergedLeafConsistent t' li.toUInt32
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih =>
    obtain ⟨newContent, _, h1, rfl, h2, -⟩ := treeAdd_succ t li lp t' h
    have := unmergedLeafConsistent_of_not_mem (t.sibling li) li.toUInt32 (by grind [UInt32.toNat_ofNat_of_lt'])
    cases _: t.nodeContent <;> grind [unmergedLeafConsistent_succ _ li]

/-- Port of `unmerged_leaf_consistent_tree_add_other`. -/
theorem unmergedLeafConsistent_treeAdd_other {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt)
  (li': UInt32) (t': TreeSync Bytes tkt l) (h: treeAdd t li lp = .success t') (h': unmergedLeafConsistent t li'):
  unmergedLeafConsistent t' li'
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih =>
    obtain ⟨newContent, _, h1, rfl, h2, -⟩ := treeAdd_succ t li lp t' h
    grind [unmergedLeafConsistent_succ _ li, Tree.containsLeafIndex]

/-- Port of `unmerged_leaves_ok_tree_add`. -/
theorem unmergedLeavesOk_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt l) (h: treeAdd t li lp = .success t') (hli: t.containsLeafIndex li) (hok: unmergedLeavesOk t):
  unmergedLeavesOk t'
:= by
  induction t using Tree.childInduction li with
  | leaf t => simp
  | node t ih =>
    obtain ⟨newContent, _, h1, rfl, h2, h3⟩ := treeAdd_succ t li lp t' h
    simp only [unmergedLeavesOk_succ _ li, Bool.and_eq_true] at hok ⊢
    have := unmergedLeafConsistent_treeAdd_self t li lp _ h
    have := fun li' => unmergedLeafConsistent_treeAdd_other t li lp li' _ h
    have := fun li' => leafAt_treeAdd t li lp li' _ h hli
    cases _: t.nodeContent <;>
      grind [unmergedLeafExists, Tree.containsLeafIndex, unmergedLeavesSorted_insertSorted]

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `unmerged_leaves_ok_apply_path_aux`. -/
theorem unmergedLeavesOk_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t') (hok: unmergedLeavesOk t):
  unmergedLeavesOk t'
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t => simp
  | node t ih =>
    obtain ⟨newOptContent, _, _, _, h1, rfl, h2⟩ := applyPathAux_succ t li p parentParentHash t' h
    simp only [unmergedLeavesOk_succ _ li, Bool.and_eq_true] at hok ⊢
    have := ih _ _ _ h1 hok.1.2
    cases newOptContent <;> simp_all [applyPathAux_position _ _ _ _ _ h1, unmergedLeavesSorted]

/-- Port of `unmerged_leaves_ok_apply_path`. -/
theorem unmergedLeavesOk_applyPath {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (t': TreeSync Bytes tkt l) (h: applyPath t li p = .success t') (hok: unmergedLeavesOk t):
  unmergedLeavesOk t'
:=
  unmergedLeavesOk_applyPathAux t li p _ t' h hok

end CryptoBytes

end MLS.TreeSync
