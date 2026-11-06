module

public import MLS.TreeSync.Code.Invariants.ParentHash
public import MLS.TreeSync.Proofs.Invariants.UnmergedLeaves
import all MLS.TreeSync.Code.Invariants.UnmergedLeaves
import all MLS.TreeSync.Code.Invariants.ParentHash
import all MLS.TreeSync.Code.Operations
import all MLS.Common.Code.TreeCommon

/-!
Port of `MLS.TreeSync.Invariants.ParentHash.Proofs`.

Port-specific differences:
- `node_index_inside_tree` is `Tree.containsNodeIndex` (as `leaf_index_inside_tree` is `Tree.containsLeafIndex`).
- `is_subtree_of` is the inductive `Tree.IsSubtreeOf`, in the namespace `MLS` as it is not specific to TreeSync.
  MLS*'s conditions `ld <= lp` and `leaf_index_inside lp ip id` are consequences of it
  (`Tree.IsSubtreeOf.le`, `Tree.IsSubtreeOf.containsLeafIndex`).
- As in `MLS.TreeSync.Invariants.ParentHash`, the "parent" tree `p` has height `lp+1`,
  so MLS*'s `ld < lp` is `ld ≤ lp`.
  Lemmas relating `d` and `p` take a hypothesis `d.IsSubtreeOf p`, which MLS* gets from the tree index arithmetic
  (`leaf_index_same_side`).
- `find_parent_hash_link_aux` and `find_parent_hash_link` are not ported:
  the subtree they compute is the witness of existential statements
  (`exists_subtree_applyPathAux` and `nodeHasParentHashLinkP_applyPathAux`).
  `find_parent_hash_link_last_update` and `find_parent_hash_link_parent_hash` take the subtree as an argument,
  with the properties of the witness they need as hypotheses.
- `last_update_set_eqP_imply_eq` (and the sortedness lemmas) do not need the hypothesis `node_indices_are_leaf_indices`
  on the two lists, only on `last_update_lhs`.
- Lemmas about `tree_add` take the resulting tree with an hypothesis `treeAdd t li content = .success t'`
  (MLS*'s `Success? (tree_add t li content)`).
-/

namespace MLS

variable {Leaf Node: Type}

/-- Port of `node_index_inside_tree`. -/
@[expose]
public
def Tree.containsNodeIndex {l: Nat} (t: Tree Leaf Node l) (x: NodeIndex): Bool :=
  x.levels ≤ l && t.containsLeafIndex x.position

/--
Port of `is_subtree_of`.
`d` is a subtree of `p`: either `d = p`, or `d` is a subtree of the child of `p` containing `d`.
-/
public
inductive Tree.IsSubtreeOf {ld: Nat} (d: Tree Leaf Node ld): {lp: Nat} → Tree Leaf Node lp → Prop
  | refl: d.IsSubtreeOf d
  | child {lp: Nat} (p: Tree Leaf Node (lp+1)): d.IsSubtreeOf (p.child d.position) → d.IsSubtreeOf p

grind_pattern Tree.IsSubtreeOf.refl => d.IsSubtreeOf d

grind_pattern Tree.IsSubtreeOf.child => d.IsSubtreeOf (p.child d.position)

namespace Tree.IsSubtreeOf

public
theorem le {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp} (h: d.IsSubtreeOf p): ld ≤ lp := by
  induction h <;> grind

grind_pattern Tree.IsSubtreeOf.le => d.IsSubtreeOf p

/-- The leaves of a subtree are leaves of the tree. -/
public
theorem mem {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp} (h: d.IsSubtreeOf p) {li: Nat}
  (hli: d.containsLeafIndex li):
  p.containsLeafIndex li
:= by
  induction h <;> grind

grind_pattern Tree.IsSubtreeOf.mem =>
  d.containsLeafIndex li,
  d.IsSubtreeOf p

public
theorem containsLeafIndex {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp} (h: d.IsSubtreeOf p):
  p.containsLeafIndex d.position
:= by
  grind [mem]

grind_pattern Tree.IsSubtreeOf.containsLeafIndex => d.IsSubtreeOf p

/-- A subtree of a node, smaller than it, is a subtree of the child containing it. -/
public
theorem child_of_le {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node (lp+1)} (h: d.IsSubtreeOf p) (hl: ld ≤ lp):
  d.IsSubtreeOf (p.child d.position)
:= by
  cases h with
  | refl => grind
  | child _ h => exact h

grind_pattern Tree.IsSubtreeOf.child_of_le =>
  d.IsSubtreeOf p,
  p.child d.position

/-- A subtree of the child for `li` containing `li` is a subtree of the tree. -/
public
theorem of_child {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node (lp+1)} {li: Nat}
  (h: d.IsSubtreeOf (p.child li)):
  d.IsSubtreeOf p
:= by
  grind [Tree.IsSubtreeOf.child]

grind_pattern Tree.IsSubtreeOf.of_child => d.IsSubtreeOf (p.child li)

/-- A subtree of the sibling for `li` is a subtree of the tree. -/
theorem of_sibling {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node (lp+1)} {li: Nat}
  (h: d.IsSubtreeOf (p.sibling li)):
  d.IsSubtreeOf p
:= by
  grind [Tree.IsSubtreeOf.child]

grind_pattern Tree.IsSubtreeOf.of_sibling => d.IsSubtreeOf (p.sibling li)

public
theorem trans {le ld lp: Nat} {e: Tree Leaf Node le} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp}
  (h1: e.IsSubtreeOf d) (h2: d.IsSubtreeOf p):
  e.IsSubtreeOf p
:= by
  induction h2 <;> grind

/-- Port of `is_subtree_of_left_right`, through the child / sibling view. -/
theorem child_sibling {ld lp: Nat} {d: Tree Leaf Node (ld+1)} {p: Tree Leaf Node lp} (h: d.IsSubtreeOf p) (li: Nat):
  (d.child li).IsSubtreeOf p ∧ (d.sibling li).IsSubtreeOf p
:= by
  constructor <;> apply trans (d := d) <;> grind [of_child, of_sibling]

/-- Port of `leaf_at_subtree`. -/
public
theorem leafAt_eq {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp} (h: d.IsSubtreeOf p) {li: Nat}
  (hli: d.containsLeafIndex li):
  leafAt p li = leafAt d li
:= by
  induction h with
  | refl => rfl
  | child p h ih =>
    grind [leafAt.eq_def]

grind_pattern Tree.IsSubtreeOf.leafAt_eq =>
  leafAt d li,
  d.IsSubtreeOf p

end Tree.IsSubtreeOf

end MLS

namespace MLS.TreeSync

open Comparse
open MLS

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-! ## Misc lemmas -/

/-- Port of `mem_ul_eq`. -/
public
theorem memUl_iff (x: Nat) (l: List UInt32): memUl x l ↔ ∃ y ∈ l, y.toNat = x := by
  induction l <;> grind [memUl]

/-- Port of `mem_ul_insert_sorted`. -/
theorem memUl_insertSorted (x: UInt32) (l: List UInt32) (elem: Nat):
  memUl elem (insertSorted x l) ↔ elem = x.toNat ∨ memUl elem l
:= by
  grind [memUl_iff]

grind_pattern memUl_insertSorted => memUl elem (insertSorted x l)

/-- Port of `mem_ul_filter`. -/
theorem memUl_filter (p: UInt32 → Bool) (l: List UInt32) (x: Nat):
  memUl x (l.filter p) ↔ ∃ y ∈ l, y.toNat = x ∧ p y
:= by
  grind [memUl_iff]

grind_pattern memUl_filter => memUl x (l.filter p)

/-- Port of `mem_unmerged_resolution_eq`. -/
public
theorem mem_unmergedResolution (l: List UInt32) (x: NodeIndex):
  x ∈ unmergedResolution l ↔ x.levels = 0 ∧ memUl x.position l
:= by
  obtain ⟨xl, xp⟩ := x
  grind [unmergedResolution, NodeIndex.ofLeafIndex, memUl_iff]

grind_pattern mem_unmergedResolution => x ∈ unmergedResolution l

/-! ## `set_eqP` -/

/-- Port of `set_eqP`. -/
public
def SetEqP {α: Type} (l1 l2: List α): Prop :=
  ∀ x, x ∈ l1 ↔ x ∈ l2

/-- Port of `set_eq_to_set_eqP` and `set_eqP_to_set_eq`. -/
theorem setEq_iff {α: Type} [DecidableEq α] (l1 l2: List α): setEq l1 l2 ↔ SetEqP l1 l2 := by
  grind [setEq, setEqualMem, SetEqP]

/-! ## Unfolding the definitions -/

public
theorem resolution_zero (t: TreeSync Bytes tkt 0):
  resolution t = if t.leafContent.isSome then [t.nodeIndex] else []
:= by
  obtain ⟨p, ⟨c⟩⟩ := t
  cases c <;> rfl

public
theorem resolution_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  resolution t =
    match t.nodeContent with
    | none => resolution t.left ++ resolution t.right
    | some content => t.nodeIndex :: unmergedResolution content.unmergedLeaves.val
:= by
  obtain ⟨p, bt⟩ := t
  cases bt with | node c L R => cases c <;> rfl

/-- Membership in the resolution of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem mem_resolution_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (x: NodeIndex):
  x ∈ resolution t ↔
    match t.nodeContent with
    | none => x ∈ resolution (t.child li) ∨ x ∈ resolution (t.sibling li)
    | some content => x = t.nodeIndex ∨ x ∈ unmergedResolution content.unmergedLeaves.val
:= by
  grind [resolution_succ]

/-- The resolution of a blank node whose sibling for `li` has an empty resolution. -/
public
theorem resolution_succ_of_resolution_sibling {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat)
  (hc: t.nodeContent = none) (hs: resolution (t.sibling li) = []):
  resolution t = resolution (t.child li)
:= by
  grind [resolution_succ]

public
theorem unmergedLeavesOk_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)) (h: unmergedLeavesOk t):
  unmergedLeavesOk t.left ∧ unmergedLeavesOk t.right
:= by
  have := unmergedLeavesOk_succ t t.position
  grind

public
theorem unmergedLeavesOk_child_sibling {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (h: unmergedLeavesOk t):
  unmergedLeavesOk (t.child li) ∧ unmergedLeavesOk (t.sibling li)
:= by
  grind [unmergedLeavesOk_succ]

/-- What `unmergedLeavesOk` says about the unmerged leaves of the root. -/
public
theorem unmergedLeavesOk_content {l: Nat} (t: TreeSync Bytes tkt (l+1)) (content: ParentNode Bytes tkt)
  (hc: t.nodeContent = some content) (h: unmergedLeavesOk t):
  (∀ x ∈ content.unmergedLeaves.val, t.containsLeafIndex x.toNat ∧ (leafAt t x.toNat).isSome) ∧
  unmergedLeavesSorted content.unmergedLeaves.val
:= by
  have := unmergedLeavesOk_succ t 0
  grind [unmergedLeafExists]

public
theorem unmergedLeavesOf_eq {l: Nat} (p: TreeSync Bytes tkt (l+1)):
  unmergedLeavesOf p = (p.nodeContent.map (·.unmergedLeaves.val)).getD []
:= by
  obtain ⟨_, bt⟩ := p
  cases bt with | node c L R => cases c <;> rfl

theorem mem_lastUpdateLhs_iff {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (x: NodeIndex):
  x ∈ lastUpdateLhs d p ↔ x ∈ resolution (p.child d.position) ∧ x ≠ d.nodeIndex
:= by
  simp [lastUpdateLhs]

theorem mem_lastUpdateRhs_iff {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (x: NodeIndex):
  x ∈ lastUpdateRhs d p ↔
    x.levels = 0 ∧ (p.child d.position).containsLeafIndex x.position ∧ memUl x.position (unmergedLeavesOf p)
:= by
  grind [lastUpdateRhs, memUl_iff]

/-- `lastUpdateCorrect`, stated with membership in the resolution. -/
public
theorem lastUpdateCorrect_iff {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)):
  lastUpdateCorrect d p ↔
    d.nodeIndex ∈ resolution (p.child d.position) ∧
    ∀ x, (x ∈ resolution (p.child d.position) ∧ x ≠ d.nodeIndex) ↔
      (x.levels = 0 ∧ (p.child d.position).containsLeafIndex x.position ∧ memUl x.position (unmergedLeavesOf p))
:= by
  simp only [lastUpdateCorrect, lastUpdateDInResC, Bool.and_eq_true, List.contains_iff_mem, setEq_iff, SetEqP,
    mem_lastUpdateLhs_iff, mem_lastUpdateRhs_iff]

/-! ## Resolution lemmas -/

/-- Port of `resolution_inside_tree`. -/
public
theorem containsNodeIndex_of_mem_resolution {l: Nat} (t: TreeSync Bytes tkt l) (x: NodeIndex)
  (hx: x ∈ resolution t) (hok: unmergedLeavesOk t):
  t.containsNodeIndex x
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    grind [resolution_zero, Tree.containsNodeIndex, Tree.nodeIndex]
  | @node l t ihLeft ihRight =>
    have := unmergedLeavesOk_left_right t hok
    rw [resolution_succ] at hx
    split at hx
    · grind [Tree.containsNodeIndex, Tree.containsLeafIndex]
    · have := unmergedLeavesOk_content t _ ‹_› hok
      simp only [List.mem_cons, mem_unmergedResolution, memUl_iff] at hx
      grind [Tree.containsNodeIndex, Tree.nodeIndex]

/-- Port of `blank_leaf_not_in_resolution`. -/
theorem ofLeafIndex_not_mem_resolution {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none) (hok: unmergedLeavesOk t):
  NodeIndex.ofLeafIndex li ∉ resolution t
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    unfold leafAt at hleaf
    grind [resolution_zero]
  | @node l t ih =>
    have hleaf' := hleaf
    unfold leafAt at hleaf'
    have := unmergedLeavesOk_child_sibling t li hok
    rw [mem_resolution_succ t li]
    split
    · have := containsNodeIndex_of_mem_resolution (t.sibling li) (NodeIndex.ofLeafIndex li)
      grind [Tree.containsNodeIndex, NodeIndex.ofLeafIndex]
    grind [unmergedLeavesOk_content, memUl_iff, NodeIndex.ofLeafIndex, Tree.nodeIndex]

/-! ## `last_update` set equality imply equality -/

/-- Port of `node_indices_are_leaf_indices`. -/
public
def NodeIndicesAreLeafIndices (l: List NodeIndex): Prop :=
  ∀ x ∈ l, x.levels = 0

/-- Port of `node_index_lt`. -/
public
def nodeIndexLt (x y: NodeIndex): Bool :=
  x.position < y.position

/-- Port of `node_indices_are_sorted`. -/
public
def nodeIndicesAreSorted (l: List NodeIndex): Bool :=
  decide (l.Pairwise (nodeIndexLt · ·))

/-- Port of `unmerged_resolution_unmerged_leaves_sorted`. -/
theorem unmergedResolution_sorted (l: List UInt32) (h: unmergedLeavesSorted l):
  NodeIndicesAreLeafIndices (unmergedResolution l) ∧ nodeIndicesAreSorted (unmergedResolution l)
:= by
  rw [unmergedLeavesSorted_iff] at h
  simp only [NodeIndicesAreLeafIndices, nodeIndicesAreSorted, unmergedResolution, List.mem_map, decide_eq_true_eq,
    List.pairwise_map, nodeIndexLt, NodeIndex.ofLeafIndex]
  grind [List.Pairwise.imp]

/-- Port of `filtered_resolution_are_leaves_imply_are_sorted`. -/
theorem nodeIndicesAreSorted_filter_resolution {l: Nat} (p: NodeIndex → Bool) (t: TreeSync Bytes tkt l)
  (h: NodeIndicesAreLeafIndices ((resolution t).filter p)) (hok: unmergedLeavesOk t):
  nodeIndicesAreSorted ((resolution t).filter p)
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    rw [resolution_zero]
    split <;> simp [nodeIndicesAreSorted, List.filter_cons] <;> split <;> simp
  | @node l t ihLeft ihRight =>
    have := unmergedLeavesOk_left_right t hok
    simp only [nodeIndicesAreSorted, decide_eq_true_eq] at ihLeft ihRight ⊢
    rw [resolution_succ] at h ⊢
    cases hc: t.nodeContent with
    | none =>
      simp only [hc, List.filter_append, NodeIndicesAreLeafIndices, List.mem_append] at h ⊢
      rw [List.pairwise_append]
      refine ⟨ihLeft (by grind [NodeIndicesAreLeafIndices]) (by grind), ihRight (by grind [NodeIndicesAreLeafIndices]) (by grind), ?_⟩
      intro a ha b hb
      simp only [List.mem_filter] at ha hb
      have := containsNodeIndex_of_mem_resolution _ _ ha.1 (by grind)
      have := containsNodeIndex_of_mem_resolution _ _ hb.1 (by grind)
      grind [nodeIndexLt, Tree.containsNodeIndex, Tree.containsLeafIndex]
    | some content =>
      have hs := unmergedResolution_sorted _ (unmergedLeavesOk_content t _ hc hok).2
      simp only [nodeIndicesAreSorted, decide_eq_true_eq] at hs
      simp only [hc, List.filter_cons] at h ⊢
      by_cases hp: p t.nodeIndex
      · have := h t.nodeIndex (by simp [hp])
        grind [Tree.nodeIndex]
      grind

/-- Port of `last_update_lhs_sorted`. -/
theorem lastUpdateLhs_sorted {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (h: NodeIndicesAreLeafIndices (lastUpdateLhs d p)) (hok: unmergedLeavesOk p):
  nodeIndicesAreSorted (lastUpdateLhs d p)
:= by
  grind [lastUpdateLhs, nodeIndicesAreSorted_filter_resolution, unmergedLeavesOk_child_sibling]

/-- Port of `last_update_rhs_sorted`. -/
theorem lastUpdateRhs_sorted {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (hok: unmergedLeavesOk p):
  NodeIndicesAreLeafIndices (lastUpdateRhs d p) ∧ nodeIndicesAreSorted (lastUpdateRhs d p)
:= by
  apply unmergedResolution_sorted
  rw [unmergedLeavesOf_eq]
  cases h: p.nodeContent with
  | none => simp [unmergedLeavesSorted, ListChain]
  | some content =>
    have := (unmergedLeavesOk_content p content h hok).2
    simp only [unmergedLeavesSorted_iff, Option.map_some, Option.getD_some] at *
    grind

/--
Port of `node_indices_are_leaf_indices_and_sorted_set_eqP_imply_eq`.
MLS* also requires `node_indices_are_leaf_indices l1` and `node_indices_are_leaf_indices l2`, which are not needed.
-/
theorem eq_of_sorted_of_setEqP (l1 l2: List NodeIndex)
  (h1: nodeIndicesAreSorted l1) (h2: nodeIndicesAreSorted l2) (h: SetEqP l1 l2):
  l1 = l2
:= by
  simp only [nodeIndicesAreSorted, decide_eq_true_eq, SetEqP] at *
  induction l1 generalizing l2 with
  | nil => cases l2 with | nil => rfl | cons b _ => simpa using (h b).2 List.mem_cons_self
  | cons a t1 ih =>
    cases l2 with
    | nil => simpa using (h a).1 List.mem_cons_self
    | cons b t2 =>
      grind [List.pairwise_cons, List.mem_cons_self, nodeIndexLt]

/-- Port of `last_update_set_eqP_imply_eq`. -/
public
theorem lastUpdateLhs_eq_lastUpdateRhs {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (hok: unmergedLeavesOk p) (h: SetEqP (lastUpdateLhs d p) (lastUpdateRhs d p)):
  lastUpdateLhs d p = lastUpdateRhs d p
:= by
  grind [lastUpdateRhs_sorted, eq_of_sorted_of_setEqP, lastUpdateLhs_sorted, NodeIndicesAreLeafIndices, SetEqP]

public
theorem nodeNotBlank_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)): nodeNotBlank t = t.nodeContent.isSome := by
  simp [nodeNotBlank]

theorem treeAdd_nodeContent {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt (l+1)) (h: treeAdd t li content = .success t'):
  t'.nodeContent.map (·.unmergedLeaves.val) = t.nodeContent.map (insertSorted li.toUInt32 ·.unmergedLeaves.val) ∧
  (t.nodeContent.isSome → li < 2^32) ∧
  t'.nodeContent.map (fun c => (c.content, c.parentHash)) = t.nodeContent.map (fun c => (c.content, c.parentHash))
:= by
  obtain ⟨newContent, newChild, h1, rfl, h2, h3, h4⟩ := treeAdd_succ t li content t' h
  grind

/-! ## Un-add lemmas -/

public
theorem optionParentNode_ext {o1 o2: Option (ParentNode Bytes tkt)}
  (h1: o1.map (fun c => (c.content, c.parentHash)) = o2.map (fun c => (c.content, c.parentHash)))
  (h2: o1.map (·.unmergedLeaves.val) = o2.map (·.unmergedLeaves.val)):
  o1 = o2
:= by
  grind [cases ParentNode, cases Option]

/-- Two `unAddP` of nodes are equal when their children, siblings and contents are. -/
public
theorem unAddP_eq_unAddP_succ {l: Nat} (t t': TreeSync Bytes tkt (l+1)) (li: Nat) (pred pred': Nat → Bool)
  (hpos: t.position = t'.position)
  (hchild: unAddP (t.child li) pred = unAddP (t'.child li) pred')
  (hsibling: unAddP (t.sibling li) pred = unAddP (t'.sibling li) pred')
  (hc: t.nodeContent.map (fun c => (c.content, c.parentHash)) = t'.nodeContent.map (fun c => (c.content, c.parentHash)))
  (hul: t.nodeContent.map (·.unmergedLeaves.val.filter (fun x => pred x.toNat)) =
    t'.nodeContent.map (·.unmergedLeaves.val.filter (fun x => pred' x.toNat))):
  unAddP t pred = unAddP t' pred'
:= by
  have := unAddP_succ t li pred
  have := unAddP_succ t' li pred'
  grind [Tree.ext_succ, optionParentNode_ext]

/-- Port of `un_add_new_leaf_not_in_tree_lemma`. -/
theorem filter_unAddUnmergedLeaf_insertSorted_of_not_mem {l: Nat} (t: TreeSync Bytes tkt l)
  (unmergedLeaves: List UInt32) (leaf: UInt32) (leaves: List UInt32)
  (h: ∀ x ∈ unmergedLeaves, unmergedLeafExists t x.toNat) (hleaf: ¬ t.containsLeafIndex leaf.toNat):
  unmergedLeaves.filter (fun x => unAddUnmergedLeaf (insertSorted leaf leaves) x.toNat) =
    unmergedLeaves.filter (fun x => unAddUnmergedLeaf leaves x.toNat)
:= by
  induction unmergedLeaves <;> grind [unAddUnmergedLeaf, unmergedLeafExists]

/-- Port of `un_add_new_leaf_not_in_tree`. -/
theorem unAdd_insertSorted_of_not_mem {l: Nat} (t: TreeSync Bytes tkt l) (leaves: List UInt32) (leaf: UInt32)
  (h: ¬ t.containsLeafIndex leaf.toNat) (hok: unmergedLeavesOk t):
  unAdd t leaves = unAdd t (insertSorted leaf leaves)
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => grind [unAdd, unAddP_zero, unAddUnmergedLeaf]
  | node t ihLeft ihRight =>
    have := unmergedLeavesOk_left_right t hok
    apply unAddP_eq_unAddP_succ (li := t.position)
    · rfl
    · grind [unAdd]
    · grind [unAdd]
    · rfl
    cases hc: t.nodeContent with
    | none => rfl
    | some c =>
      simp [filter_unAddUnmergedLeaf_insertSorted_of_not_mem t c.unmergedLeaves.val leaf leaves
        (by grind [unmergedLeavesOk_content, unmergedLeafExists]) h]

/-- Port of `un_add_empty_lemma`. -/
theorem filter_unAddUnmergedLeaf_nil (l: List UInt32): l.filter (fun x => unAddUnmergedLeaf [] x.toNat) = l := by
  simp [unAddUnmergedLeaf, memUl]

/-- Port of `un_add_empty`. -/
public
theorem unAdd_nil {l: Nat} (t: TreeSync Bytes tkt l): unAdd t [] = t := by
  induction t using Tree.leftRightInduction with
  | leaf t => apply Tree.ext_zero <;> simp [unAdd, unAddP_zero, unAddUnmergedLeaf, memUl]
  | node t ihLeft ihRight =>
    have := unAddP_succ t t.position (unAddUnmergedLeaf [])
    grind [Tree.ext_succ, unAdd, optionParentNode_ext, filter_unAddUnmergedLeaf_nil]

/-- Removing a non-member from a sorted insertion. Port of `add_outside_last_update_aux`. -/
theorem filter_insertSorted_of_not (pred: UInt32 → Bool) (li: UInt32) (l: List UInt32) (h: ¬ pred li):
  (insertSorted li l).filter pred = l.filter pred
:= by
  induction l <;> grind [insertSorted]

/--
Port of `un_add_add_lemma` and `un_add_add_lemma_lemma`.
MLS* requires `li: leaf_index l i`, which is not needed.
-/
theorem filter_unAddUnmergedLeaf_insertSorted_insertSorted {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (unmergedLeaves leaves: List UInt32)
  (h: ¬ unmergedLeafExists t li) (hul: ∀ x ∈ unmergedLeaves, unmergedLeafExists t x.toNat) (hli: li < 2^32):
  unmergedLeaves.filter (fun x => unAddUnmergedLeaf leaves x.toNat) =
    (insertSorted li.toUInt32 unmergedLeaves).filter (fun x => unAddUnmergedLeaf (insertSorted li.toUInt32 leaves) x.toNat)
:= by
  grind [filter_insertSorted_of_not, List.filter_congr, unAddUnmergedLeaf]

/-- Port of `un_add_add`. -/
theorem unAdd_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (content: LeafNode Bytes tkt)
  (leaves: List UInt32) (t': TreeSync Bytes tkt l) (h: treeAdd t li content = .success t')
  (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none) (hok: unmergedLeavesOk t) (hli32: li < 2^32):
  unAdd t' (insertSorted li.toUInt32 leaves) = unAdd t leaves
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    unfold leafAt at hleaf
    have := eq_of_containsLeafIndex_zero hli t.containsLeafIndex_position
    grind [unAdd, unAddP_zero, unAddUnmergedLeaf]
  | node t ih =>
    obtain ⟨newContent, newChild, h1, rfl, h2, -, h3⟩ := treeAdd_succ t li content t' h
    have hpos := treeAdd_position _ _ _ _ h1
    have hok' := unmergedLeavesOk_child_sibling t li hok
    have := ih _ h1 (t.mem_child_self hli) (by grind [leafAt.eq_def]) hok'.1
    have := unAdd_insertSorted_of_not_mem (t.sibling li) leaves li.toUInt32 (by grind) hok'.2
    apply unAddP_eq_unAddP_succ (li := li)
    · grind
    · grind [unAdd]
    · grind [unAdd]
    · grind
    cases hc: t.nodeContent <;> cases newContent <;> simp_all
    symm
    apply filter_unAddUnmergedLeaf_insertSorted_insertSorted t li
    all_goals grind [unmergedLeafExists, unmergedLeavesOk_content]

/-! ## Adding a leaf -/

/-- Port of `mem_resolution_add_eq`. -/
theorem mem_resolution_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (content: LeafNode Bytes tkt)
  (x: NodeIndex) (t': TreeSync Bytes tkt l) (h: treeAdd t li content = .success t')
  (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none):
  x ∈ resolution t' ↔ x = NodeIndex.ofLeafIndex li ∨ x ∈ resolution t
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    rw [treeAdd_zero t li content t' h]
    have := eq_of_containsLeafIndex_zero hli t.containsLeafIndex_position
    grind [resolution_zero, Tree.nodeIndex, NodeIndex.ofLeafIndex]
  | @node l t ih =>
    obtain ⟨newContent, newChild, h1, rfl, h2, h3, -⟩ := treeAdd_succ t li content t' h
    have := ih _ h1 (t.mem_child_self hli) (by grind [leafAt.eq_def])
    rw [mem_resolution_succ _ li, mem_resolution_succ t li]
    obtain ⟨xl, xp⟩ := x
    grind [Tree.nodeIndex, NodeIndex.ofLeafIndex]

/-- Port of `add_inside_subtree`. -/
theorem isSubtreeOf_treeAdd_inside {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp) (li: Nat)
  (content: LeafNode Bytes tkt) (d': TreeSync Bytes tkt ld) (p': TreeSync Bytes tkt lp)
  (hd: treeAdd d li content = .success d') (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hli: d.containsLeafIndex li):
  d'.IsSubtreeOf p'
:= by
  induction hsub with
  | refl =>
    grind
  | child p hsub ih =>
    obtain ⟨_, newChild, h1, rfl, -⟩ := treeAdd_succ p li content p' hp
    apply Tree.IsSubtreeOf.of_child (li := li)
    grind

/-- Port of `tree_add_pre_subtree_inside`. -/
theorem treeAdd_of_isSubtreeOf_inside {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp) (li: Nat)
  (content: LeafNode Bytes tkt) (p': TreeSync Bytes tkt lp) (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hli: d.containsLeafIndex li):
  ∃ d', treeAdd d li content = .success d'
:= by
  induction hsub with
  | refl =>
    refine ⟨p', ?_⟩
    grind
  | child p hsub ih =>
    obtain ⟨_, newChild, h1, -⟩ := treeAdd_succ p li content p' hp
    grind

/-- Port of `add_outside_subtree`. -/
theorem isSubtreeOf_treeAdd_outside {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp) (li: Nat)
  (content: LeafNode Bytes tkt) (p': TreeSync Bytes tkt lp) (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hli: p.containsLeafIndex li) (hlid: ¬ d.containsLeafIndex li):
  d.IsSubtreeOf p'
:= by
  induction hsub with
  | refl =>
    exfalso
    grind
  | child p hsub ih =>
    obtain ⟨_, newChild, h1, rfl, -⟩ := treeAdd_succ p li content p' hp
    grind [Tree.IsSubtreeOf.child]

/-- The content of a non-blank node after `treeAdd`. -/
theorem nodeContent_treeAdd {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt (l+1)) (h: treeAdd t li content = .success t')
  (pc: ParentNode Bytes tkt) (hpc: t.nodeContent = some pc):
  ∃ pc', t'.nodeContent = some pc' ∧ pc'.content = pc.content ∧ pc'.parentHash = pc.parentHash ∧
    pc'.unmergedLeaves.val = insertSorted li.toUInt32 pc.unmergedLeaves.val ∧ li.toUInt32.toNat = li
:= by
  have := treeAdd_nodeContent t li content t' h
  cases hc': t'.nodeContent <;> simp_all

/-- The unmerged leaves of a non-blank node after `treeAdd`. -/
theorem unmergedLeavesOf_treeAdd {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt (l+1)) (h: treeAdd t li content = .success t') (hnb: nodeNotBlank t):
  unmergedLeavesOf t' = insertSorted li.toUInt32 (unmergedLeavesOf t) ∧ li.toUInt32.toNat = li
:= by
  have := treeAdd_nodeContent t li content t' h
  rw [nodeNotBlank_succ] at hnb
  cases hc: t.nodeContent <;> cases hc': t'.nodeContent <;> simp_all [unmergedLeavesOf_eq]

/-- Port of `add_inside_last_update`. -/
theorem lastUpdateCorrect_treeAdd_inside {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (d': TreeSync Bytes tkt ld) (p': TreeSync Bytes tkt (lp+1))
  (hd: treeAdd d li content = .success d') (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hl: ld ≤ lp) (hnb: nodeNotBlank p) (hli: d.containsLeafIndex li)
  (hleaf: leafAt p li = none) (hlu: lastUpdateCorrect d p) (hok: unmergedLeavesOk p):
  lastUpdateCorrect d' p'
:= by
  obtain ⟨newContent, newChild, h1, hp', h2, h3, -⟩ := treeAdd_succ p li content p' hp
  have hlic: (p.child li).containsLeafIndex li := by grind
  have hleafc: leafAt (p.child li) li = none := by grind [leafAt.eq_def]
  have := fun x => mem_resolution_treeAdd _ li content x newChild h1 hlic hleafc
  -- Proves `NodeIndex.ofLeafIndex li ≠ d.nodeIndex`
  have := ofLeafIndex_not_mem_resolution _ li hlic hleafc (unmergedLeavesOk_child_sibling p li hok).1
  have hlhs: ∀ x, x ∈ lastUpdateLhs d' p' ↔ x ∈ lastUpdateLhs d p ∨ x = .ofLeafIndex li := by
    grind [mem_lastUpdateLhs_iff, lastUpdateCorrect, lastUpdateDInResC, Tree.nodeIndex]
  have hrhs: ∀ x, x ∈ lastUpdateRhs d' p' ↔ x ∈ lastUpdateRhs d p ∨ x = .ofLeafIndex li := by
    have := unmergedLeavesOf_treeAdd p li content _ hp hnb
    intro ⟨xl, xp⟩
    grind [mem_lastUpdateRhs_iff, NodeIndex.ofLeafIndex, Tree.containsLeafIndex]
  grind [lastUpdateCorrect, lastUpdateDInResC, setEq_iff, SetEqP, Tree.nodeIndex]

/-- Port of `add_outside_last_update`. -/
theorem lastUpdateCorrect_treeAdd_outside {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (p': TreeSync Bytes tkt (lp+1)) (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hnb: nodeNotBlank p)
  (hli: p.containsLeafIndex li) (hlid: ¬ d.containsLeafIndex li) (hleaf: leafAt p li = none)
  (hlu: lastUpdateCorrect d p):
  lastUpdateCorrect d p'
:= by
  obtain ⟨newContent, newChild, h1, hp', h2, h3, -⟩ := treeAdd_succ p li content p' hp
  rcases p.child_eq_or_sibling hli hsub.containsLeafIndex with ⟨-, hc⟩ | ⟨hc, -⟩
  · -- `li` is in the same child as `d`
    have := fun x => mem_resolution_treeAdd _ li content x newChild h1 (p.mem_child_self hli) (by grind [leafAt.eq_def])
    have hlhs: ∀ x, x ∈ lastUpdateLhs d p' ↔ x ∈ lastUpdateLhs d p ∨ x = .ofLeafIndex li := by
      grind [mem_lastUpdateLhs_iff, NodeIndex.ofLeafIndex, Tree.nodeIndex]
    have hrhs: ∀ x, x ∈ lastUpdateRhs d p' ↔ x ∈ lastUpdateRhs d p ∨ x = .ofLeafIndex li := by
      have := unmergedLeavesOf_treeAdd p li content _ hp hnb
      intro ⟨xl, xp⟩
      grind [mem_lastUpdateRhs_iff, NodeIndex.ofLeafIndex, Tree.containsLeafIndex]
    grind [lastUpdateCorrect, lastUpdateDInResC, setEq_iff, SetEqP]
  · -- `li` is in the sibling of `d`
    have hrhs: ∀ x, x ∈ lastUpdateRhs d p' ↔ x ∈ lastUpdateRhs d p := by
      have := unmergedLeavesOf_treeAdd p li content _ hp hnb
      grind [mem_lastUpdateRhs_iff]
    grind [lastUpdateCorrect, lastUpdateDInResC, lastUpdateLhs, setEq_iff, SetEqP]

public
theorem getParentHashOf_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  getParentHashOf t = t.nodeContent.map (·.parentHash)
:= by
  obtain ⟨_, bt⟩ := t
  cases bt with | node c L R => cases c <;> rfl

public
theorem getParentHashOf_zero (t: TreeSync Bytes tkt 0) (h: t.leafContent = none): getParentHashOf t = none := by
  obtain ⟨_, ⟨c⟩⟩ := t
  subst h
  rfl

public
theorem getParentHashOf_leaf (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt) (h: t.leafContent = some ln):
  getParentHashOf t = if h: ln.data.source == .commit then some (ln.data.parentHash.get h) else none
:= by
  obtain ⟨_, ⟨c⟩⟩ := t
  subst h
  rfl

theorem getParentHashOf_treeAdd {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt (l+1)) (h: treeAdd t li content = .success t'):
  getParentHashOf t' = getParentHashOf t
:= by
  have := (treeAdd_nodeContent t li content t' h).2.2
  rw [getParentHashOf_succ, getParentHashOf_succ]
  cases hc: t.nodeContent <;> cases hc': t'.nodeContent <;> simp_all

/-- A subtree with a parent hash, containing a blank leaf, is a node. -/
theorem exists_succ_of_nodeHasParentHash {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (hph: nodeHasParentHash t) (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none):
  ∃ l', l = l' + 1
:= by
  cases l with
  | zero =>
    unfold leafAt at hleaf
    grind [nodeHasParentHash, getParentHashOf_zero]
  | succ l =>
    refine ⟨l, ?_⟩
    grind

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-! ## Unfolding the definitions -/

theorem nodeHasParentHashLinkAux_zero (d: TreeSync Bytes tkt 0) {lp: Nat} (p: TreeSync Bytes tkt (lp+1)):
  nodeHasParentHashLinkAux d p = (d.leafContent.isSome && parentHashLinked d p)
:= by
  obtain ⟨_, ⟨c⟩⟩ := d
  cases c <;> rfl

theorem nodeHasParentHashLinkAux_left_right {ld: Nat} (d: TreeSync Bytes tkt (ld+1)) {lp: Nat} (p: TreeSync Bytes tkt (lp+1)):
  nodeHasParentHashLinkAux d p =
    match d.nodeContent with
    | none => nodeHasParentHashLinkAux d.left p || nodeHasParentHashLinkAux d.right p
    | some _ => parentHashLinked d p
:= by
  obtain ⟨_, bt⟩ := d
  cases bt with | node c L R => cases c <;> rfl

/-- `nodeHasParentHashLinkAux` of a node, through the child / sibling view for any leaf index `li`. -/
theorem nodeHasParentHashLinkAux_succ {ld: Nat} (d: TreeSync Bytes tkt (ld+1)) (li: Nat) {lp: Nat} (p: TreeSync Bytes tkt (lp+1)):
  nodeHasParentHashLinkAux d p =
    match d.nodeContent with
    | none => nodeHasParentHashLinkAux (d.child li) p || nodeHasParentHashLinkAux (d.sibling li) p
    | some _ => parentHashLinked d p
:= by
  grind [nodeHasParentHashLinkAux_left_right]

theorem nodeHasParentHashLink_eq {lp: Nat} (p: TreeSync Bytes tkt (lp+1)) (li: Nat):
  nodeHasParentHashLink p = (nodeHasParentHashLinkAux (p.child li) p || nodeHasParentHashLinkAux (p.sibling li) p)
:= by
  simp only [nodeHasParentHashLink, Tree.intoLeftRightView_eq]
  grind

theorem parentHashInvariant_zero (t: TreeSync Bytes tkt 0): parentHashInvariant t := by
  obtain ⟨_, ⟨c⟩⟩ := t
  rfl

theorem parentHashInvariant_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  parentHashInvariant t = (
    parentHashInvariant t.left && parentHashInvariant t.right &&
    match t.nodeContent with
    | none => true
    | some _ => nodeHasParentHashLink t)
:= by
  obtain ⟨_, bt⟩ := t
  cases bt with | node c L R => cases c <;> simp only [Tree.nodeContent_node, Bool.and_true] <;> rfl

/-- `parentHashInvariant` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem parentHashInvariant_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  parentHashInvariant t = (
    parentHashInvariant (t.child li) && parentHashInvariant (t.sibling li) &&
    match t.nodeContent with
    | none => true
    | some _ => nodeHasParentHashLink t)
:= by
  grind [parentHashInvariant_left_right]

/-- `parentHashCorrect`, without the `match`es. -/
public
theorem parentHashCorrect_iff {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)):
  parentHashCorrect d p ↔
    ∃ pContent ph, p.nodeContent = some pContent ∧ getParentHashOf d = some ph ∧
      computeParentHash pContent.content pContent.parentHash.val
        (unAdd (p.sibling d.position) pContent.unmergedLeaves.val) = .success ph.val
:= by
  grind [parentHashCorrect]

public
theorem nodeHasParentHash_of_parentHashCorrect {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (h: parentHashCorrect d p):
  nodeHasParentHash d
:= by
  grind [parentHashCorrect_iff, nodeHasParentHash]

/-! ## Prop invariant definition -/

/-- Port of `parent_hash_linkedP`. -/
@[expose]
public
def ParentHashLinkedP {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): Prop :=
  d.IsSubtreeOf p ∧ parentHashLinked d p

/--
Port of `node_has_parent_hash_linkP`.
MLS*'s condition `TNode? p` holds as `p` has height `lp+1`.
-/
@[expose]
public
def NodeHasParentHashLinkP {lp: Nat} (p: TreeSync Bytes tkt (lp+1)): Prop :=
  nodeNotBlank p → ∃ (ld: Nat) (d: TreeSync Bytes tkt ld), ld ≤ lp ∧ nodeHasParentHash d ∧ ParentHashLinkedP d p

/-- Port of `parent_hash_invariantP`. -/
public
def ParentHashInvariantP {l: Nat} (t: TreeSync Bytes tkt l): Prop :=
  match t.intoLeftRightView with
  | .leaf _ _ => True
  | .node _ left right => NodeHasParentHashLinkP t ∧ ParentHashInvariantP left ∧ ParentHashInvariantP right
termination_by l

theorem parentHashInvariantP_zero (t: TreeSync Bytes tkt 0): ParentHashInvariantP t := by
  grind [ParentHashInvariantP.eq_def]

theorem parentHashInvariantP_left_right {l: Nat} (t: TreeSync Bytes tkt (l+1)):
  ParentHashInvariantP t ↔ NodeHasParentHashLinkP t ∧ ParentHashInvariantP t.left ∧ ParentHashInvariantP t.right
:= by
  grind [ParentHashInvariantP.eq_def]

/-- `ParentHashInvariantP` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem parentHashInvariantP_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  ParentHashInvariantP t ↔
    NodeHasParentHashLinkP t ∧ ParentHashInvariantP (t.child li) ∧ ParentHashInvariantP (t.sibling li)
:= by
  grind [parentHashInvariantP_left_right]

/-! ## Prop invariant lemmas -/

/-- Port of `node_has_parent_hash_linkP_intro`. -/
theorem nodeHasParentHashLinkP_intro {lp ld: Nat} (p: TreeSync Bytes tkt (lp+1)) (d: TreeSync Bytes tkt ld)
  (hl: ld ≤ lp) (hph: nodeHasParentHash d) (hsub: d.IsSubtreeOf p)
  (hlu: lastUpdateCorrect d p) (hpc: parentHashCorrect d p):
  NodeHasParentHashLinkP p
:= by
  intro _
  refine ⟨ld, d, ?_⟩
  grind [ParentHashLinkedP, parentHashLinked]

/-! ## Bool invariant ↔ Prop invariant -/

/-- Port of `node_has_parent_hash_link_bool2prop`. -/
theorem nodeHasParentHashLinkP_of_nodeHasParentHashLinkAux {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (hl: ld ≤ lp) (hsub: d.IsSubtreeOf p) (h: nodeHasParentHashLinkAux d p):
  NodeHasParentHashLinkP p
:= by
  induction d using Tree.leftRightInduction with
  | leaf d =>
    rw [nodeHasParentHashLinkAux_zero] at h
    simp only [Bool.and_eq_true, parentHashLinked] at h
    apply nodeHasParentHashLinkP_intro p d <;> grind [nodeHasParentHash_of_parentHashCorrect]
  | node d ihLeft ihRight =>
    rw [nodeHasParentHashLinkAux_left_right] at h
    have := hsub.child_sibling d.position
    split at h
    · simp only [Bool.or_eq_true] at h
      grind
    · simp only [parentHashLinked, Bool.and_eq_true] at h
      apply nodeHasParentHashLinkP_intro p d <;> grind [nodeHasParentHash_of_parentHashCorrect]

/-- Port of `parent_hash_invariant_bool2prop`. -/
public
theorem parentHashInvariantP_of_parentHashInvariant {l: Nat} (t: TreeSync Bytes tkt l) (h: parentHashInvariant t):
  ParentHashInvariantP t
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => exact parentHashInvariantP_zero t
  | node t ihLeft ihRight =>
    rw [parentHashInvariant_left_right] at h
    rw [parentHashInvariantP_left_right]
    have := (Tree.IsSubtreeOf.refl (d := t)).child_sibling t.position
    have := nodeHasParentHashLinkP_of_nodeHasParentHashLinkAux t.left t (Nat.le_refl _)
    have := nodeHasParentHashLinkP_of_nodeHasParentHashLinkAux t.right t (Nat.le_refl _)
    grind [nodeHasParentHashLink_eq, NodeHasParentHashLinkP, nodeNotBlank_succ]

/-- Port of `node_has_parent_hash_link_aux_prop2bool`. -/
theorem nodeHasParentHashLinkAux_of_parentHashLinkedP {ld lp lt: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (t: TreeSync Bytes tkt lt)
  (hres: ∀ x ∈ resolution t, x ∈ resolution (p.child d.position))
  (hph: nodeHasParentHash d) (hlink: ParentHashLinkedP d p) (hsub: d.IsSubtreeOf t):
  nodeHasParentHashLinkAux t p
:= by
  have hlinked := hlink.2
  simp only [parentHashLinked, Bool.and_eq_true] at hlinked
  induction hsub with
  | refl =>
    cases ld with
    | zero =>
      rw [nodeHasParentHashLinkAux_zero]
      cases h: d.leafContent <;> simp_all [nodeHasParentHash, getParentHashOf_zero, parentHashLinked]
    | succ ld =>
      rw [nodeHasParentHashLinkAux_succ d 0]
      grind [nodeHasParentHash, getParentHashOf_succ, parentHashLinked]
  | @child lt t hsub ih =>
    rw [nodeHasParentHashLinkAux_succ t d.position]
    cases hc: t.nodeContent with
    | none =>
      have := ih (fun x hx => hres x (by grind [mem_resolution_succ t d.position]))
      grind
    | some c =>
      have hmem := hres t.nodeIndex (by grind [mem_resolution_succ t 0])
      grind [lastUpdateCorrect_iff, Tree.nodeIndex]

/-- Port of `parent_hash_invariant_prop2bool`. -/
theorem parentHashInvariant_of_parentHashInvariantP {l: Nat} (t: TreeSync Bytes tkt l) (h: ParentHashInvariantP t):
  parentHashInvariant t
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => exact parentHashInvariant_zero t
  | @node l t ihLeft ihRight =>
    rw [parentHashInvariantP_left_right] at h
    rw [parentHashInvariant_left_right]
    simp only [Bool.and_eq_true]
    refine ⟨⟨ihLeft h.2.1, ihRight h.2.2⟩, ?_⟩
    cases hc: t.nodeContent with
    | none => rfl
    | some c =>
      obtain ⟨ld, d, hl, hph, hlink⟩ := h.1 (by simp [nodeNotBlank_succ, hc])
      simp only [nodeHasParentHashLink_eq t d.position, Bool.or_eq_true]
      left
      apply nodeHasParentHashLinkAux_of_parentHashLinkedP d t <;> grind [ParentHashLinkedP]

/-! ## Parent-hash invariant: easy cases -/

/-- Port of `parent_hash_invariant_tree_create`. -/
public
theorem parentHashInvariant_treeCreate (ln: LeafNode Bytes tkt):
  parentHashInvariant (treeCreate ln: TreeSync Bytes tkt 0)
:=
  parentHashInvariant_zero _

/-- Port of `parent_hash_invariant_mk_blank_tree`. -/
theorem parentHashInvariant_mkBlankTree (l p: Nat):
  parentHashInvariant (mkBlankTree l p: TreeSync Bytes tkt l)
:= by
  induction l generalizing p with
  | zero => exact parentHashInvariant_zero _
  | succ l ih =>
    simp only [mkBlankTree] at ih
    grind [parentHashInvariant_left_right, mkBlankTree, mkBlankTreeGeneral]

/-- Port of `parent_hash_invariant_tree_extend`. -/
public
theorem parentHashInvariant_treeExtend {l: Nat} (t: TreeSync Bytes tkt l) (h: parentHashInvariant t):
  parentHashInvariant (treeExtend t)
:= by
  have := parentHashInvariant_mkBlankTree (tkt := tkt) l (t.position + 2^l)
  grind [parentHashInvariant_left_right, treeExtend, mkBlankTree]

/--
Port of `parent_hash_invariant_tree_truncate`.
MLS* requires `is_tree_empty (TNode?.right t)`, which is not needed.
-/
public
theorem parentHashInvariant_treeTruncate {l: Nat} (t: TreeSync Bytes tkt (l+1)) (h: parentHashInvariant t):
  parentHashInvariant (treeTruncate t)
:= by
  grind [parentHashInvariant_left_right, treeTruncate]

theorem parentHashInvariant_treeChangePath {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (oln: Option (LeafNode Bytes tkt)) (h: parentHashInvariant t):
  parentHashInvariant (treeChangePath t li oln none)
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact parentHashInvariant_zero _
  | node t ih => grind [treeChangePath.eq_def, parentHashInvariant_succ _ li]

/-- Port of `parent_hash_invariant_tree_update`. -/
public
theorem parentHashInvariant_treeUpdate {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt)
  (h: parentHashInvariant t):
  parentHashInvariant (treeUpdate t li ln)
:= by
  apply parentHashInvariant_treeChangePath t li (some ln)
  grind

/-- Port of `parent_hash_invariant_tree_remove`. -/
public
theorem parentHashInvariant_treeRemove {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (h: parentHashInvariant t):
  parentHashInvariant (treeRemove t li)
:= by
  apply parentHashInvariant_treeChangePath t li none
  grind

/-! ## Parent-hash invariant: adding a leaf -/

/-- Port of `add_inside_parent_hash`. -/
theorem parentHashCorrect_treeAdd_inside {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (d': TreeSync Bytes tkt ld) (p': TreeSync Bytes tkt (lp+1))
  (hd: treeAdd d li content = .success d') (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hl: ld ≤ lp) (hli: d.containsLeafIndex li) (hleaf: leafAt p li = none)
  (hpc: parentHashCorrect d p) (hok: unmergedLeavesOk p):
  parentHashCorrect d' p'
:= by
  obtain ⟨pc, ph, hpcn, hgph, hcomp⟩ := (parentHashCorrect_iff d p).mp hpc
  have hgph': getParentHashOf d' = getParentHashOf d := by
    obtain ⟨ld', rfl⟩ := exists_succ_of_nodeHasParentHash d li (by simp [nodeHasParentHash, hgph]) hli
      (by grind)
    grind [getParentHashOf_treeAdd]
  have := nodeContent_treeAdd p li content p' hp pc hpcn
  obtain ⟨_, newChild, h1, rfl, -⟩ := treeAdd_succ p li content p' hp
  grind [parentHashCorrect_iff, unAdd_insertSorted_of_not_mem, unmergedLeavesOk_child_sibling]

/-- Port of `add_outside_parent_hash`. -/
theorem parentHashCorrect_treeAdd_outside {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (li: Nat) (content: LeafNode Bytes tkt)
  (p': TreeSync Bytes tkt (lp+1)) (hp: treeAdd p li content = .success p')
  (hsub: d.IsSubtreeOf p) (hli: p.containsLeafIndex li)
  (hleaf: leafAt p li = none) (hpc: parentHashCorrect d p) (hok: unmergedLeavesOk p):
  parentHashCorrect d p'
:= by
  obtain ⟨pc, ph, hpcn, hgph, hcomp⟩ := (parentHashCorrect_iff d p).mp hpc
  have := nodeContent_treeAdd p li content p' hp pc hpcn
  obtain ⟨_, newChild, h1, rfl, -, h3, -⟩ := treeAdd_succ p li content p' hp
  have hok' := unmergedLeavesOk_child_sibling p li hok
  have := unAdd_treeAdd _ li content pc.unmergedLeaves.val _ h1 (p.mem_child_self hli) (by grind [leafAt.eq_def])
    hok'.1 (h3 (by simp [hpcn]))
  rcases p.child_eq_or_sibling hli hsub.containsLeafIndex with ⟨hm, hc⟩ | ⟨hc, -⟩ <;>
    grind [parentHashCorrect_iff, unAdd_insertSorted_of_not_mem]

/-- Port of `parent_hash_invariantP_tree_add`. -/
theorem parentHashInvariantP_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt l) (h: treeAdd t li content = .success t')
  (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none)
  (hinv: ParentHashInvariantP t) (hok: unmergedLeavesOk t):
  ParentHashInvariantP t'
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact parentHashInvariantP_zero _
  | @node l t ih =>
    have := treeAdd_nodeContent t li content t' h
    obtain ⟨newContent, newChild, h1, rfl, -⟩ := treeAdd_succ t li content t' h
    rw [parentHashInvariantP_succ _ li] at hinv ⊢
    refine ⟨fun hnb' => ?link, ?child, by grind⟩
    case child =>
      grind [leafAt.eq_def, unmergedLeavesOk_child_sibling]
    case link =>
      have hnb: nodeNotBlank t := by cases ht: t.nodeContent <;> simp_all [nodeNotBlank_succ]
      obtain ⟨ld, d, hl, hph, hsub, hlinked⟩ := hinv.1 hnb
      simp only [parentHashLinked, Bool.and_eq_true] at hlinked
      by_cases hlid: d.containsLeafIndex li
      · obtain ⟨d', hd⟩ := treeAdd_of_isSubtreeOf_inside d t li content _ h hsub hlid
        have hpc := parentHashCorrect_treeAdd_inside d t li content d' _ hd h hsub hl hlid hleaf hlinked.1 hok
        revert hnb'
        apply nodeHasParentHashLinkP_intro (d := d')
        · grind
        · grind [nodeHasParentHash_of_parentHashCorrect]
        · apply isSubtreeOf_treeAdd_inside d t li content d' <;> grind
        · apply lastUpdateCorrect_treeAdd_inside d t li content d' <;> grind
        · grind
      · revert hnb'
        apply nodeHasParentHashLinkP_intro (d := d)
        · grind
        · grind
        · apply isSubtreeOf_treeAdd_outside d t li content <;> grind
        · apply lastUpdateCorrect_treeAdd_outside d t li content <;> grind
        · apply parentHashCorrect_treeAdd_outside d t li content <;> grind

/-- Port of `parent_hash_invariant_tree_add`. -/
public
theorem parentHashInvariant_treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (content: LeafNode Bytes tkt)
  (t': TreeSync Bytes tkt l) (h: treeAdd t li content = .success t')
  (hli: t.containsLeafIndex li) (hleaf: leafAt t li = none)
  (hinv: parentHashInvariant t) (hok: unmergedLeavesOk t):
  parentHashInvariant t'
:= by
  grind [parentHashInvariant_of_parentHashInvariantP, parentHashInvariantP_treeAdd, parentHashInvariantP_of_parentHashInvariant]

/-! ## Parent-hash invariant: applying a path -/

/--
Port of `path_is_parent_hash_valid_aux`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def pathIsParentHashValidAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes): Bool
:=
  let newLp := p.getPathLeaf
  if h: newLp.data.source == .commit then
    computeLeafParentHashFromPath t li p parentParentHash == .success ((newLp.data.parentHash.get h).val)
  else
    false

theorem pathIsParentHashValid_eq {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l):
  pathIsParentHashValid t li p = pathIsParentHashValidAux t li p rootParentHash.val
:=
  rfl

public
theorem pathIsParentHashValidAux_leaf (t: TreeSync Bytes tkt 0) (li: Nat) (ln: LeafNode Bytes tkt)
  (parentParentHash: Bytes):
  pathIsParentHashValidAux t li (.leaf ln) parentParentHash =
    if h: ln.data.source == .commit then parentParentHash == (ln.data.parentHash.get h).val else false
:= by
  have: computeLeafParentHashFromPath t li (.leaf ln) parentParentHash = .success parentParentHash := by
    unfold computeLeafParentHashFromPath
    simp [pure]
  grind [pathIsParentHashValidAux, Path.getPathLeaf, Result.success_beq_success]

public
theorem pathIsParentHashValidAux_node {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (newOptContent: Option (ParentNode Bytes tkt)) (newParentParentHash: Bytes)
  (h: computeNewNpAndPh optExtContent (t.sibling li) parentParentHash = .success (newOptContent, newParentParentHash)):
  pathIsParentHashValidAux t li (.node optExtContent pNext) parentParentHash =
    pathIsParentHashValidAux (t.child li) li pNext newParentParentHash
:= by
  grind [pathIsParentHashValidAux, Path.getPathLeaf, computeLeafParentHashFromPath_node]

/-- Port of `is_tree_empty_implies_empty_resolution`. -/
public
theorem resolution_eq_nil_of_isTreeEmpty {l: Nat} (t: TreeSync Bytes tkt l) (h: isTreeEmpty t): resolution t = [] := by
  induction t using Tree.leftRightInduction with
  | leaf t => simp_all [resolution_zero, isTreeEmpty_zero]
  | node t ihLeft ihRight =>
    rw [isTreeEmpty_succ t t.position] at h
    grind [resolution_succ]

/--
Port of `find_parent_hash_link_aux` and `find_parent_hash_link_aux_misc_properties`.
The subtree `d` is the one computed by `find_parent_hash_link_aux`.
-/
theorem exists_subtree_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t')
  (hvalid: pathIsParentHashValidAux t li p parentParentHash) (hfilter: pathIsFilterValid t li p):
  ∃ (ld: Nat) (d: TreeSync Bytes tkt ld),
    ld ≤ l ∧ nodeHasParentHash d ∧ d.IsSubtreeOf t' ∧
    (getParentHashOf d).map (·.val) = some parentParentHash ∧ resolution t' = [d.nodeIndex]
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p with
    | leaf ln =>
      rw [applyPathAux_zero t li ln parentParentHash t' h]
      rw [pathIsParentHashValidAux_leaf] at hvalid
      have := getParentHashOf_leaf ((ChildSiblingView.leaf (some ln) t.position).pack: TreeSync Bytes tkt 0) ln (by simp)
      split at hvalid
      · refine ⟨0, (ChildSiblingView.leaf (some ln) t.position).pack, ?_⟩
        grind [nodeHasParentHash, resolution_zero]
      · exfalso
        grind
  | @node l t ih =>
    cases p with
    | node optExtContent pNext =>
      obtain ⟨newOptContent, newParentParentHash, newChild, hcn, hchild, rfl⟩ :=
        applyPathAux_node t li optExtContent pNext parentParentHash t' h
      have hspec := computeNewNpAndPh_spec _ _ _ _ _ hcn
      rw [pathIsParentHashValidAux_node t li optExtContent pNext parentParentHash _ _ hcn] at hvalid
      rw [pathIsFilterValid_node] at hfilter
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hfilter
      cases optExtContent with
      | none =>
        obtain ⟨ld, d, hl, hph, hsub, hgph, hres⟩ := ih pNext _ newChild hchild hvalid hfilter.2
        refine ⟨ld, d, ?_⟩
        rw [resolution_succ_of_resolution_sibling _ li (by grind) (by grind [resolution_eq_nil_of_isTreeEmpty])]
        grind
      | some extContent =>
        refine ⟨l+1, (ChildSiblingView.node newOptContent newChild (t.sibling li)).pack, ?_⟩
        grind [nodeHasParentHash, getParentHashOf_succ, resolution_succ, unmergedResolution]

/--
Port of `find_parent_hash_link_last_update`.
`d` is the subtree computed by `find_parent_hash_link` (see `exists_subtree_applyPathAux`):
it is in the child of `t` for `li`, and its node index is the resolution of the new child.
-/
theorem lastUpdateCorrect_applyPathAux {l ld: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (extContent: tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (t': TreeSync Bytes tkt (l+1)) (d: TreeSync Bytes tkt ld)
  (h: applyPathAux t li (.node (some extContent) pNext) parentParentHash = .success t')
  (hm: (t.child li).containsLeafIndex d.position) (hres: resolution (t'.child li) = [d.nodeIndex]):
  lastUpdateCorrect d t'
:= by
  obtain ⟨_, _, newChild, hcn, hchild, rfl⟩ := applyPathAux_node t li _ pNext parentParentHash t' h
  obtain ⟨c, rfl, -, -, hcul, -⟩ := computeNewNpAndPh_spec _ _ _ _ _ hcn
  grind [lastUpdateCorrect_iff, unmergedLeavesOf_eq, memUl]

/--
Port of `find_parent_hash_link_parent_hash`.
`d` is the subtree computed by `find_parent_hash_link` (see `exists_subtree_applyPathAux`):
it is in the child of `t` for `li`, and its parent hash is the one computed from the sibling.
-/
theorem parentHashCorrect_applyPathAux {l ld: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (extContent: tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (t': TreeSync Bytes tkt (l+1)) (d: TreeSync Bytes tkt ld) (ph: MlsBytes Bytes)
  (h: applyPathAux t li (.node (some extContent) pNext) parentParentHash = .success t')
  (hm: (t.child li).containsLeafIndex d.position) (hgph: getParentHashOf d = some ph)
  (hcomp: computeParentHash extContent parentParentHash (t.sibling li) = .success ph.val):
  parentHashCorrect d t'
:= by
  obtain ⟨_, _, newChild, hcn, hchild, rfl⟩ := applyPathAux_node t li _ pNext parentParentHash t' h
  have := computeNewNpAndPh_spec _ _ _ _ _ hcn
  grind [parentHashCorrect_iff, unAdd_nil]

/--
`d` is the subtree computed by `find_parent_hash_link` (see `exists_subtree_applyPathAux`):
it is parent-hash linked to the new node.
-/
public
theorem parentHashLinkedP_applyPathAux {l ld: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (extContent: tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (t': TreeSync Bytes tkt (l+1)) (d: TreeSync Bytes tkt ld) (ph: MlsBytes Bytes)
  (h: applyPathAux t li (.node (some extContent) pNext) parentParentHash = .success t')
  (hsub: d.IsSubtreeOf (t'.child li)) (hres: resolution (t'.child li) = [d.nodeIndex])
  (hgph: getParentHashOf d = some ph)
  (hcomp: computeParentHash extContent parentParentHash (t.sibling li) = .success ph.val):
  ParentHashLinkedP d t'
:= by
  have hm: (t.child li).containsLeafIndex d.position := by grind [Tree.containsLeafIndex]
  have := parentHashCorrect_applyPathAux t li extContent pNext parentParentHash t' d ph h hm hgph hcomp
  have := lastUpdateCorrect_applyPathAux t li extContent pNext parentParentHash t' d h hm hres
  grind [ParentHashLinkedP, parentHashLinked, Tree.IsSubtreeOf.of_child]

/--
Port of the `Some` case of `parent_hash_invariantP_apply_path_aux`,
with `find_parent_hash_link` and `find_parent_hash_link_misc_properties`.
MLS* requires `path_node_not_blank p`: here, the root of the path is `some extContent`.
-/
theorem nodeHasParentHashLinkP_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (extContent: tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (t': TreeSync Bytes tkt (l+1))
  (h: applyPathAux t li (.node (some extContent) pNext) parentParentHash = .success t')
  (hvalid: pathIsParentHashValidAux t li (.node (some extContent) pNext) parentParentHash)
  (hfilter: pathIsFilterValid t li (.node (some extContent) pNext)):
  NodeHasParentHashLinkP t'
:= by
  obtain ⟨_, newParentParentHash, newChild, hcn, hchild, ht'⟩ := applyPathAux_node t li _ pNext parentParentHash t' h
  obtain ⟨_, -, -, -, -, hcomp⟩ := computeNewNpAndPh_spec _ _ _ _ _ hcn
  rw [pathIsParentHashValidAux_node t li _ pNext parentParentHash _ _ hcn] at hvalid
  rw [pathIsFilterValid_node, Bool.and_eq_true] at hfilter
  obtain ⟨ld, d, hl, hph, hsub, hgph, hres⟩ := exists_subtree_applyPathAux _ li pNext _ newChild hchild hvalid hfilter.2
  obtain ⟨ph, hph', rfl⟩: ∃ ph, getParentHashOf d = some ph ∧ ph.val = newParentParentHash := by
    cases hg: getParentHashOf d <;> simp_all
  intro _
  refine ⟨ld, d, ?_⟩
  have := parentHashLinkedP_applyPathAux t li extContent pNext parentParentHash t' d ph h
  grind

/-- Port of `parent_hash_invariantP_apply_path_aux`. -/
theorem parentHashInvariantP_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t')
  (hinv: ParentHashInvariantP t)
  (hvalid: pathIsParentHashValidAux t li p parentParentHash) (hfilter: pathIsFilterValid t li p):
  ParentHashInvariantP t'
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t => exact parentHashInvariantP_zero _
  | @node l t ih =>
    cases p with
    | node optExtContent pNext =>
      have hlink: NodeHasParentHashLinkP t' := by
        cases optExtContent with
        | none =>
          intro hnb
          obtain ⟨_, _, _, hcn, hchild, rfl⟩ := applyPathAux_node t li none pNext parentParentHash t' h
          have := computeNewNpAndPh_spec _ _ _ _ _ hcn
          grind [nodeNotBlank_succ]
        | some extContent => apply nodeHasParentHashLinkP_applyPathAux t li extContent pNext parentParentHash <;> grind
      obtain ⟨newOptContent, newParentParentHash, newChild, hcn, hchild, rfl⟩ :=
        applyPathAux_node t li optExtContent pNext parentParentHash t' h
      rw [pathIsParentHashValidAux_node t li optExtContent pNext parentParentHash _ _ hcn] at hvalid
      rw [pathIsFilterValid_node] at hfilter
      rw [parentHashInvariantP_succ _ li] at hinv ⊢
      grind

/-- Port of `parent_hash_invariant_apply_path`. -/
public
theorem parentHashInvariant_applyPath {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (t': TreeSync Bytes tkt l) (h: applyPath t li p = .success t')
  (hinv: parentHashInvariant t) (hvalid: pathIsParentHashValid t li p) (hfilter: pathIsFilterValid t li p):
  parentHashInvariant t'
:= by
  apply parentHashInvariant_of_parentHashInvariantP
  apply parentHashInvariantP_applyPathAux t li p rootParentHash.val t'
  · grind [applyPath]
  · grind [parentHashInvariantP_of_parentHashInvariant]
  · grind [pathIsParentHashValid_eq]
  · grind

end CryptoBytes

end MLS.TreeSync
