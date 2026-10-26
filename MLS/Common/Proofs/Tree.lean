module

public import MLS.Common.Code.Tree

/-!
Port of `MLS.Tree.Lemmas`, and reasoning lemmas about the views of `MLS.Tree`.

Port-specific differences:
- MLS*'s lemmas about `tree_index` arithmetic (`leaf_index_inside_right_index`, `leaf_index_same_side`, …)
  have no counterpart: positions are not in the types.
- Proofs about functions recursing on views follow this pattern:
  1. unfold the function (e.g. `unfold leafAt`),
  2. `simp` (or `grind`) reduces the `match` on the view with `Tree.intoChildSiblingView_eq`:
     the view of a node is `.node t.nodeContent (t.child li) (t.sibling li)`,
  3. the projections (`t.child li`, …) are reasoned about with the lemmas below.
  Functions rebuilding a tree (e.g. `treeChangePath`) compute the pack
  `(.node t.nodeContent c (t.sibling li)).pack`: `t` where the child for `li` is replaced by `c`.
- `Tree.commonPathInduction li li'` is an induction principle following the common path of two leaf indices.
-/

namespace MLS

variable {Leaf Node: Type}

/-- A tree is determined by its position and bare tree. -/
@[simp]
public
theorem Tree.mk_bareTree {l: Nat} (t: Tree Leaf Node l) (p: Nat) (h: t.position = p):
  (⟨p, t.bareTree⟩: Tree Leaf Node l) = t
:= by
  subst h
  rfl

/-! ## Unfolding on concrete trees -/

theorem Tree.intoLeftRightView_node {l: Nat} (p: Nat) (content: Node) (left right: BareTree Leaf Node l):
  (⟨p, .node content left right⟩: Tree Leaf Node (l+1)).intoLeftRightView = .node content ⟨p, left⟩ ⟨p + 2^l, right⟩
:= rfl

theorem Tree.intoChildSiblingView_node {l: Nat} (p: Nat) (content: Node) (left right: BareTree Leaf Node l) (li: Nat):
  (⟨p, .node content left right⟩: Tree Leaf Node (l+1)).intoChildSiblingView li =
    if li < p + 2^l then .node content ⟨p, left⟩ ⟨p + 2^l, right⟩ else .node content ⟨p + 2^l, right⟩ ⟨p, left⟩
:= rfl

theorem ChildSiblingView.pack_node {l: Nat} (content: Node) (child sibling: Tree Leaf Node l):
  (ChildSiblingView.node content child sibling).pack =
    if child.position < sibling.position then
      ⟨child.position, .node content child.bareTree sibling.bareTree⟩
    else
      ⟨sibling.position, .node content sibling.bareTree child.bareTree⟩
:= by
  rfl

public
theorem Tree.nodeContent_node {l: Nat} (p: Nat) (content: Node) (left right: BareTree Leaf Node l):
  (⟨p, .node content left right⟩: Tree Leaf Node (l+1)).nodeContent = content
:= rfl

theorem Tree.child_node {l: Nat} (p: Nat) (content: Node) (left right: BareTree Leaf Node l) (li: Nat):
  (⟨p, .node content left right⟩: Tree Leaf Node (l+1)).child li =
    if li < p + 2^l then ⟨p, left⟩ else ⟨p + 2^l, right⟩
:= by
  grind [Tree.child, Tree.sibling, Tree.intoChildSiblingView_node]

theorem Tree.sibling_node {l: Nat} (p: Nat) (content: Node) (left right: BareTree Leaf Node l) (li: Nat):
  (⟨p, .node content left right⟩: Tree Leaf Node (l+1)).sibling li =
    if li < p + 2^l then ⟨p + 2^l, right⟩ else ⟨p, left⟩
:= by
  grind [Tree.child, Tree.sibling, Tree.intoChildSiblingView_node]

/-! ## Views -/

@[simp]
public
theorem Tree.intoLeftRightView_eq {l: Nat} (t: Tree Leaf Node (l+1)):
  t.intoLeftRightView = .node t.nodeContent t.left t.right
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoLeftRightView_eq => t.intoLeftRightView

@[simp]
public
theorem Tree.right_position {l: Nat} (t: Tree Leaf Node (l+1)): t.right.position = t.position + 2^l := by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.right_position => t.right.position

@[simp]
public
theorem Tree.left_position {l: Nat} (t: Tree Leaf Node (l+1)): t.left.position = t.position := by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.left_position => t.left.position

@[simp]
public
theorem Tree.intoChildSiblingView_eq {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  t.intoChildSiblingView li = .node t.nodeContent (t.child li) (t.sibling li)
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.nodeContent_node, Tree.child_node, Tree.sibling_node, Tree.intoChildSiblingView_node]

grind_pattern Tree.intoChildSiblingView_eq => t.intoChildSiblingView li

@[simp]
public
theorem Tree.intoChildSiblingView_zero (t: Tree Leaf Node 0) (li: Nat):
  t.intoChildSiblingView li = .leaf t.leafContent t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoChildSiblingView_zero => t.intoChildSiblingView li

@[simp]
public
theorem Tree.intoLeftRightView_zero (t: Tree Leaf Node 0):
  t.intoLeftRightView = .leaf t.leafContent t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoLeftRightView_zero => t.intoLeftRightView

@[simp]
public
theorem LeftRightView.position_pack_leaf (content: Leaf) (p: Nat):
  ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).position = p
:= rfl

grind_pattern LeftRightView.position_pack_leaf => ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).position

@[simp]
public
theorem LeftRightView.leafContent_pack (content: Leaf) (p: Nat):
  ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).leafContent = content
:= rfl

grind_pattern LeftRightView.leafContent_pack => ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).leafContent

@[simp]
public
theorem ChildSiblingView.position_pack_leaf (content: Leaf) (p: Nat):
  ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).position = p
:= rfl

grind_pattern ChildSiblingView.position_pack_leaf => ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).position

@[simp]
public
theorem ChildSiblingView.leafContent_pack (content: Leaf) (p: Nat):
  ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).leafContent = content
:= rfl

grind_pattern ChildSiblingView.leafContent_pack => ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).leafContent

/-! ## Left / right view and child / sibling view -/

@[simp]
public
theorem LeftRightView.position_pack_node {l: Nat} (content: Node) (left right: Tree Leaf Node l):
  (LeftRightView.node content left right).pack.position = left.position
:= rfl

grind_pattern LeftRightView.position_pack_node => (LeftRightView.node content left right).pack.position

@[simp]
public
theorem LeftRightView.nodeContent_pack {l: Nat} (content: Node) (left right: Tree Leaf Node l):
  (LeftRightView.node content left right).pack.nodeContent = content
:= rfl

grind_pattern LeftRightView.nodeContent_pack => (LeftRightView.node content left right).pack.nodeContent

@[simp]
public
theorem LeftRightView.left_pack {l: Nat} (content: Node) (left right: Tree Leaf Node l):
  (LeftRightView.node content left right).pack.left = left
:= rfl

grind_pattern LeftRightView.left_pack => (LeftRightView.node content left right).pack.left

@[simp]
public
theorem LeftRightView.right_pack {l: Nat} (content: Node) (left right: Tree Leaf Node l)
  (h: right.position = left.position + 2^l):
  (LeftRightView.node content left right).pack.right = right
:= by
  obtain ⟨pr, br⟩ := right
  grind [LeftRightView.pack, Tree.right, Tree.intoLeftRightView]

grind_pattern LeftRightView.right_pack => (LeftRightView.node content left right).pack.right

/-- The child for `li` of a packed left / right view, when `right` is the right half next to `left`. -/
@[simp]
public
theorem LeftRightView.child_pack {l: Nat} (content: Node) (left right: Tree Leaf Node l) (li: Nat)
  (h: right.position = left.position + 2^l):
  (LeftRightView.node content left right).pack.child li = if li < right.position then left else right
:= by
  obtain ⟨pl, bl⟩ := left
  obtain ⟨pr, br⟩ := right
  grind [LeftRightView.pack, Tree.child_node]

/-- The child for `li` is the left or right half, depending on the side of `li`. -/
public
theorem Tree.child_eq_left_right {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  t.child li = if li < t.right.position then t.left else t.right
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  simp only [Tree.child_node]
  rfl

grind_pattern Tree.child_eq_left_right => t.child li

public
theorem Tree.sibling_eq_left_right {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  t.sibling li = if li < t.right.position then t.right else t.left
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.sibling_node, Tree.left, Tree.right, Tree.intoLeftRightView_node]

grind_pattern Tree.sibling_eq_left_right => t.sibling li

public
theorem Tree.mem_left_or_right {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (h: t.containsLeafIndex li):
  (t.left.containsLeafIndex li ∧ li < t.right.position) ∨ (t.right.containsLeafIndex li ∧ ¬ li < t.right.position)
:= by
  grind [Tree.containsLeafIndex]

/-! ## Replacing the child of a view

`(.node t.nodeContent c (t.sibling li)).pack` is `t`, where the child for `li` is replaced by `c`.
-/

/-- On a concrete node, replacing the child by a tree at the same position. -/
theorem Tree.pack_replaceChild_node {l: Nat} (p: Nat) (content content': Node) (left right: BareTree Leaf Node l) (li: Nat)
  (c: Tree Leaf Node l) (hc: c.position = ((⟨p, .node content left right⟩: Tree Leaf Node (l+1)).child li).position):
  (ChildSiblingView.node content' c ((⟨p, .node content left right⟩: Tree Leaf Node (l+1)).sibling li)).pack =
    if li < p + 2^l then ⟨p, .node content' c.bareTree right⟩ else ⟨p, .node content' left c.bareTree⟩
:= by
  grind [Tree.child_node, Tree.sibling_node, ChildSiblingView.pack_node]

@[simp]
public
theorem Tree.position_pack_replaceChild {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (content: Node)
  (c: Tree Leaf Node l) (hc: c.position = (t.child li).position):
  (ChildSiblingView.node content c (t.sibling li)).pack.position = t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node]

grind_pattern Tree.position_pack_replaceChild => (ChildSiblingView.node content c (t.sibling li)).pack.position

@[simp]
public
theorem Tree.nodeContent_pack_replaceChild {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (content: Node)
  (c: Tree Leaf Node l) (hc: c.position = (t.child li).position):
  (ChildSiblingView.node content c (t.sibling li)).pack.nodeContent = content
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node, Tree.nodeContent_node]

grind_pattern Tree.nodeContent_pack_replaceChild => (ChildSiblingView.node content c (t.sibling li)).pack.nodeContent

@[simp]
public
theorem Tree.sibling_pack_replaceChild {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (content: Node)
  (c: Tree Leaf Node l) (hc: c.position = (t.child li).position):
  (ChildSiblingView.node content c (t.sibling li)).pack.sibling li = t.sibling li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node, Tree.sibling_node, Tree.child_node]

grind_pattern Tree.sibling_pack_replaceChild => (ChildSiblingView.node content c (t.sibling li)).pack.sibling li

/-- If `li'` is in the same child as `li`, the child for `li'` is the new child. -/
@[simp]
public
theorem Tree.child_pack_replaceChild_of_child_eq_child {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
  (content: Node) (c: Tree Leaf Node l) (hc: c.position = (t.child li).position) (h: t.child li' = t.child li):
  (ChildSiblingView.node content c (t.sibling li)).pack.child li' = c
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  obtain ⟨pc, bc⟩ := c
  grind [Tree.pack_replaceChild_node, Tree.child_node]

grind_pattern Tree.child_pack_replaceChild_of_child_eq_child =>
  (ChildSiblingView.node content c (t.sibling li)).pack.child li'
where
  guard t.child li' = t.child li

/-- If `li'` is in the sibling of `li`, the child for `li'` is untouched. -/
@[simp]
public
theorem Tree.child_pack_replaceChild_of_child_eq_sibling {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
  (content: Node) (c: Tree Leaf Node l) (hc: c.position = (t.child li).position) (h: t.child li' = t.sibling li):
  (ChildSiblingView.node content c (t.sibling li)).pack.child li' = t.sibling li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node, Tree.child_node, Tree.sibling_node]

grind_pattern Tree.child_pack_replaceChild_of_child_eq_sibling =>
  (ChildSiblingView.node content c (t.sibling li)).pack.child li'
where
  guard t.child li' = t.sibling li

/-- If `li'` is in the same child as `li`, the sibling for `li'` is untouched. -/
@[simp]
public
theorem Tree.sibling_pack_replaceChild_of_child_eq_child {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
  (content: Node) (c: Tree Leaf Node l) (hc: c.position = (t.child li).position) (h: t.child li' = t.child li):
  (ChildSiblingView.node content c (t.sibling li)).pack.sibling li' = t.sibling li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node, Tree.child_node, Tree.sibling_node]

grind_pattern Tree.sibling_pack_replaceChild_of_child_eq_child =>
  (ChildSiblingView.node content c (t.sibling li)).pack.sibling li'
where
  guard t.child li' = t.child li

/-- If `li'` is in the sibling of `li`, the sibling for `li'` is the new child. -/
@[simp]
public
theorem Tree.sibling_pack_replaceChild_of_child_eq_sibling {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
  (content: Node) (c: Tree Leaf Node l) (hc: c.position = (t.child li).position) (h: t.child li' = t.sibling li):
  (ChildSiblingView.node content c (t.sibling li)).pack.sibling li' = c
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  obtain ⟨pc, bc⟩ := c
  grind [Tree.pack_replaceChild_node, Tree.child_node, Tree.sibling_node]

grind_pattern Tree.sibling_pack_replaceChild_of_child_eq_sibling =>
  (ChildSiblingView.node content c (t.sibling li)).pack.sibling li'
where
  guard t.child li' = t.sibling li

/-! ## Leaf indices in the child or the sibling -/

public
theorem Tree.mem_child_self {l: Nat} (t: Tree Leaf Node (l+1)) {li: Nat} (hli: t.containsLeafIndex li):
  (t.child li).containsLeafIndex li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.child_node, Tree.containsLeafIndex, Nat.pow_succ]

grind_pattern Tree.mem_child_self => (t.child li).containsLeafIndex li

public
theorem Tree.not_mem_sibling_self {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  ¬ (t.sibling li).containsLeafIndex li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.sibling_node, Tree.containsLeafIndex, Nat.pow_succ]

grind_pattern Tree.not_mem_sibling_self => (t.sibling li).containsLeafIndex li

/--
A leaf index `li'` of `t` is either in the same child as `li`, or in the sibling of `li` (and then `li ≠ li'`).
-/
public
theorem Tree.child_eq_or_sibling {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  ((t.child li).containsLeafIndex li' ∧ t.child li' = t.child li) ∨ (t.child li' = t.sibling li ∧ li ≠ li')
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.child_node, Tree.sibling_node, Tree.containsLeafIndex, Nat.pow_succ]

public
theorem eq_of_containsLeafIndex_zero {t: Tree Leaf Node 0} {li li': Nat}
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'): li = li'
:= by
  grind [Tree.containsLeafIndex]

grind_pattern eq_of_containsLeafIndex_zero =>
  t.containsLeafIndex li,
  t.containsLeafIndex li'

/-- The child for the position of a tree is its left half. -/
public
theorem Tree.child_position {l: Nat} (t: Tree Leaf Node (l+1)): t.child t.position = t.left := by
  grind

grind_pattern Tree.child_position => t.child t.position

public
theorem Tree.sibling_position {l: Nat} (t: Tree Leaf Node (l+1)): t.sibling t.position = t.right := by
  grind

grind_pattern Tree.sibling_position => t.sibling t.position

@[simp]
public
theorem LeftRightView.pack_node_left_right {l: Nat} (t: Tree Leaf Node (l+1)):
  (LeftRightView.node t.nodeContent t.left t.right).pack = t
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

public
theorem Tree.containsLeafIndex_position {l: Nat} (t: Tree Leaf Node l): t.containsLeafIndex t.position := by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.containsLeafIndex_position => t.containsLeafIndex t.position

/-- Trees of the same height and position contain the same leaf indices. -/
public
theorem Tree.containsLeafIndex_of_position_eq {Leaf' Node': Type} {l: Nat}
  (t: Tree Leaf Node l) (t': Tree Leaf' Node' l) (li: Nat)
  (hpos: t.position = t'.position) (hli: t.containsLeafIndex li):
  t'.containsLeafIndex li
:= by
  grind [Tree.containsLeafIndex]

public
theorem Tree.containsLeafIndex_of_mem_child {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.child li).containsLeafIndex li'):
  t.containsLeafIndex li'
:= by
  grind [Tree.containsLeafIndex, Nat.pow_succ]

grind_pattern Tree.containsLeafIndex_of_mem_child => (t.child li).containsLeafIndex li'

public
theorem Tree.containsLeafIndex_of_mem_sibling {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.sibling li).containsLeafIndex li'):
  t.containsLeafIndex li'
:= by
  grind [Tree.containsLeafIndex, Nat.pow_succ]

grind_pattern Tree.containsLeafIndex_of_mem_sibling => (t.sibling li).containsLeafIndex li'

/-- A leaf index `li'` in the child for `li` has the same child. -/
public
theorem Tree.child_eq_of_mem_child {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.child li).containsLeafIndex li'):
  t.child li' = t.child li
:= by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.child_eq_of_mem_child =>
  t.child li',
  (t.child li).containsLeafIndex li'

/-- A leaf index `li'` in the sibling of `li` has the sibling as child. -/
public
theorem Tree.child_eq_sibling_of_mem_sibling {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.sibling li).containsLeafIndex li'):
  t.child li' = t.sibling li
:= by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.child_eq_sibling_of_mem_sibling =>
  t.child li',
  (t.sibling li).containsLeafIndex li'

/-- A leaf index `li'` in the child for `li` has the same sibling. -/
public
theorem Tree.sibling_eq_of_mem_child {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.child li).containsLeafIndex li'):
  t.sibling li' = t.sibling li
:= by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.sibling_eq_of_mem_child =>
  t.sibling li',
  (t.child li).containsLeafIndex li'

/-- A leaf index `li'` in the sibling of `li` has the child for `li` as sibling. -/
public
theorem Tree.sibling_eq_child_of_mem_sibling {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.sibling li).containsLeafIndex li'):
  t.sibling li' = t.child li
:= by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.sibling_eq_child_of_mem_sibling =>
  t.sibling li',
  (t.sibling li).containsLeafIndex li'

/-- The child and the sibling for `li` are disjoint. -/
public
theorem Tree.not_mem_sibling_of_mem_child {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (h: (t.child li).containsLeafIndex li'):
  ¬ (t.sibling li).containsLeafIndex li'
:= by
  grind [Tree.containsLeafIndex]

grind_pattern Tree.not_mem_sibling_of_mem_child =>
  (t.sibling li).containsLeafIndex li',
  (t.child li).containsLeafIndex li'

/-! ## Extensionality -/

public
theorem Tree.ext_zero {t1 t2: Tree Leaf Node 0}
  (hp: t1.position = t2.position) (hc: t1.leafContent = t2.leafContent):
  t1 = t2
:= by
  obtain ⟨p1, ⟨c1⟩⟩ := t1
  obtain ⟨p2, ⟨c2⟩⟩ := t2
  simp_all [Tree.leafContent]

/-- Two nodes are equal when their positions, contents, children and siblings for some leaf index `li` are. -/
public
theorem Tree.ext_succ {l: Nat} {t1 t2: Tree Leaf Node (l+1)} (li: Nat)
  (hp: t1.position = t2.position) (hc: t1.nodeContent = t2.nodeContent)
  (hchild: t1.child li = t2.child li) (hsibling: t1.sibling li = t2.sibling li):
  t1 = t2
:= by
  obtain ⟨p1, bt1⟩ := t1
  obtain ⟨p2, bt2⟩ := t2
  cases bt1
  cases bt2
  simp only [Tree.child_node, Tree.sibling_node, Tree.nodeContent_node] at *
  subst hp hc
  split at hchild <;> simp_all

/--
Equality of trees at possibly different heights (MLS*'s `l1 == l2 /\ i1 == i2 /\ t1 == t2`), on leaves.
-/
public
theorem Tree.sigma_eq_zero (t1 t2: Tree Leaf Node 0):
  (⟨0, t1⟩: (l: Nat) × Tree Leaf Node l) = ⟨0, t2⟩ ↔
    t1.position = t2.position ∧ t1.leafContent = t2.leafContent
:= by
  grind [Tree.ext_zero]

/-- Equality of trees at possibly different heights, on nodes: contents and both children are equal. -/
public
theorem Tree.sigma_eq_succ {l1 l2: Nat} (t1: Tree Leaf Node (l1+1)) (t2: Tree Leaf Node (l2+1)):
  (⟨l1+1, t1⟩: (l: Nat) × Tree Leaf Node l) = ⟨l2+1, t2⟩ ↔
    t1.nodeContent = t2.nodeContent ∧
    (⟨l1, t1.left⟩: (l: Nat) × Tree Leaf Node l) = ⟨l2, t2.left⟩ ∧
    (⟨l1, t1.right⟩: (l: Nat) × Tree Leaf Node l) = ⟨l2, t2.right⟩
:= by
  obtain ⟨_, ⟨_⟩⟩ := t1
  obtain ⟨_, ⟨_⟩⟩ := t2
  simp [Tree.left, Tree.right, Tree.nodeContent, Tree.intoLeftRightView]
  grind

@[simp]
public
theorem ChildSiblingView.pack_node_child_sibling {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  (ChildSiblingView.node t.nodeContent (t.child li) (t.sibling li)).pack = t
:= by
  apply Tree.ext_succ li <;> simp

/-! ## Induction principles -/

/-- Induction on a tree, with induction hypotheses on its left and right halves. -/
@[elab_as_elim]
public
theorem Tree.leftRightInduction {motive: (l: Nat) → Tree Leaf Node l → Prop}
  (leaf: ∀ (t: Tree Leaf Node 0), motive 0 t)
  (node: ∀ {l: Nat} (t: Tree Leaf Node (l+1)), motive l t.left → motive l t.right → motive (l+1) t):
  ∀ {l: Nat} (t: Tree Leaf Node l), motive l t
| 0, t => leaf t
| _+1, t => node t (Tree.leftRightInduction leaf node t.left) (Tree.leftRightInduction leaf node t.right)

/--
Induction on two trees of possibly different heights,
with induction hypotheses on their left halves and on their right halves.
-/
@[elab_as_elim]
public
theorem Tree.leftRightInduction₂ {motive: (l1 l2: Nat) → Tree Leaf Node l1 → Tree Leaf Node l2 → Prop}
  (leafLeaf: ∀ (t1 t2: Tree Leaf Node 0), motive 0 0 t1 t2)
  (leafNode: ∀ {l2: Nat} (t1: Tree Leaf Node 0) (t2: Tree Leaf Node (l2+1)), motive 0 (l2+1) t1 t2)
  (nodeLeaf: ∀ {l1: Nat} (t1: Tree Leaf Node (l1+1)) (t2: Tree Leaf Node 0), motive (l1+1) 0 t1 t2)
  (nodeNode: ∀ {l1 l2: Nat} (t1: Tree Leaf Node (l1+1)) (t2: Tree Leaf Node (l2+1)),
    motive l1 l2 t1.left t2.left → motive l1 l2 t1.right t2.right → motive (l1+1) (l2+1) t1 t2):
  ∀ {l1 l2: Nat} (t1: Tree Leaf Node l1) (t2: Tree Leaf Node l2), motive l1 l2 t1 t2
| 0, 0, t1, t2 => leafLeaf t1 t2
| 0, _+1, t1, t2 => leafNode t1 t2
| _+1, 0, t1, t2 => nodeLeaf t1 t2
| _+1, _+1, t1, t2 =>
  nodeNode t1 t2
    (Tree.leftRightInduction₂ leafLeaf leafNode nodeLeaf nodeNode t1.left t2.left)
    (Tree.leftRightInduction₂ leafLeaf leafNode nodeLeaf nodeNode t1.right t2.right)

/-- Induction on a tree, following the child for the leaf index `li`. -/
@[elab_as_elim]
public
theorem Tree.childInduction (li: Nat) {motive: (l: Nat) → Tree Leaf Node l → Prop}
  (leaf: ∀ (t: Tree Leaf Node 0), motive 0 t)
  (node: ∀ {l: Nat} (t: Tree Leaf Node (l+1)), motive l (t.child li) → motive (l+1) t):
  ∀ {l: Nat} (t: Tree Leaf Node l), motive l t
| 0, t => leaf t
| _+1, t => node t (Tree.childInduction li leaf node (t.child li))

/-! ## Induction along the common path of two leaf indices -/

/--
Induction along the common path of the leaf indices `li` and `li'`:
- on a leaf, `li = li'`;
- on a node, either `li'` is in the same child as `li`, with an induction hypothesis on this child,
- or `li'` is in the sibling of `li`.
-/
@[elab_as_elim]
public
theorem Tree.commonPathInduction (li li': Nat)
  {motive: (l: Nat) → (t: Tree Leaf Node l) → t.containsLeafIndex li → t.containsLeafIndex li' → Prop}
  (leaf: ∀ (t: Tree Leaf Node 0) {hli hli'}, li = li' → motive 0 t hli hli')
  (sameChild: ∀ {l: Nat} (t: Tree Leaf Node (l+1)) {hli hli' hli'c},
    t.child li' = t.child li → motive l (t.child li) (t.mem_child_self hli) hli'c → motive (l+1) t hli hli')
  (sibling: ∀ {l: Nat} (t: Tree Leaf Node (l+1)) {hli hli'},
    t.child li' = t.sibling li → li ≠ li' → motive (l+1) t hli hli'):
  ∀ {l: Nat} (t: Tree Leaf Node l) (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'),
    motive l t hli hli'
| 0, t, hli, hli' => leaf t (eq_of_containsLeafIndex_zero hli hli')
| _+1, t, hli, hli' =>
  match t.child_eq_or_sibling hli hli' with
  | .inl ⟨hm, h⟩ => sameChild t h (Tree.commonPathInduction li li' leaf sameChild sibling (t.child li) (t.mem_child_self hli) hm)
  | .inr ⟨h, hne⟩ => sibling t h hne

end MLS
