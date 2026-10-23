import Mls.Tree

/-!
Port of `MLS.Tree.Lemmas`, and reasoning lemmas about the views of `Mls.Tree`.

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

namespace Mls

variable {Leaf Node: Type}

/-- A tree is determined by its position and bare tree. -/
@[simp] theorem Tree.mk_bareTree {l: Nat} (t: Tree Leaf Node l) (p: Nat) (h: t.position = p):
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

@[simp] theorem Tree.intoLeftRightView_eq {l: Nat} (t: Tree Leaf Node (l+1)):
  t.intoLeftRightView = .node t.nodeContent t.left t.right
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoLeftRightView_eq => t.intoLeftRightView

@[simp] theorem Tree.right_position {l: Nat} (t: Tree Leaf Node (l+1)): t.right.position = t.position + 2^l := by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.right_position => t.right.position

@[simp] theorem Tree.left_position {l: Nat} (t: Tree Leaf Node (l+1)): t.left.position = t.position := by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.left_position => t.left.position

@[simp] theorem Tree.intoChildSiblingView_eq {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  t.intoChildSiblingView li = .node t.nodeContent (t.child li) (t.sibling li)
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.nodeContent_node, Tree.child_node, Tree.sibling_node, Tree.intoChildSiblingView_node]

grind_pattern Tree.intoChildSiblingView_eq => t.intoChildSiblingView li

@[simp] theorem Tree.intoChildSiblingView_zero (t: Tree Leaf Node 0) (li: Nat):
  t.intoChildSiblingView li = .leaf t.leafContent t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoChildSiblingView_zero => t.intoChildSiblingView li

@[simp] theorem Tree.intoLeftRightView_zero (t: Tree Leaf Node 0):
  t.intoLeftRightView = .leaf t.leafContent t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  rfl

grind_pattern Tree.intoLeftRightView_zero => t.intoLeftRightView

@[simp] theorem LeftRightView.position_pack_leaf (content: Leaf) (p: Nat):
  ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).position = p
:= rfl

grind_pattern LeftRightView.position_pack_leaf => ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).position

@[simp] theorem LeftRightView.leafContent_pack (content: Leaf) (p: Nat):
  ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).leafContent = content
:= rfl

grind_pattern LeftRightView.leafContent_pack => ((LeftRightView.leaf content p).pack: Tree Leaf Node 0).leafContent

@[simp] theorem ChildSiblingView.position_pack_leaf (content: Leaf) (p: Nat):
  ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).position = p
:= rfl

grind_pattern ChildSiblingView.position_pack_leaf => ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).position

@[simp] theorem ChildSiblingView.leafContent_pack (content: Leaf) (p: Nat):
  ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).leafContent = content
:= rfl

grind_pattern ChildSiblingView.leafContent_pack => ((ChildSiblingView.leaf content p).pack: Tree Leaf Node 0).leafContent

/-! ## Left / right view and child / sibling view -/

@[simp] theorem LeftRightView.position_pack_node {l: Nat} (content: Node) (left right: Tree Leaf Node l):
  (LeftRightView.node content left right).pack.position = left.position
:= rfl

/-- The child for `li` of a packed left / right view, when `right` is the right half next to `left`. -/
@[simp] theorem LeftRightView.child_pack {l: Nat} (content: Node) (left right: Tree Leaf Node l) (li: Nat)
  (h: right.position = left.position + 2^l):
  (LeftRightView.node content left right).pack.child li = if li < right.position then left else right
:= by
  obtain ⟨pl, bl⟩ := left
  obtain ⟨pr, br⟩ := right
  grind [LeftRightView.pack, Tree.child_node]

/-- The child for `li` is the left or right half, depending on the side of `li`. -/
theorem Tree.child_eq_left_right {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat):
  t.child li = if li < t.right.position then t.left else t.right
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  simp only [Tree.child_node]
  rfl

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

@[simp] theorem Tree.position_pack_replaceChild {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (content: Node)
  (c: Tree Leaf Node l) (hc: c.position = (t.child li).position):
  (ChildSiblingView.node content c (t.sibling li)).pack.position = t.position
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.pack_replaceChild_node]

grind_pattern Tree.position_pack_replaceChild => (ChildSiblingView.node content c (t.sibling li)).pack.position

/-- If `li'` is in the same child as `li`, the child for `li'` is the new child. -/
@[simp] theorem Tree.child_pack_replaceChild_of_child_eq_child {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
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
@[simp] theorem Tree.child_pack_replaceChild_of_child_eq_sibling {l: Nat} (t: Tree Leaf Node (l+1)) (li li': Nat)
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

/-! ## Leaf indices in the child or the sibling -/

theorem Tree.mem_child_self {l: Nat} (t: Tree Leaf Node (l+1)) {li: Nat} (hli: t.containsLeafIndex li):
  (t.child li).containsLeafIndex li
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.child_node, Tree.containsLeafIndex, Nat.pow_succ]

/--
A leaf index `li'` of `t` is either in the same child as `li`, or in the sibling of `li` (and then `li ≠ li'`).
-/
theorem Tree.child_eq_or_sibling {l: Nat} (t: Tree Leaf Node (l+1)) {li li': Nat}
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  ((t.child li).containsLeafIndex li' ∧ t.child li' = t.child li) ∨ (t.child li' = t.sibling li ∧ li ≠ li')
:= by
  obtain ⟨p, bt⟩ := t
  cases bt
  grind [Tree.child_node, Tree.sibling_node, Tree.containsLeafIndex, Nat.pow_succ]

theorem eq_of_containsLeafIndex_zero {t: Tree Leaf Node 0} {li li': Nat}
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'): li = li'
:= by
  grind [Tree.containsLeafIndex]

/-! ## Induction principles -/

/-- Induction on a tree, with induction hypotheses on its left and right halves. -/
@[elab_as_elim]
theorem Tree.leftRightInduction {motive: (l: Nat) → Tree Leaf Node l → Prop}
  (leaf: ∀ (t: Tree Leaf Node 0), motive 0 t)
  (node: ∀ {l: Nat} (t: Tree Leaf Node (l+1)), motive l t.left → motive l t.right → motive (l+1) t):
  ∀ {l: Nat} (t: Tree Leaf Node l), motive l t
| 0, t => leaf t
| _+1, t => node t (Tree.leftRightInduction leaf node t.left) (Tree.leftRightInduction leaf node t.right)

/-- Induction on a tree, following the child for the leaf index `li`. -/
@[elab_as_elim]
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

end Mls
