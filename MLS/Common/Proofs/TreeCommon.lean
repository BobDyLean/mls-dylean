module

public import MLS.Common.Code.TreeCommon
public import MLS.Common.Proofs.Tree

/-!
Port of `MLS.TreeCommon.Lemmas`.

Port-specific differences:
- Leaf indices are plain `Nat`s: lemmas take `Tree.containsLeafIndex` hypotheses
  (MLS*'s refinement `leaf_index l i`).
- Proofs unfold the functions and reason on the views, with the lemmas of `MLS.Tree.Lemmas`.
-/

namespace MLS

variable {Leaf Node: Type}

public
theorem mem_insertSorted {α: Type} [LT α] [DecidableLT α] [DecidableEq α] (x: α) (l: List α) (elem: α):
  elem ∈ insertSorted x l ↔ elem = x ∨ elem ∈ l
:= by
  induction l <;> grind [insertSorted]

grind_pattern mem_insertSorted => elem ∈ insertSorted x l

/-! ## `treeChangePath`, `treeUpdate` and `treeRemove` -/

@[simp]
public
theorem treeChangePath_position {l: Nat} (t: Tree Leaf Node l) (li: Nat) (leafContent: Leaf) (nodeContent: Node):
  (treeChangePath t li leafContent nodeContent).position = t.position
:= by
  induction t using Tree.childInduction li <;> unfold treeChangePath <;> simp_all

grind_pattern treeChangePath_position => (treeChangePath t li leafContent nodeContent).position

/-- Port of `leaf_at_tree_change_path`. -/
public
theorem leafAt_treeChangePath {l: Nat} (t: Tree Leaf Node l) (li: Nat) (leafContent: Leaf) (nodeContent: Node) (li': Nat)
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt (treeChangePath t li leafContent nodeContent) li' = if li = li' then leafContent else leafAt t li'
:= by
  induction t, hli, hli' using Tree.commonPathInduction li li' <;> unfold leafAt treeChangePath <;> simp_all

public
theorem treeChangePath_succ {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (leafContent: Leaf) (nodeContent: Node):
  treeChangePath t li leafContent nodeContent =
    (ChildSiblingView.node nodeContent (treeChangePath (t.child li) li leafContent nodeContent) (t.sibling li)).pack
:= by
  rw [treeChangePath.eq_def]
  simp

@[simp]
public
theorem child_treeChangePath {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (leafContent: Leaf) (nodeContent: Node):
  (treeChangePath t li leafContent nodeContent).child li = treeChangePath (t.child li) li leafContent nodeContent
:= by
  rw [treeChangePath_succ]
  simp

@[simp]
public
theorem sibling_treeChangePath {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (leafContent: Leaf) (nodeContent: Node):
  (treeChangePath t li leafContent nodeContent).sibling li = t.sibling li
:= by
  rw [treeChangePath_succ]
  simp

@[simp]
public
theorem nodeContent_treeChangePath {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat) (leafContent: Leaf) (nodeContent: Node):
  (treeChangePath t li leafContent nodeContent).nodeContent = nodeContent
:= by
  rw [treeChangePath_succ]
  simp

/-- Port of `leaf_at_tree_update`. -/
public
theorem leafAt_treeUpdate {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat) (leafContent: Leaf) (li': Nat)
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt (treeUpdate t li leafContent) li' = if li = li' then some leafContent else leafAt t li'
:=
  leafAt_treeChangePath t li (some leafContent) none li' hli hli'

/-- Port of `leaf_at_tree_remove`. -/
public
theorem leafAt_treeRemove {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat) (li': Nat)
  (hli: t.containsLeafIndex li) (hli': t.containsLeafIndex li'):
  leafAt (treeRemove t li) li' = if li = li' then none else leafAt t li'
:=
  leafAt_treeChangePath t li none none li' hli hli'

/-! ## Blank trees and tree extension -/

@[simp]
public
theorem mkBlankTreeGeneral_position (l p: Nat) (leafContent: Leaf) (nodeContent: Node):
  (mkBlankTreeGeneral l p leafContent nodeContent).position = p
:= by
  induction l generalizing p <;> simp_all [mkBlankTreeGeneral]

grind_pattern mkBlankTreeGeneral_position => (mkBlankTreeGeneral l p leafContent nodeContent).position

/-- Port of `leaf_at_mk_blank_tree_general`. -/
theorem leafAt_mkBlankTreeGeneral (l p: Nat) (leafContent: Leaf) (nodeContent: Node) (li: Nat):
  leafAt (mkBlankTreeGeneral l p leafContent nodeContent) li = leafContent
:= by
  induction l generalizing p <;> grind [leafAt.eq_def, mkBlankTreeGeneral]

/-- Port of `leaf_at_tree_extend`. -/
public
theorem leafAt_treeExtend {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat):
  leafAt (treeExtend t) li = if li < t.position + 2^l then leafAt t li else none
:= by
  grind [treeExtend, leafAt.eq_def, mkBlankTree, leafAt_mkBlankTreeGeneral]

public
theorem isTreeEmpty_zero (t: Tree (Option Leaf) (Option Node) 0): isTreeEmpty t = t.leafContent.isNone := by
  grind [isTreeEmpty.eq_def]

/-- `isTreeEmpty` of a node, through the child / sibling view for any leaf index `li`. -/
public
theorem isTreeEmpty_succ {l: Nat} (t: Tree (Option Leaf) (Option Node) (l+1)) (li: Nat):
  isTreeEmpty t = (t.nodeContent.isNone && isTreeEmpty (t.child li) && isTreeEmpty (t.sibling li))
:= by
  grind [isTreeEmpty.eq_def]

/-- Port of `is_tree_empty_leaf_at`. -/
public
theorem leafAt_of_isTreeEmpty {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat) (h: isTreeEmpty t):
  leafAt t li = none
:= by
  induction t using Tree.childInduction li <;> unfold leafAt <;> simp_all [isTreeEmpty_zero, isTreeEmpty_succ _ li]

/-- Port of the refinement on the result of `find_empty_leaf`. -/
public
theorem findEmptyLeaf_spec {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat) (h: findEmptyLeaf t = some li):
  t.containsLeafIndex li ∧ leafAt t li = none
:= by
  induction t using Tree.leftRightInduction generalizing li with
  | leaf t =>
    unfold findEmptyLeaf at h
    unfold leafAt
    simp at h ⊢
    grind [Tree.containsLeafIndex]
  | @node l t ihLeft ihRight =>
    unfold findEmptyLeaf at h
    have := Nat.two_pow_pos l
    grind [leafAt.eq_def, Tree.containsLeafIndex]

/-- Port of `find_empty_leaf_mk_blank_tree`. -/
theorem findEmptyLeaf_mkBlankTree (l p: Nat):
  (findEmptyLeaf (mkBlankTree l p: Tree (Option Leaf) (Option Node) l)).isSome
:= by
  induction l generalizing p with
  | zero => unfold findEmptyLeaf mkBlankTree mkBlankTreeGeneral; simp
  | succ l ih =>
    unfold findEmptyLeaf mkBlankTree mkBlankTreeGeneral
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ih p)
    simp only [mkBlankTree] at hx
    simp [LeftRightView.pack, Tree.intoLeftRightView, hx]

/-- Port of `find_empty_leaf_tree_extend`. -/
public
theorem findEmptyLeaf_treeExtend {l: Nat} (t: Tree (Option Leaf) (Option Node) l):
  (findEmptyLeaf (treeExtend t)).isSome
:= by
  unfold findEmptyLeaf treeExtend
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (findEmptyLeaf_mkBlankTree (Leaf := Leaf) (Node := Node) l (t.position + 2^l))
  simp only [LeftRightView.pack, Tree.intoLeftRightView]
  split <;> simp_all [mkBlankTree]

/-! ## Leaf list -/

public
theorem length_getLeafList {Leaf Node: Type} {l: Nat} (t: Tree Leaf Node l):
  (getLeafList t).length = 2^l
:= by
  induction t using Tree.leftRightInduction <;> rw [getLeafList.eq_def] <;> simp_all <;> grind

/--
Port of `index_get_leaf_list`.
Stated with `[ind]?`, which also gives the length of the list.
-/
public
theorem index_getLeafList {Leaf Node: Type} {l: Nat} (t: Tree Leaf Node l) (ind: Nat) (h: ind < 2^l):
  (getLeafList t)[ind]? = some (leafAt t (t.position + ind))
:= by
  induction t using Tree.leftRightInduction generalizing ind with
  | leaf t => simp_all [getLeafList.eq_def, leafAt.eq_def]
  | node t ihl ihr =>
    rw [getLeafList.eq_def, leafAt.eq_def]
    simp only [Tree.intoLeftRightView_eq, Tree.intoChildSiblingView_eq, List.getElem?_append, length_getLeafList]
    split
    · grind
    · have := ihr (ind - (getLeafList t.left).length) (by grind [length_getLeafList])
      grind [length_getLeafList]

end MLS
