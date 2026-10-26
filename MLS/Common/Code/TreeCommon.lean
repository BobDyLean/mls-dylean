module

public import MLS.Common.Code.Tree

/-!
Port of `MLS.TreeCommon`.

Port-specific differences:
- Functions recurse on the views of `MLS.Tree`: `ChildSiblingView` for functions following a leaf index
  (`treeChangePath`), `LeftRightView` for functions visiting both children.
- Leaf indices are plain `Nat`s (see `MLS.Tree`): `treeChangePath` follows the child / sibling view for `li`.
- `find_empty_leaf` returns a leaf index, without proof of `leaf_at t li == None` (see `findEmptyLeaf_spec`).
-/

namespace MLS

variable {Leaf Node: Type}

/-! ## Tree creation -/

/-- Port of `tree_create`. -/
@[expose]
public
def treeCreate (lp: Leaf): Tree (Option Leaf) Node 0 :=
  (LeftRightView.leaf (some lp) 0).pack

/-! ## Common tree operations -/

/--
Port of `tree_change_path`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def treeChangePath {l: Nat} (t: Tree Leaf Node l) (li: Nat) (leafContent: Leaf) (nodeContent: Node): Tree Leaf Node l :=
  match t.intoChildSiblingView li with
  | .leaf _ position => (ChildSiblingView.leaf leafContent position).pack
  | .node _ child sibling => (ChildSiblingView.node nodeContent (treeChangePath child li leafContent nodeContent) sibling).pack
-- Well-founded recursion: with structural recursion,
-- Lean fails to generate the equation lemmas used by `unfold` in `MLS.TreeCommon.Lemmas`.
termination_by l

/--
Port of `tree_update`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def treeUpdate {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat) (lp: Leaf): Tree (Option Leaf) (Option Node) l :=
  treeChangePath t li (some lp) none

/--
Port of `tree_remove`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
@[expose]
public
def treeRemove {l: Nat} (t: Tree (Option Leaf) (Option Node) l) (li: Nat): Tree (Option Leaf) (Option Node) l :=
  treeChangePath t li none none

/-! ## Tree extension / truncation -/

/-- Port of `is_tree_empty`. -/
@[expose]
public
def isTreeEmpty {l: Nat} (t: Tree (Option Leaf) (Option Node) l): Bool :=
  match t.intoLeftRightView with
  | .leaf content _ => content.isNone
  | .node content left right => content.isNone && isTreeEmpty left && isTreeEmpty right

/--
Port of `tree_truncate`.
MLS* requires `is_tree_empty (TNode?.right t)`; otherwise, the right subtree is dropped.
-/
@[expose]
public
def treeTruncate {l: Nat} (t: Tree (Option Leaf) (Option Node) (l+1)): Tree (Option Leaf) (Option Node) l :=
  t.left

-- Helper functions to add leaf / extend the tree

/-- Port of `find_empty_leaf`. -/
@[expose]
public
def findEmptyLeaf {l: Nat} (t: Tree (Option Leaf) (Option Node) l): Option Nat :=
  match t.intoLeftRightView with
  | .leaf content position => if content.isNone then some position else none
  | .node _ left right =>
    match findEmptyLeaf left with
    | some x => some x
    | none => findEmptyLeaf right

/-- Port of `mk_blank_tree_general`. -/
@[expose]
public
def mkBlankTreeGeneral: (l: Nat) → (position: Nat) → (leafContent: Leaf) → (nodeContent: Node) → Tree Leaf Node l
  | 0, position, leafContent, _ => (LeftRightView.leaf leafContent position).pack
  | l+1, position, leafContent, nodeContent =>
    (LeftRightView.node nodeContent
      (mkBlankTreeGeneral l position leafContent nodeContent)
      (mkBlankTreeGeneral l (position + 2^l) leafContent nodeContent)).pack

/-- Port of `mk_blank_tree`. -/
@[expose]
public
def mkBlankTree (l: Nat) (position: Nat): Tree (Option Leaf) (Option Node) l :=
  mkBlankTreeGeneral l position none none

/-- Port of `tree_extend`. -/
@[expose]
public
def treeExtend {l: Nat} (t: Tree (Option Leaf) (Option Node) l): Tree (Option Leaf) (Option Node) (l+1) :=
  (LeftRightView.node none t (mkBlankTree l (t.position + 2^l))).pack

/-! ## Add helper -/

/-- Port of `insert_sorted`. -/
@[expose]
public
def insertSorted {α: Type} [LT α] [DecidableLT α] [DecidableEq α] (x: α): List α → List α
  | [] => [x]
  | h::t =>
    if x < h then x::h::t
    else if x = h then h::t
    else h::(insertSorted x t)

end MLS
