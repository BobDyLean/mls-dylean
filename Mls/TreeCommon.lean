import Mls.Tree

/-!
Port of `MLS.TreeCommon`.

Port-specific differences:
- `tree_truncate` takes the emptiness of the right subtree as a separate hypothesis
  (in F*, it is a refinement mentioning `TNode?.right t`).
- `find_empty_leaf` returns a leaf index together with a proof of `leaf_at t li == None`, as a subtype.
-/

namespace Mls

namespace Tree

variable {Leaf Node: Type}

/-! ## Tree creation -/

def treeCreate (lp: Leaf): Tree (Option Leaf) Node 0 (TreeIndex.zero 0) :=
  .leaf (some lp)

/-! ## Common tree operations -/

def treeChangePath: {l: Nat} → {i: TreeIndex l} → Tree Leaf Node l i → LeafIndex l i → Leaf → Node → Tree Leaf Node l i
  | _, _, .leaf _, _, leafContent, _ => .leaf leafContent
  | _, _, .node _ left right, li, leafContent, nodeContent =>
    if h: isLeftLeaf li then
      .node nodeContent (treeChangePath left (li.childOfLeft h) leafContent nodeContent) right
    else
      .node nodeContent left (treeChangePath right (li.childOfRight (by simpa using h)) leafContent nodeContent)

def treeUpdate {l: Nat} {i: TreeIndex l} (t: Tree (Option Leaf) (Option Node) l i) (li: LeafIndex l i) (lp: Leaf):
  Tree (Option Leaf) (Option Node) l i
:=
  treeChangePath t li (some lp) none

def treeRemove {l: Nat} {i: TreeIndex l} (t: Tree (Option Leaf) (Option Node) l i) (li: LeafIndex l i):
  Tree (Option Leaf) (Option Node) l i
:=
  treeChangePath t li none none

/-! ## Tree extension / truncation -/

def isTreeEmpty: {l: Nat} → {i: TreeIndex l} → Tree (Option Leaf) (Option Node) l i → Bool
  | _, _, .node (some _) _ _ => false
  | _, _, .node none left right => isTreeEmpty left && isTreeEmpty right
  | _, _, .leaf (some _) => false
  | _, _, .leaf none => true

def right {l: Nat} {i: TreeIndex (l+1)}: Tree Leaf Node (l+1) i → Tree Leaf Node l i.right
  | .node _ _ right => right

def left {l: Nat} {i: TreeIndex (l+1)}: Tree Leaf Node (l+1) i → Tree Leaf Node l i.left
  | .node _ left _ => left

/--
Port of `tree_truncate`.
The left child of `TreeIndex.zero (l+1)` is definitionally `TreeIndex.zero l`.
-/
def treeTruncate {l: Nat} (t: Tree (Option Leaf) (Option Node) (l+1) (TreeIndex.zero (l+1)))
  (_: isTreeEmpty t.right):
  Tree (Option Leaf) (Option Node) l (TreeIndex.zero l)
:=
  t.left

-- Helper functions to add leaf / extend the tree

def findEmptyLeaf: {l: Nat} → {i: TreeIndex l} → (t: Tree (Option Leaf) (Option Node) l i) →
  Option {li: LeafIndex l i // leafAt t li = none}
  | _, _, .leaf (some _) => none
  | _, i, .leaf none => some ⟨⟨i.val, by simp [leafIndexInside]⟩, rfl⟩
  | _, _, .node _ left right =>
    match findEmptyLeaf left, findEmptyLeaf right with
    | some x, _ => some ⟨x.val.ofLeft, by rw [leafAt_ofLeft]; exact x.property⟩
    | none, some x => some ⟨x.val.ofRight, by rw [leafAt_ofRight]; exact x.property⟩
    | none, none => none

def mkBlankTreeGeneral (leafContent: Leaf) (nodeContent: Node): (l: Nat) → (i: TreeIndex l) → Tree Leaf Node l i
  | 0, _ => .leaf leafContent
  | l+1, i => .node nodeContent (mkBlankTreeGeneral leafContent nodeContent l i.left) (mkBlankTreeGeneral leafContent nodeContent l i.right)

def mkBlankTree (l: Nat) (i: TreeIndex l): Tree (Option Leaf) (Option Node) l i :=
  mkBlankTreeGeneral none none l i

/-- The left child of `TreeIndex.zero (l+1)` is definitionally `TreeIndex.zero l`. -/
def treeExtend {l: Nat} (t: Tree (Option Leaf) (Option Node) l (TreeIndex.zero l)):
  Tree (Option Leaf) (Option Node) (l+1) (TreeIndex.zero (l+1))
:=
  .node none t (mkBlankTree l _)

end Tree

/-! ## Add helper -/

def insertSorted (x: UInt32): List UInt32 → List UInt32
  | [] => [x]
  | h::t =>
    if x < h then x::h::t
    else if x = h then h::t
    else h::(insertSorted x t)

end Mls
