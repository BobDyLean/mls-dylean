/-!
Port of `MLS.Tree`.

Port-specific differences:
- MLS*'s `tree leaf_t node_t l i` is split in two types:
  `BareTree Leaf Node l` is the bare tree of height `l`,
  and `Tree Leaf Node l` bundles it with its position (the leaf index of its leftmost leaf, MLS*'s `i`).
  The position is not in the type: in Lean, the child of a tree for a leaf index `li`
  would otherwise have a type depending on `li` (`if is_left_leaf li then left_index i else right_index i`),
  requiring casts.
- Leaf indices are plain `Nat`s (MLS*'s `leaf_index l i` is a refinement `leaf_index_inside l i li`).
  Functions follow the child / sibling view, lemmas take `Tree.containsLeafIndex` hypotheses.
- Trees are destructed with views:
  `LeftRightView` (MLS*'s matching on `TNode content left right`)
  and `ChildSiblingView` (MLS*'s `get_child_sibling`), which come with their `pack` function.
- `path` is only indexed by its height `l` (see `Path`).
-/

namespace Mls

/-! ## Trees -/

/-- Bare complete binary tree, with height `l`. -/
inductive BareTree (Leaf Node: Type): Nat → Type where
  | leaf (content: Leaf): BareTree Leaf Node 0
  | node {l: Nat} (content: Node) (left right: BareTree Leaf Node l): BareTree Leaf Node (l+1)

/--
Complete binary tree, with height `l`: a bare tree together with its position,
the leaf index of its leftmost leaf.
Port of MLS*'s `tree leaf_t node_t l i`, where `i` is the position.
-/
structure Tree (Leaf Node: Type) (l: Nat) where
  position: Nat
  bareTree: BareTree Leaf Node l

/-- Port of `node_index`: the height and position of a subtree. -/
structure NodeIndex where
  levels: Nat
  position: Nat
deriving DecidableEq

/-- Port of `nat_to_node_index`. -/
def NodeIndex.ofLeafIndex (leafIndex: Nat): NodeIndex :=
  { levels := 0, position := leafIndex }

variable {Leaf Node: Type}

def Tree.nodeIndex {l: Nat} (t: Tree Leaf Node l): NodeIndex :=
  { levels := l, position := t.position }

/-- Port of `leaf_index_inside_tree`. -/
def Tree.containsLeafIndex {l: Nat} (t: Tree Leaf Node l) (li: Nat): Bool :=
  t.position ≤ li && li < t.position + 2^l

/-! ## Left / right view -/

inductive LeftRightView (Leaf Node: Type): Nat → Type where
  | leaf (content: Leaf) (position: Nat): LeftRightView Leaf Node 0
  | node {l: Nat} (content: Node) (left right: Tree Leaf Node l): LeftRightView Leaf Node (l+1)

def Tree.intoLeftRightView {l: Nat} (t: Tree Leaf Node l): LeftRightView Leaf Node l :=
  match l, t with
  | _, { position, bareTree := .leaf content } => .leaf content position
  | l+1, { position, bareTree := .node content left right } =>
    .node content
      { position, bareTree := left }
      { position := position + 2^l, bareTree := right }

def LeftRightView.pack {l: Nat}: LeftRightView Leaf Node l → Tree Leaf Node l
  | .leaf content position => { position, bareTree := .leaf content }
  | .node content left right => { position := left.position, bareTree := .node content left.bareTree right.bareTree }

/-! ## Child / sibling view -/

/--
When dealing with a subtree and a specific leaf in this subtree,
MLS use the term `child` for the child of the subtree containing the leaf,
and the term `sibling` for the other child (that doesn't contain the leaf).
-/
inductive ChildSiblingView (Leaf Node: Type): Nat → Type where
  | leaf (content: Leaf) (position: Nat): ChildSiblingView Leaf Node 0
  | node {l: Nat} (content: Node) (child sibling: Tree Leaf Node l): ChildSiblingView Leaf Node (l+1)

/--
Port of `get_child_sibling`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the child is the left one if `li` is before the tree, and the right one if `li` is after the tree.
-/
def Tree.intoChildSiblingView {l: Nat} (t: Tree Leaf Node l) (li: Nat): ChildSiblingView Leaf Node l :=
  match t.intoLeftRightView with
  | .leaf content position => .leaf content position
  | .node content left right =>
    if li < right.position then
      .node content left right
    else
      .node content right left

def ChildSiblingView.pack {l: Nat}: ChildSiblingView Leaf Node l → Tree Leaf Node l
  | .leaf content position => (LeftRightView.leaf content position).pack
  | .node content child sibling =>
    if child.position < sibling.position then
      (LeftRightView.node content child sibling).pack
    else
      (LeftRightView.node content sibling child).pack

/-! ## Projections of the left / right view -/

def Tree.nodeContent {l: Nat} (t: Tree Leaf Node (l+1)): Node :=
  match t.intoLeftRightView with
  | .node content _ _ => content

def Tree.left {l: Nat} (t: Tree Leaf Node (l+1)): Tree Leaf Node l :=
  match t.intoLeftRightView with
  | .node _ left _ => left

def Tree.right {l: Nat} (t: Tree Leaf Node (l+1)): Tree Leaf Node l :=
  match t.intoLeftRightView with
  | .node _ _ right => right

/-! ## Projections of the child / sibling view -/

/-- MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`); otherwise, see `Tree.intoChildSiblingView`. -/
def Tree.child {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat): Tree Leaf Node l :=
  match t.intoChildSiblingView li with
  | .node _ child _ => child

/-- MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`); otherwise, see `Tree.intoChildSiblingView`. -/
def Tree.sibling {l: Nat} (t: Tree Leaf Node (l+1)) (li: Nat): Tree Leaf Node l :=
  match t.intoChildSiblingView li with
  | .node _ _ sibling => sibling

def Tree.leafContent (t: Tree Leaf Node 0): Leaf :=
  match t.bareTree with
  | .leaf content => content

/-! ## Tree functions -/

/-- Port of `get_leaf_list`. -/
def getLeafList {l: Nat} (t: Tree Leaf Node l): List Leaf :=
  match t.intoLeftRightView with
  | .leaf content _ => [content]
  | .node _ left right => getLeafList left ++ getLeafList right

/--
Port of `leaf_at`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def leafAt {l: Nat} (t: Tree Leaf Node l) (li: Nat): Leaf :=
  match t.intoChildSiblingView li with
  | .leaf content _ => content
  | .node _ child _ => leafAt child li

/-- Port of `print_tree`. -/
def Tree.toString (printLeaf: Leaf → String) (printNode: Node → String) {l: Nat} (t: Tree Leaf Node l): String :=
  match t.intoLeftRightView with
  | .leaf content _ => printLeaf content
  | .node content left right =>
    "(" ++ left.toString printLeaf printNode ++ ") " ++ printNode content ++ " (" ++ right.toString printLeaf printNode ++ ")"

/-- Port of `tree_map`. -/
def Tree.map {Leaf' Node': Type} (fLeaf: Leaf → Leaf') (fNode: Node → Node') {l: Nat} (t: Tree Leaf Node l):
  Tree Leaf' Node' l
:=
  match t.intoLeftRightView with
  | .leaf content position => (LeftRightView.leaf (fLeaf content) position).pack
  | .node content left right => (LeftRightView.node (fNode content) (left.map fLeaf fNode) (right.map fLeaf fNode)).pack

/-! ## Paths -/

/--
Type for path in a tree of height `l`, from the root down to some leaf.
Unlike MLS*, the path is not indexed by the tree index `i` and the leaf index `li`:
functions recursing on a tree and a path take the leaf index as an explicit argument,
and use it to know on which side the path goes.
-/
inductive Path (Leaf Node: Type): (l: Nat) → Type where
  | leaf (data: Leaf): Path Leaf Node 0
  | node {l: Nat} (data: Node) (next: Path Leaf Node l): Path Leaf Node (l+1)

namespace Path

/-- Port of `get_path_leaf`. -/
def getPathLeaf: {l: Nat} → Path Leaf Node l → Leaf
  | _, .leaf lp => lp
  | _, .node _ next => getPathLeaf next

/-- Port of `set_path_leaf`. -/
def setPathLeaf {Leaf': Type}: {l: Nat} → Path Leaf Node l → Leaf' → Path Leaf' Node l
  | _, .leaf _, lp => .leaf lp
  | _, .node content next, lp => .node content (setPathLeaf next lp)

end Path

end Mls
