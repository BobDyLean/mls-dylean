module

public import MLS.Common.Code.Tree
public import MLS.Comparse.Derived

/-!
Port of `MLS.Symbolic.Parsers`: message formats for trees and paths.

Port-specific differences:
- `ps_tree_index` and `ps_leaf_index` are not ported: tree and leaf indices are plain `Nat`s.
- Trees carry their position (MLS*'s index `i`, in the type): `BareTree.mf` is the port of `ps_tree`,
  and `Tree.mf` serializes the position (with `unboundedNat`, as MLS*'s `ps_tree_index`) before the bare tree.
- Paths are indexed by neither the tree index nor the leaf index: `Path.mf` only takes the height.
-/

namespace MLS

open Comparse

variable {Bytes: Type} [BytesLike Bytes] {Leaf Node: Type}

/-! ## Trees -/

namespace BareTree

public
def leafF (x: Leaf): BareTree Leaf Node 0 :=
  .leaf x

public
def leafG: BareTree Leaf Node 0 → Leaf
  | .leaf x => x

public
instance: LeftInverse (leafG (Leaf := Leaf) (Node := Node)) leafF := ⟨by intro _; rfl⟩
public
instance: RightInverse (leafG (Leaf := Leaf) (Node := Node)) leafF := ⟨by intro x; cases x; rfl⟩

/-- Port of `tree_internal_node` (with its fields `left`, `data`, `right`, in this order). -/
public
def nodeF {l: Nat}: BareTree Leaf Node l × Node × BareTree Leaf Node l → BareTree Leaf Node (l+1) :=
  fun (left, data, right) => .node data left right

public
def nodeG {l: Nat}: BareTree Leaf Node (l+1) → BareTree Leaf Node l × Node × BareTree Leaf Node l
  | .node data left right => (left, data, right)

public
instance {l: Nat}: LeftInverse (nodeG (Leaf := Leaf) (Node := Node) (l := l)) nodeF := ⟨by intro _; rfl⟩
public
instance {l: Nat}: RightInverse (nodeG (Leaf := Leaf) (Node := Node) (l := l)) nodeF := ⟨by intro x; cases x; rfl⟩

end BareTree

/-- Port of `ps_tree`. -/
@[expose]
public
def BareTree.mf (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node):
  (l: Nat) → NonExtensibleMessageFormat Bytes (BareTree Leaf Node l)
  | 0 => .isomorphic mfLeaf BareTree.leafF BareTree.leafG
  | l+1 =>
    .isomorphic (.prod (BareTree.mf mfLeaf mfNode l) (.prod mfNode (BareTree.mf mfLeaf mfNode l)))
      BareTree.nodeF BareTree.nodeG

namespace BareTree.mf

variable (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node)

public
instance [mfLeaf.IsNonAmbiguous] [mfNode.IsNonAmbiguous]:
  ∀ l, (BareTree.mf mfLeaf mfNode l).IsNonAmbiguous
  | 0 => by dsimp only [BareTree.mf]; infer_instance
  | l+1 => by
    have := instIsNonAmbiguous l
    dsimp only [BareTree.mf]
    infer_instance

public
instance [mfLeaf.HasUniqueRepresentation] [mfNode.HasUniqueRepresentation]:
  ∀ l, (BareTree.mf mfLeaf mfNode l).HasUniqueRepresentation
  | 0 => by dsimp only [BareTree.mf]; infer_instance
  | l+1 => by
    have := instHasUniqueRepresentation l
    dsimp only [BareTree.mf]
    infer_instance

public
instance [mfLeaf.ParseConsumes]:
  ∀ l, (BareTree.mf mfLeaf mfNode l).ParseConsumes
  | 0 => by dsimp only [BareTree.mf]; infer_instance
  | l+1 => by
    have := instParseConsumes l
    dsimp only [BareTree.mf]
    infer_instance

/-- Port of `ps_tree_is_well_formed` (leaf case). -/
@[simp]
public
theorem wf_leaf (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Leaf):
  (BareTree.mf mfLeaf mfNode 0).wf pred (.leaf x) = mfLeaf.wf pred x
:= by
  simp [BareTree.mf, BareTree.leafG]

/-- Port of `ps_tree_is_well_formed` (node case). -/
@[simp]
public
theorem wf_node {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: Node) (left right: BareTree Leaf Node l):
  (BareTree.mf mfLeaf mfNode (l+1)).wf pred (.node x left right) = (
    mfNode.wf pred x ∧ (BareTree.mf mfLeaf mfNode l).wf pred left ∧ (BareTree.mf mfLeaf mfNode l).wf pred right
  )
:= by
  simp only [BareTree.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, BareTree.nodeG,
    NonExtensibleMessageFormat.prod.wf_eq]
  grind

end BareTree.mf

namespace Tree

public
def f {l: Nat}: Nat × BareTree Leaf Node l → Tree Leaf Node l :=
  fun (position, bareTree) => { position, bareTree }

public
def g {l: Nat}: Tree Leaf Node l → Nat × BareTree Leaf Node l :=
  fun { position, bareTree } => (position, bareTree)

public
instance {l: Nat}: LeftInverse (g (Leaf := Leaf) (Node := Node) (l := l)) f := ⟨by intro _; rfl⟩
public
instance {l: Nat}: RightInverse (g (Leaf := Leaf) (Node := Node) (l := l)) f := ⟨by intro _; rfl⟩

end Tree

/-- Message format for trees: the position (MLS*'s `ps_tree_index`), then the bare tree (MLS*'s `ps_tree`). -/
@[expose]
public
def Tree.mf (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node) (l: Nat):
  NonExtensibleMessageFormat Bytes (Tree Leaf Node l)
:=
  .isomorphic (.prod .unboundedNat (BareTree.mf mfLeaf mfNode l)) Tree.f Tree.g

namespace Tree.mf

variable (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node)

public
instance (l: Nat) [mfLeaf.IsNonAmbiguous] [mfNode.IsNonAmbiguous]: (Tree.mf mfLeaf mfNode l).IsNonAmbiguous := by
  dsimp only [Tree.mf]
  infer_instance

public
instance (l: Nat) [mfLeaf.HasUniqueRepresentation] [mfNode.HasUniqueRepresentation]:
  (Tree.mf mfLeaf mfNode l).HasUniqueRepresentation
:= by
  dsimp only [Tree.mf]
  infer_instance

public
instance (l: Nat): (Tree.mf mfLeaf mfNode l).ParseConsumes := by
  dsimp only [Tree.mf]
  infer_instance

/-- Not `@[simp]`: use `wf_pack_leaf` / `wf_pack_node` (and `wf_zero` / `wf_succ`) on trees built from views. -/
public
theorem wf_eq {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred] (t: Tree Leaf Node l):
  (Tree.mf mfLeaf mfNode l).wf pred t = (BareTree.mf mfLeaf mfNode l).wf pred t.bareTree
:= by
  simp [Tree.mf, Tree.g]

/-- Port of `ps_tree_is_well_formed` (leaf case), on views. -/
@[simp]
public
theorem wf_pack_leaf (pred: Bytes → Prop) [BytesCompatiblePred pred] (content: Leaf) (position: Nat):
  (Tree.mf mfLeaf mfNode 0).wf pred (LeftRightView.leaf content position).pack = mfLeaf.wf pred content
:= by
  simp [LeftRightView.pack, wf_eq]

/-- Port of `ps_tree_is_well_formed` (node case), on views. -/
@[simp]
public
theorem wf_pack_node {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (content: Node) (left right: Tree Leaf Node l):
  (Tree.mf mfLeaf mfNode (l+1)).wf pred (LeftRightView.node content left right).pack = (
    mfNode.wf pred content ∧ (Tree.mf mfLeaf mfNode l).wf pred left ∧ (Tree.mf mfLeaf mfNode l).wf pred right
  )
:= by
  simp [LeftRightView.pack, wf_eq]

/-- Port of `ps_tree_is_well_formed` (leaf case), on child / sibling views. -/
@[simp]
public
theorem wf_pack_childSibling_leaf (pred: Bytes → Prop) [BytesCompatiblePred pred] (content: Leaf) (position: Nat):
  (Tree.mf mfLeaf mfNode 0).wf pred (ChildSiblingView.leaf content position).pack = mfLeaf.wf pred content
:= by
  simp [ChildSiblingView.pack]

/-- Port of `ps_tree_is_well_formed` (node case), on child / sibling views. -/
@[simp]
public
theorem wf_pack_childSibling_node {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (content: Node) (child sibling: Tree Leaf Node l):
  (Tree.mf mfLeaf mfNode (l+1)).wf pred (ChildSiblingView.node content child sibling).pack = (
    mfNode.wf pred content ∧ (Tree.mf mfLeaf mfNode l).wf pred child ∧ (Tree.mf mfLeaf mfNode l).wf pred sibling
  )
:= by
  simp only [ChildSiblingView.pack]
  split <;> simp only [wf_pack_node] <;> grind

/-- Well-formedness of a leaf, through its projections. -/
public
theorem wf_zero (pred: Bytes → Prop) [BytesCompatiblePred pred] (t: Tree Leaf Node 0):
  (Tree.mf mfLeaf mfNode 0).wf pred t = mfLeaf.wf pred t.leafContent
:= by
  obtain ⟨_, bt⟩ := t
  cases bt
  simp [Tree.leafContent, wf_eq]

/-- Well-formedness of a node, through its projections. -/
public
theorem wf_succ {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred] (t: Tree Leaf Node (l+1)):
  (Tree.mf mfLeaf mfNode (l+1)).wf pred t = (
    mfNode.wf pred t.nodeContent ∧ (Tree.mf mfLeaf mfNode l).wf pred t.left ∧ (Tree.mf mfLeaf mfNode l).wf pred t.right
  )
:= by
  obtain ⟨_, bt⟩ := t
  cases bt
  simp [Tree.nodeContent, Tree.left, Tree.right, Tree.intoLeftRightView, wf_eq]

end Tree.mf

/-! ## Paths -/

namespace Path

public
def leafF (x: Leaf): Path Leaf Node 0 :=
  .leaf x

public
def leafG: Path Leaf Node 0 → Leaf
  | .leaf x => x

public
instance: LeftInverse (leafG (Leaf := Leaf) (Node := Node)) leafF := ⟨by intro _; rfl⟩
public
instance: RightInverse (leafG (Leaf := Leaf) (Node := Node)) leafF := ⟨by intro x; cases x; rfl⟩

/-- Port of `path_internal_node` (with its fields `data`, `next`, in this order). -/
public
def nodeF {l: Nat}: Node × Path Leaf Node l → Path Leaf Node (l+1) :=
  fun (data, next) => .node data next

public
def nodeG {l: Nat}: Path Leaf Node (l+1) → Node × Path Leaf Node l
  | .node data next => (data, next)

public
instance {l: Nat}: LeftInverse (nodeG (Leaf := Leaf) (Node := Node) (l := l)) nodeF := ⟨by intro _; rfl⟩
public
instance {l: Nat}: RightInverse (nodeG (Leaf := Leaf) (Node := Node) (l := l)) nodeF := ⟨by intro x; cases x; rfl⟩

end Path

/-- Port of `ps_path`. -/
public
def Path.mf (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node):
  (l: Nat) → NonExtensibleMessageFormat Bytes (Path Leaf Node l)
  | 0 => .isomorphic mfLeaf Path.leafF Path.leafG
  | l+1 => .isomorphic (.prod mfNode (Path.mf mfLeaf mfNode l)) Path.nodeF Path.nodeG

namespace Path.mf

variable (mfLeaf: NonExtensibleMessageFormat Bytes Leaf) (mfNode: NonExtensibleMessageFormat Bytes Node)

public
instance [mfLeaf.IsNonAmbiguous] [mfNode.IsNonAmbiguous]:
  ∀ l, (Path.mf mfLeaf mfNode l).IsNonAmbiguous
  | 0 => by dsimp only [Path.mf]; infer_instance
  | l+1 => by
    have := instIsNonAmbiguous l
    dsimp only [Path.mf]
    infer_instance

public
instance [mfLeaf.HasUniqueRepresentation] [mfNode.HasUniqueRepresentation]:
  ∀ l, (Path.mf mfLeaf mfNode l).HasUniqueRepresentation
  | 0 => by dsimp only [Path.mf]; infer_instance
  | l+1 => by
    have := instHasUniqueRepresentation l
    dsimp only [Path.mf]
    infer_instance

public
instance [mfLeaf.ParseConsumes]:
  ∀ l, (Path.mf mfLeaf mfNode l).ParseConsumes
  | 0 => by dsimp only [Path.mf]; infer_instance
  | l+1 => by
    have := instParseConsumes l
    dsimp only [Path.mf]
    infer_instance

/-- Port of `ps_path_is_well_formed` (leaf case). -/
@[simp]
public
theorem wf_leaf (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Leaf):
  (Path.mf mfLeaf mfNode 0).wf pred (.leaf x) = mfLeaf.wf pred x
:= by
  simp [Path.mf, Path.leafG]

/-- Port of `ps_path_is_well_formed` (node case). -/
@[simp]
public
theorem wf_node {l: Nat} (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: Node) (next: Path Leaf Node l):
  (Path.mf mfLeaf mfNode (l+1)).wf pred (.node x next) = (mfNode.wf pred x ∧ (Path.mf mfLeaf mfNode l).wf pred next)
:= by
  simp [Path.mf, Path.nodeG]

end Path.mf

end MLS
