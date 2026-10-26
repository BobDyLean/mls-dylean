module

public import MLS.Common.Code.Crypto.Derived
public import MLS.TreeSync.Code.Types

/-!
Port of `MLS.TreeSync.TreeHash`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

/-! ## Formats -/

section Formats

variable {Bytes: Type} [BytesLike Bytes]

/--
struct {
    uint32 leaf_index;
    optional<LeafNode> leaf_node;
} LeafNodeHashInput;
-/
public
structure LeafNodeTreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  leafIndex: UInt32
  leafNode: Option (LeafNode Bytes tkt)

namespace LeafNodeTreeHashInput

variable {tkt: TreeKEMTypes Bytes}

@[expose]
public
def f: UInt32 × Option (LeafNode Bytes tkt) → LeafNodeTreeHashInput Bytes tkt :=
  fun (leafIndex, leafNode) => { leafIndex, leafNode }

@[expose]
public
def g: LeafNodeTreeHashInput Bytes tkt → UInt32 × Option (LeafNode Bytes tkt) :=
  fun { leafIndex, leafNode } => (leafIndex, leafNode)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end LeafNodeTreeHashInput

@[expose]
public
def LeafNodeTreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (LeafNodeTreeHashInput Bytes tkt) :=
  .isomorphic (.prod .uint32BE (MlsOption.mf (LeafNode.mf tkt))) LeafNodeTreeHashInput.f LeafNodeTreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem LeafNodeTreeHashInput.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: LeafNodeTreeHashInput Bytes tkt):
  (LeafNodeTreeHashInput.mf tkt).wf pred x = (MlsOption.mf (LeafNode.mf tkt)).wf pred x.leafNode
:= by
  simp [LeafNodeTreeHashInput.mf, LeafNodeTreeHashInput.g]

/--
struct {
    optional<ParentNode> parent_node;
    opaque left_hash<V>;
    opaque right_hash<V>;
} ParentNodeHashInput;
-/
public
structure ParentNodeTreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  parentNode: Option (ParentNode Bytes tkt)
  leftHash: MlsBytes Bytes
  rightHash: MlsBytes Bytes

namespace ParentNodeTreeHashInput

variable {tkt: TreeKEMTypes Bytes}

@[expose]
public
def f: Option (ParentNode Bytes tkt) × MlsBytes Bytes × MlsBytes Bytes → ParentNodeTreeHashInput Bytes tkt :=
  fun (parentNode, leftHash, rightHash) => { parentNode, leftHash, rightHash }

@[expose]
public
def g: ParentNodeTreeHashInput Bytes tkt → Option (ParentNode Bytes tkt) × MlsBytes Bytes × MlsBytes Bytes :=
  fun { parentNode, leftHash, rightHash } => (parentNode, leftHash, rightHash)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end ParentNodeTreeHashInput

@[expose]
public
def ParentNodeTreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (ParentNodeTreeHashInput Bytes tkt) :=
  .isomorphic (.prod (MlsOption.mf (ParentNode.mf tkt)) (.prod MlsBytes.mf MlsBytes.mf))
    ParentNodeTreeHashInput.f ParentNodeTreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ParentNodeTreeHashInput.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ParentNodeTreeHashInput Bytes tkt):
  (ParentNodeTreeHashInput.mf tkt).wf pred x = (
    (MlsOption.mf (ParentNode.mf tkt)).wf pred x.parentNode ∧ pred x.leftHash.val ∧ pred x.rightHash.val
  )
:= by
  simp [ParentNodeTreeHashInput.mf, ParentNodeTreeHashInput.g]

/--
struct {
  NodeType node_type;
  select (TreeHashInput.node_type) {
    case leaf:   LeafNodeHashInput leaf_node;
    case parent: ParentNodeHashInput parent_node;
  };
} TreeHashInput;
-/
public
inductive TreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  | leaf: LeafNodeTreeHashInput Bytes tkt → TreeHashInput Bytes tkt
  | parent: ParentNodeTreeHashInput Bytes tkt → TreeHashInput Bytes tkt

namespace TreeHashInput

variable {tkt: TreeKEMTypes Bytes}

@[expose]
public
def internalType (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes): NodeType → Type
  | .leaf => LeafNodeTreeHashInput Bytes tkt
  | .parent => ParentNodeTreeHashInput Bytes tkt

@[expose]
public
def internalType.mf (tkt: TreeKEMTypes Bytes): (t: NodeType) → NonExtensibleMessageFormat Bytes (internalType Bytes tkt t)
  | .leaf => LeafNodeTreeHashInput.mf tkt
  | .parent => ParentNodeTreeHashInput.mf tkt

public
instance: ∀ t, (internalType.mf tkt t).IsNonAmbiguous
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
instance: ∀ t, (internalType.mf tkt t).HasUniqueRepresentation
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

@[expose]
public
def f: (t: NodeType) × internalType Bytes tkt t → TreeHashInput Bytes tkt
  | ⟨.leaf, x⟩ => .leaf x
  | ⟨.parent, x⟩ => .parent x

@[expose]
public
def g: TreeHashInput Bytes tkt → (t: NodeType) × internalType Bytes tkt t
  | .leaf x => ⟨.leaf, x⟩
  | .parent x => ⟨.parent, x⟩

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro x; cases x <;> rfl⟩

end TreeHashInput

@[expose]
public
def TreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (TreeHashInput Bytes tkt) :=
  .isomorphic (.sigma NodeType.mf (TreeHashInput.internalType.mf tkt)) TreeHashInput.f TreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem TreeHashInput.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeHashInput Bytes tkt):
  (TreeHashInput.mf tkt).wf pred x = (
    match x with
    | .leaf x => (LeafNodeTreeHashInput.mf tkt).wf pred x
    | .parent x => (ParentNodeTreeHashInput.mf tkt).wf pred x
  )
:= by
  cases x <;> simp [TreeHashInput.mf, TreeHashInput.g] <;> simp [TreeHashInput.internalType.mf, TreeHashInput.internalType]

end Formats

/-! ## Tree hash -/

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `tree_hash`.
Compute the tree hash of a tree.
-/
@[expose]
public
def treeHash {l: Nat} (t: TreeSync Bytes tkt l): Result Bytes :=
  match t.intoLeftRightView with
  | .leaf olp position => do
    let i ← mkUInt32 position "tree_hash" "i"
    let hashInput := serializeNE (TreeHashInput.mf tkt) (.leaf { leafIndex := i, leafNode := olp })
    CryptoBytes.hashHash hashInput
  | .node onp left right => do
    let leftHash ← treeHash left
    let leftHash ← mkMlsBytes leftHash "tree_hash" "left_bytes"
    let rightHash ← treeHash right
    let rightHash ← mkMlsBytes rightHash "tree_hash" "right_bytes"
    let hashInput := serializeNE (TreeHashInput.mf tkt) (.parent { parentNode := onp, leftHash, rightHash })
    CryptoBytes.hashHash hashInput

end MLS.TreeSync
