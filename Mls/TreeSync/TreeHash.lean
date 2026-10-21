import Mls.Crypto.Derived
import Mls.TreeSync.Types

/-!
Port of `MLS.TreeSync.TreeHash`.
-/

namespace Mls.TreeSync

open Comparse
open Mls

/-! ## Formats -/

section Formats

variable {Bytes: Type} [BytesLike Bytes]

/--
struct {
    uint32 leaf_index;
    optional<LeafNode> leaf_node;
} LeafNodeHashInput;
-/
structure LeafNodeTreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  leafIndex: UInt32
  leafNode: Option (LeafNode Bytes tkt)

namespace LeafNodeTreeHashInput

variable {tkt: TreeKEMTypes Bytes}

def f: UInt32 × Option (LeafNode Bytes tkt) → LeafNodeTreeHashInput Bytes tkt :=
  fun (leafIndex, leafNode) => { leafIndex, leafNode }

def g: LeafNodeTreeHashInput Bytes tkt → UInt32 × Option (LeafNode Bytes tkt) :=
  fun { leafIndex, leafNode } => (leafIndex, leafNode)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end LeafNodeTreeHashInput

def LeafNodeTreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (LeafNodeTreeHashInput Bytes tkt) :=
  .isomorphic (.prod .uint32BE (MlsOption.mf (LeafNode.mf tkt))) LeafNodeTreeHashInput.f LeafNodeTreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
    optional<ParentNode> parent_node;
    opaque left_hash<V>;
    opaque right_hash<V>;
} ParentNodeHashInput;
-/
structure ParentNodeTreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  parentNode: Option (ParentNode Bytes tkt)
  leftHash: MlsBytes Bytes
  rightHash: MlsBytes Bytes

namespace ParentNodeTreeHashInput

variable {tkt: TreeKEMTypes Bytes}

def f: Option (ParentNode Bytes tkt) × MlsBytes Bytes × MlsBytes Bytes → ParentNodeTreeHashInput Bytes tkt :=
  fun (parentNode, leftHash, rightHash) => { parentNode, leftHash, rightHash }

def g: ParentNodeTreeHashInput Bytes tkt → Option (ParentNode Bytes tkt) × MlsBytes Bytes × MlsBytes Bytes :=
  fun { parentNode, leftHash, rightHash } => (parentNode, leftHash, rightHash)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end ParentNodeTreeHashInput

def ParentNodeTreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (ParentNodeTreeHashInput Bytes tkt) :=
  .isomorphic (.prod (MlsOption.mf (ParentNode.mf tkt)) (.prod MlsBytes.mf MlsBytes.mf))
    ParentNodeTreeHashInput.f ParentNodeTreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/--
struct {
  NodeType node_type;
  select (TreeHashInput.node_type) {
    case leaf:   LeafNodeHashInput leaf_node;
    case parent: ParentNodeHashInput parent_node;
  };
} TreeHashInput;
-/
inductive TreeHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  | leaf: LeafNodeTreeHashInput Bytes tkt → TreeHashInput Bytes tkt
  | parent: ParentNodeTreeHashInput Bytes tkt → TreeHashInput Bytes tkt

namespace TreeHashInput

variable {tkt: TreeKEMTypes Bytes}

def internalType (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes): NodeType → Type
  | .leaf => LeafNodeTreeHashInput Bytes tkt
  | .parent => ParentNodeTreeHashInput Bytes tkt

def internalType.mf (tkt: TreeKEMTypes Bytes): (t: NodeType) → NonExtensibleMessageFormat Bytes (internalType Bytes tkt t)
  | .leaf => LeafNodeTreeHashInput.mf tkt
  | .parent => ParentNodeTreeHashInput.mf tkt

instance: ∀ t, (internalType.mf tkt t).IsNonAmbiguous
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

instance: ∀ t, (internalType.mf tkt t).HasUniqueRepresentation
  | .leaf | .parent => by
    dsimp only [internalType.mf, internalType]
    infer_instance

def f: (t: NodeType) × internalType Bytes tkt t → TreeHashInput Bytes tkt
  | ⟨.leaf, x⟩ => .leaf x
  | ⟨.parent, x⟩ => .parent x

def g: TreeHashInput Bytes tkt → (t: NodeType) × internalType Bytes tkt t
  | .leaf x => ⟨.leaf, x⟩
  | .parent x => ⟨.parent, x⟩

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro ⟨t, _⟩; cases t <;> rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro x; cases x <;> rfl⟩

end TreeHashInput

def TreeHashInput.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (TreeHashInput Bytes tkt) :=
  .isomorphic (.sigma NodeType.mf (TreeHashInput.internalType.mf tkt)) TreeHashInput.f TreeHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

end Formats

/-! ## Tree hash -/

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Compute the tree hash of a tree. -/
def treeHash: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → Result Bytes
  | _, i, .leaf olp => do
    let i ← mkUInt32 i.val "tree_hash" "i"
    let hashInput := serializeNE (TreeHashInput.mf tkt) (.leaf { leafIndex := i, leafNode := olp })
    CryptoBytes.hashHash hashInput
  | _, _, .node onp left right => do
    let leftHash ← treeHash left
    let leftHash ← mkMlsBytes leftHash "tree_hash" "left_bytes"
    let rightHash ← treeHash right
    let rightHash ← mkMlsBytes rightHash "tree_hash" "right_bytes"
    let hashInput := serializeNE (TreeHashInput.mf tkt) (.parent { parentNode := onp, leftHash, rightHash })
    CryptoBytes.hashHash hashInput

end Mls.TreeSync
