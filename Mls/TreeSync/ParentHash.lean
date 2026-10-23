import Mls.TreeSync.TreeHash

/-!
Port of `MLS.TreeSync.ParentHash`.
-/

namespace Mls.TreeSync

open Comparse
open Mls

/--
struct {
    HPKEPublicKey encryption_key;
    opaque parent_hash<V>;
    opaque original_sibling_tree_hash<V>;
} ParentHashInput;
-/
structure ParentHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  /-- encryption key -/
  content: tkt.NodeContent
  parentHash: MlsBytes Bytes
  originalSiblingTreeHash: MlsBytes Bytes

namespace ParentHashInput

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

def f: tkt.NodeContent × MlsBytes Bytes × MlsBytes Bytes → ParentHashInput Bytes tkt :=
  fun (content, parentHash, originalSiblingTreeHash) => { content, parentHash, originalSiblingTreeHash }

def g: ParentHashInput Bytes tkt → tkt.NodeContent × MlsBytes Bytes × MlsBytes Bytes :=
  fun { content, parentHash, originalSiblingTreeHash } => (content, parentHash, originalSiblingTreeHash)

instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end ParentHashInput

def ParentHashInput.mf {Bytes: Type} [BytesLike Bytes] (tkt: TreeKEMTypes Bytes):
  NonExtensibleMessageFormat Bytes (ParentHashInput Bytes tkt)
:=
  .isomorphic (.prod tkt.mfNodeContent (.prod MlsBytes.mf MlsBytes.mf)) ParentHashInput.f ParentHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `compute_parent_hash`.
Compute the parent hash to store in the child of a node, given:
- the node content (with TreeKEM, the HPKE public key),
- the parent hash stored in the node,
- the original sibling.
-/
def computeParentHash {l: Nat}
  (content: tkt.NodeContent) (parentHash: Bytes) (originalSibling: TreeSync Bytes tkt l)
  : Result Bytes
:= do
  let parentHash ← mkMlsBytes parentHash "compute_parent_hash" "parent_hash"
  let originalSiblingTreeHash ← treeHash originalSibling
  let originalSiblingTreeHash ← mkMlsBytes originalSiblingTreeHash "compute_parent_hash" "original_sibling_tree_hash"
  let hashInput := serializeNE (ParentHashInput.mf tkt) { content, parentHash, originalSiblingTreeHash }
  CryptoBytes.hashHash hashInput

/-- Port of `root_parent_hash`. -/
def rootParentHash {Bytes: Type} [BytesLike Bytes]: MlsBytes Bytes :=
  ⟨BytesLike.empty, by simp [mlsNatPred, BytesLike.empty_length]⟩

end Mls.TreeSync
