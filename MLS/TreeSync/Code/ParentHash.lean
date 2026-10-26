module

public import MLS.TreeSync.Code.TreeHash

/-!
Port of `MLS.TreeSync.ParentHash`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

/--
struct {
    HPKEPublicKey encryption_key;
    opaque parent_hash<V>;
    opaque original_sibling_tree_hash<V>;
} ParentHashInput;
-/
public
structure ParentHashInput (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) where
  /-- encryption key -/
  content: tkt.NodeContent
  parentHash: MlsBytes Bytes
  originalSiblingTreeHash: MlsBytes Bytes

namespace ParentHashInput

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

@[expose]
public
def f: tkt.NodeContent × MlsBytes Bytes × MlsBytes Bytes → ParentHashInput Bytes tkt :=
  fun (content, parentHash, originalSiblingTreeHash) => { content, parentHash, originalSiblingTreeHash }

@[expose]
public
def g: ParentHashInput Bytes tkt → tkt.NodeContent × MlsBytes Bytes × MlsBytes Bytes :=
  fun { content, parentHash, originalSiblingTreeHash } => (content, parentHash, originalSiblingTreeHash)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end ParentHashInput

@[expose]
public
def ParentHashInput.mf {Bytes: Type} [BytesLike Bytes] (tkt: TreeKEMTypes Bytes):
  NonExtensibleMessageFormat Bytes (ParentHashInput Bytes tkt)
:=
  .isomorphic (.prod tkt.mfNodeContent (.prod MlsBytes.mf MlsBytes.mf)) ParentHashInput.f ParentHashInput.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ParentHashInput.mf.wf_eq {Bytes: Type} [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ParentHashInput Bytes tkt):
  (ParentHashInput.mf tkt).wf pred x = (
    tkt.mfNodeContent.wf pred x.content ∧ pred x.parentHash.val ∧ pred x.originalSiblingTreeHash.val
  )
:= by
  simp [ParentHashInput.mf, ParentHashInput.g]

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `compute_parent_hash`.
Compute the parent hash to store in the child of a node, given:
- the node content (with TreeKEM, the HPKE public key),
- the parent hash stored in the node,
- the original sibling.
-/
@[expose]
public
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
@[expose]
public
def rootParentHash {Bytes: Type} [BytesLike Bytes]: MlsBytes Bytes :=
  ⟨BytesLike.empty, by simp [mlsNatPred, BytesLike.empty_length]⟩

end MLS.TreeSync
