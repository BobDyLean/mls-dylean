import MLS.TreeSync.Code.ParentHash
import MLS.TreeSync.Proofs.TreeHash

/-!
Port of `MLS.TreeSync.ParentHash.Proofs`.

Port-specific differences:
- As `tree_hash_inj` (see `MLS.TreeSync.Proofs.TreeHash`), MLS*'s `compute_parent_hash_inj`
  is split into the function `computeParentHashInj` and its correctness theorem `computeParentHashInj_spec`.
- `computeParentHashInj` does not use decidable equality on the inputs:
  it compares the serialized parent hash inputs, and otherwise returns the result of `treeHashInj`
  on the original siblings (instead of first checking whether all the inputs are equal).
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `get_parent_hash_input`.
MLS* requires `parent_hash: mls_bytes bytes`; otherwise, this function fails.
-/
def getParentHashInput {l: Nat}
  (content: tkt.NodeContent) (parentHash: Bytes) (originalSibling: TreeSync Bytes tkt l)
  : Result (ParentHashInput Bytes tkt)
:= do
  let parentHash ← mkMlsBytes parentHash "compute_parent_hash" "parent_hash"
  let originalSiblingTreeHash ← treeHash originalSibling
  let originalSiblingTreeHash ← mkMlsBytes originalSiblingTreeHash "compute_parent_hash" "original_sibling_tree_hash"
  pure { content, parentHash, originalSiblingTreeHash }

theorem getParentHashInput_eq_success {l: Nat}
  (content: tkt.NodeContent) (parentHash: Bytes) (originalSibling: TreeSync Bytes tkt l)
  (hashInput: ParentHashInput Bytes tkt):
  getParentHashInput content parentHash originalSibling = .success hashInput ↔
    hashInput.content = content ∧ hashInput.parentHash.val = parentHash ∧
    treeHash originalSibling = .success hashInput.originalSiblingTreeHash.val
:= by
  obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := hashInput
  simp [getParentHashInput]
  grind

theorem computeParentHash_eq_success {l: Nat}
  (content: tkt.NodeContent) (parentHash: Bytes) (originalSibling: TreeSync Bytes tkt l) (ph: Bytes):
  computeParentHash content parentHash originalSibling = .success ph ↔
    ∃ hashInput, getParentHashInput content parentHash originalSibling = .success hashInput ∧
      CryptoBytes.hashHash (serializeNE (ParentHashInput.mf tkt) hashInput) = .success ph
:= by
  grind [computeParentHash, getParentHashInput, Result.bind_eq_success, Result.pure_eq_success]

/--
Port of `compute_parent_hash_inj`.
Injectivity theorem for the parent-hash computation, very similar to `tree_hash_inj`.

This function computes the pair of bytes, its specification is `computeParentHashInj_spec`.
-/
def computeParentHashInj {l1 l2: Nat}
  (content1: tkt.NodeContent) (parentHash1: Bytes) (originalSibling1: TreeSync Bytes tkt l1)
  (content2: tkt.NodeContent) (parentHash2: Bytes) (originalSibling2: TreeSync Bytes tkt l2)
  : Bytes × Bytes
:=
  match getParentHashInput content1 parentHash1 originalSibling1, getParentHashInput content2 parentHash2 originalSibling2 with
  | .success hashInput1, .success hashInput2 =>
    let serializedHashInput1 := serializeNE (ParentHashInput.mf tkt) hashInput1
    let serializedHashInput2 := serializeNE (ParentHashInput.mf tkt) hashInput2
    if serializedHashInput1 ≠ serializedHashInput2 then
      (serializedHashInput1, serializedHashInput2)
    else
      treeHashInj originalSibling1 originalSibling2
  | _, _ => (BytesLike.empty, BytesLike.empty)

/--
Specification of `computeParentHashInj` (MLS*'s postcondition of `compute_parent_hash_inj`):
if the parent-hashes are equal, then either all their inputs are equal,
or the two bytes computed by `computeParentHashInj` are a hash collision.
-/
theorem computeParentHashInj_spec {l1 l2: Nat}
  (content1: tkt.NodeContent) (parentHash1: Bytes) (originalSibling1: TreeSync Bytes tkt l1)
  (content2: tkt.NodeContent) (parentHash2: Bytes) (originalSibling2: TreeSync Bytes tkt l2)
  (ph: Bytes)
  (h1: computeParentHash content1 parentHash1 originalSibling1 = .success ph)
  (h2: computeParentHash content2 parentHash2 originalSibling2 = .success ph):
  (content1 = content2 ∧ parentHash1 = parentHash2 ∧
    (⟨l1, originalSibling1⟩: (l: Nat) × TreeSync Bytes tkt l) = ⟨l2, originalSibling2⟩) ∨
    isHashCollision (computeParentHashInj content1 parentHash1 originalSibling1 content2 parentHash2 originalSibling2)
:= by
  grind [computeParentHash_eq_success, getParentHashInput_eq_success, computeParentHashInj, isHashCollision,
    treeHashInj_spec]

end MLS.TreeSync
