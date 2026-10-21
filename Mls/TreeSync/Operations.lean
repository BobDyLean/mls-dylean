import Mls.TreeCommon
import Mls.MiscLemmas
import Mls.TreeSync.ParentHash

/-!
Port of `MLS.TreeSync.Operations`.

Port-specific differences:
- Functions recursing on a tree and a path at once match on `Path.nodeLeft` / `Path.nodeRight`
  instead of calling `get_child_sibling` (see `Mls.Path`).
- Refinements on the arguments (e.g. `(get_path_leaf p).source = LNS_update`) are explicit hypotheses.
-/

namespace Mls.TreeSync

open Comparse
open Mls Mls.Tree

/-! ## Tree operations -/

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/--
Add a new leaf at a specific position in the tree.
MLS specifies that an add must happen in the first empty leaf,
and that the tree must be extended if there are no empty leaves.
Finding the empty leaf and extending are separate functions,
`treeAdd` only deals with modifying a leaf and adding its index to the unmerged_leaves lists.
We can't always add a leaf in the tree:
- its leaf index has to fit in 32 bits
- the unmerged_leaves array lengths have to fit in 30 bits
This is why this function can fail.
-/
def treeAdd: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → LeafIndex l i → LeafNode Bytes tkt →
  Result (TreeSync Bytes tkt l i)
  | _, _, .leaf _, _, lp => pure (.leaf (some lp))
  | _, _, .node optContent left right, li, lp => do
    let newOptContent ← match optContent with
      | none => pure none
      | some content => do
        let li' ← mkUInt32 li.val "tree_add" "li"
        let newUnmergedLeaves ← mkMlsList (insertSorted li' content.unmergedLeaves.val) "tree_add" "new_unmerged_leaves"
        pure (some { content with unmergedLeaves := newUnmergedLeaves })
    if h: isLeftLeaf li then do
      let newLeft ← treeAdd left (li.childOfLeft h) lp
      pure (.node newOptContent newLeft right)
    else do
      let newRight ← treeAdd right (li.childOfRight (by simpa using h)) lp
      pure (.node newOptContent left newRight)

/--
Remove, or "un-add" the leaves whose index satisfy some predicate.
This is useful in the proofs, and also to compute the "original sibling"
in the parent-hash check when joining a group.
-/
def unAddP: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → (Nat → Bool) → TreeSync Bytes tkt l i
  | _, i, t@(.leaf _), pred => if pred i.val then t else .leaf none
  | _, _, .node none left right, pred => .node none (unAddP left pred) (unAddP right pred)
  | _, _, .node (some content) left right, pred =>
    let newContent := { content with
      unmergedLeaves := ⟨content.unmergedLeaves.val.filter (fun x => pred x.toNat), by
        have := bytes_length_filter (NonExtensibleMessageFormat.uint32BE (Bytes := Bytes)) (fun x => pred x.toNat) content.unmergedLeaves.val
        have := content.unmergedLeaves.property
        simp only [mlsNatPred] at *
        omega⟩
    }
    .node (some newContent) (unAddP left pred) (unAddP right pred)

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

def computeNewNpAndPh {l: Nat} {i: TreeIndex l}
  (optExtContent: Option tkt.NodeContent) (sibling: TreeSync Bytes tkt l i) (parentParentHash: Bytes)
  : Result (Option (ParentNode Bytes tkt) × Bytes)
:= do
  let newOptContent ← do
    let parentParentHash ← mkMlsBytes parentParentHash "compute_new_np_and_ph" "parent_parent_hash"
    pure (
      match optExtContent with
      | some extContent => some { content := extContent, parentHash := parentParentHash, unmergedLeaves := ⟨[], by simp [ExtensibleMessageFormat.list, ExtensibleMessageFormat.list.serialize, BytesLike.empty_length, mlsNatPred]⟩ }
      | none => none
    )
  let newParentParentHash ←
    match optExtContent with
    | some extContent => computeParentHash extContent parentParentHash sibling
    | none => pure parentParentHash
  pure (newOptContent, newParentParentHash)

/--
Recompute the parent-hash of a leaf at the end of a path.
When `PathLeaf = LeafNodeData Bytes tkt`, the path type corresponds to `ExternalPathSync`,
and this function is used to compute the new leaf parent-hash before signature.
When `PathLeaf = LeafNode Bytes tkt`, the path type corresponds to `PathSync`,
and this function is used to check the validity of the path before applying it on the tree.
-/
def computeLeafParentHashFromPath {PathLeaf: Type}:
  {l: Nat} → {i: TreeIndex l} → {li: LeafIndex l i} →
  TreeSync Bytes tkt l i → Path PathLeaf (Option tkt.NodeContent) l i li → (parentParentHash: Bytes) → Result Bytes
  | _, _, _, .leaf _, .leaf _, parentParentHash => pure parentParentHash
  | _, _, _, .node _ left right, .nodeLeft _ optExtContent pNext, parentParentHash => do
    let (_, newParentParentHash) ← computeNewNpAndPh optExtContent right parentParentHash
    computeLeafParentHashFromPath left pNext newParentParentHash
  | _, _, _, .node _ left right, .nodeRight _ optExtContent pNext, parentParentHash => do
    let (_, newParentParentHash) ← computeNewNpAndPh optExtContent left parentParentHash
    computeLeafParentHashFromPath right pNext newParentParentHash

def getLeafTbs (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: UInt32): Bytes :=
  serializeNE (LeafNodeTBS.mf tkt) {
    data := ln.data
    groupId := StaticOption.mk groupId
    leafIndex := StaticOption.mk leafIndex
  }

/-- Check the signature inside a leaf. -/
def leafIsValid (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Bool :=
  leafIndex < 2^32 && (
    let tbsBytes := getLeafTbs ln groupId leafIndex.toUInt32
    BytesLike.length tbsBytes < 2^30 &&
    verifyWithLabel ln.data.signatureKey.val "LeafNodeTBS" tbsBytes ln.signature.val
  )

/-- Check the signature of the path's leaf. -/
def pathLeafIsValid {l: Nat} {li: LeafIndex l (TreeIndex.zero l)}
  (groupId: MlsBytes Bytes) (p: PathSync Bytes tkt l (TreeIndex.zero l) li): Bool
:=
  leafIsValid p.getPathLeaf groupId li.val

/-- Check the parent-hash of the path's leaf. -/
def pathIsParentHashValid {l: Nat} {li: LeafIndex l (TreeIndex.zero l)}
  (t: TreeSync Bytes tkt l (TreeIndex.zero l)) (p: PathSync Bytes tkt l (TreeIndex.zero l) li): Bool
:=
  let newLp := p.getPathLeaf
  if h: newLp.data.source == .commit then
    match computeLeafParentHashFromPath t p rootParentHash.val with
    | .success ph => ph == (newLp.data.parentHash.get h).val
    | _ => false
  else
    false

/-- Check that blank nodes in the path corresponds to filtered nodes. -/
def pathIsFilterValid {PathLeaf: Type}:
  {l: Nat} → {i: TreeIndex l} → {li: LeafIndex l i} →
  TreeSync Bytes tkt l i → Path PathLeaf (Option tkt.NodeContent) l i li → Bool
  | _, _, _, .leaf _, .leaf _ => true
  | _, _, _, .node _ left right, .nodeLeft _ newOpn pNext =>
    (newOpn.isSome || isTreeEmpty right) && pathIsFilterValid left pNext
  | _, _, _, .node _ left right, .nodeRight _ newOpn pNext =>
    (newOpn.isSome || isTreeEmpty left) && pathIsFilterValid right pNext

/-- Combine all the validity checks for paths, defined above. -/
def pathIsValid {l: Nat} {li: LeafIndex l (TreeIndex.zero l)}
  (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt l (TreeIndex.zero l)) (p: PathSync Bytes tkt l (TreeIndex.zero l) li): Bool
:=
  let newLp := p.getPathLeaf
  -- TODO (as in MLS*): something stating that newLp is related to `leafAt t li`
  let signatureOk := pathLeafIsValid groupId p
  let parentHashOk := pathIsParentHashValid t p
  let filterOk := pathIsFilterValid t p
  let sourceOk := newLp.data.source == .commit
  signatureOk && parentHashOk && filterOk && sourceOk

/-- Auxiliary function, useful for proofs. -/
def externalPathToPathAux {l: Nat} {i: TreeIndex l} {li: LeafIndex l i}
  (t: TreeSync Bytes tkt l i) (p: ExternalPathSync Bytes tkt l i li)
  (groupId: MlsBytes Bytes) (signKey: Bytes) (nonce: Bytes)
  : Result (LeafNode Bytes tkt)
:= do
  let computedParentHash ← computeLeafParentHashFromPath t p rootParentHash.val
  let computedParentHash ← mkMlsBytes computedParentHash "external_path_to_path_aux" "computed_parent_hash"
  let lp := p.getPathLeaf
  let newLpData: LeafNodeData Bytes tkt := {
    lp with
    source := .commit
    lifetime := ()
    parentHash := computedParentHash
  }
  let newLpTbs ← do
    let leafIndex ← mkUInt32 li.val "external_path_to_path_aux" "li"
    pure (serializeNE (LeafNodeTBS.mf tkt) { data := newLpData, groupId, leafIndex })
  let newSignature ← signWithLabel signKey "LeafNodeTBS" newLpTbs nonce
  let newSignature ← mkMlsBytes newSignature "external_path_to_path_aux" "new_signature"
  pure { data := newLpData, signature := newSignature }

/--
Authenticate an `ExternalPathSync` by computing the leaf parent-hash, signing the leaf, and returns a `PathSync`.
MLS* requires `(get_path_leaf p).source == LNS_update`.
-/
def externalPathToPath {l: Nat} {i: TreeIndex l} {li: LeafIndex l i}
  (t: TreeSync Bytes tkt l i) (p: ExternalPathSync Bytes tkt l i li) (_: p.getPathLeaf.source = .update)
  (groupId: MlsBytes Bytes) (signKey: Bytes) (nonce: Bytes)
  : Result (PathSync Bytes tkt l i li)
:= do
  let newLeaf ← externalPathToPathAux t p groupId signKey nonce
  pure (p.setPathLeaf newLeaf)

def applyPathAux:
  {l: Nat} → {i: TreeIndex l} → {li: LeafIndex l i} →
  TreeSync Bytes tkt l i → PathSync Bytes tkt l i li → (parentParentHash: Bytes) → Result (TreeSync Bytes tkt l i)
  | _, _, _, .leaf _, .leaf lp, _ => pure (.leaf (some lp))
  | _, _, _, .node _ left right, .nodeLeft _ optExtContent pNext, parentParentHash => do
    let (newOptContent, newParentParentHash) ← computeNewNpAndPh optExtContent right parentParentHash
    let newLeft ← applyPathAux left pNext newParentParentHash
    pure (.node newOptContent newLeft right)
  | _, _, _, .node _ left right, .nodeRight _ optExtContent pNext, parentParentHash => do
    let (newOptContent, newParentParentHash) ← computeNewNpAndPh optExtContent left parentParentHash
    let newRight ← applyPathAux right pNext newParentParentHash
    pure (.node newOptContent left newRight)

/-- Apply a path on the tree, and compute the parent-hashes of internal nodes. -/
def applyPath {l: Nat} {li: LeafIndex l (TreeIndex.zero l)}
  (t: TreeSync Bytes tkt l (TreeIndex.zero l)) (p: PathSync Bytes tkt l (TreeIndex.zero l) li)
  : Result (TreeSync Bytes tkt l (TreeIndex.zero l))
:=
  applyPathAux t p rootParentHash.val

/-- MLS* requires `ln_data.source = LNS_key_package`. -/
def signLeafNodeDataKeyPackage (lnData: LeafNodeData Bytes tkt) (_: lnData.source = .keyPackage)
  (signKey: Bytes) (nonce: Bytes) : Result (LeafNode Bytes tkt)
:= do
  let lnTbs := serializeNE (LeafNodeTBS.mf tkt) { data := lnData, groupId := StaticOption.mk rootParentHash, leafIndex := StaticOption.mk 0 }
  let signature ← signWithLabel signKey "LeafNodeTBS" lnTbs nonce
  let signature ← mkMlsBytes signature "sign_leaf_node_data_key_package" "signature"
  pure { data := lnData, signature }

/-- MLS* requires `ln_data.source = LNS_update`. -/
def signLeafNodeDataUpdate (lnData: LeafNodeData Bytes tkt) (_: lnData.source = .update)
  (groupId: MlsBytes Bytes) (leafIndex: UInt32) (signKey: Bytes) (nonce: Bytes) : Result (LeafNode Bytes tkt)
:= do
  let lnTbs := serializeNE (LeafNodeTBS.mf tkt) { data := lnData, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk leafIndex }
  let signature ← signWithLabel signKey "LeafNodeTBS" lnTbs nonce
  let signature ← mkMlsBytes signature "sign_leaf_node_data_update" "signature"
  pure { data := lnData, signature }

end CryptoBytes

end Mls.TreeSync
