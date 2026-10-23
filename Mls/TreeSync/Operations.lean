import Mls.TreeCommon
import Mls.MiscLemmas
import Mls.TreeSync.ParentHash

/-!
Port of `MLS.TreeSync.Operations`.

Port-specific differences:
- Functions recurse on the views of `Mls.Tree`: `ChildSiblingView` for functions following a leaf index,
  `LeftRightView` for functions visiting both children.
- Leaf indices are plain `Nat`s (see `Mls.Tree`).
- Paths are not indexed by the leaf index (see `Mls.Path`): functions recursing on a tree and a path
  take the leaf index as an explicit argument.
- Preconditions of MLS* (e.g. `(get_path_leaf p).source = LNS_update`) are not ported:
  functions fail or have a default behavior when they are not met (see the docstrings).
-/

namespace Mls.TreeSync

open Comparse
open Mls

/-! ## Tree operations -/

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `tree_add`.
Add a new leaf at a specific position in the tree.
MLS specifies that an add must happen in the first empty leaf,
and that the tree must be extended if there are no empty leaves.
Finding the empty leaf and extending are separate functions,
`treeAdd` only deals with modifying a leaf and adding its index to the unmerged_leaves lists.
We can't always add a leaf in the tree:
- its leaf index has to fit in 32 bits
- the unmerged_leaves array lengths have to fit in 30 bits
This is why this function can fail.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def treeAdd {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (lp: LeafNode Bytes tkt): Result (TreeSync Bytes tkt l) :=
  match t.intoChildSiblingView li with
  | .leaf _ position => pure (ChildSiblingView.leaf (some lp) position).pack
  | .node optContent child sibling => do
    let newOptContent ← match optContent with
      | none => pure none
      | some content => do
        let li' ← mkUInt32 li "tree_add" "li"
        let newUnmergedLeaves ← mkMlsList (insertSorted li' content.unmergedLeaves.val) "tree_add" "new_unmerged_leaves"
        pure (some { content with unmergedLeaves := newUnmergedLeaves })
    let newChild ← treeAdd child li lp
    pure (ChildSiblingView.node newOptContent newChild sibling).pack

/--
Port of `un_addP`.
Remove, or "un-add" the leaves whose index satisfy some predicate.
This is useful in the proofs, and also to compute the "original sibling"
in the parent-hash check when joining a group.
-/
def unAddP {l: Nat} (t: TreeSync Bytes tkt l) (pred: Nat → Bool): TreeSync Bytes tkt l :=
  match t.intoLeftRightView with
  | .leaf content position => (LeftRightView.leaf (if pred position then content else none) position).pack
  | .node optContent left right =>
    let newOptContent := optContent.map fun content => { content with
      unmergedLeaves := ⟨content.unmergedLeaves.val.filter (fun x => pred x.toNat), by
        have := bytes_length_filter (NonExtensibleMessageFormat.uint32BE (Bytes := Bytes)) (fun x => pred x.toNat) content.unmergedLeaves.val
        have := content.unmergedLeaves.property
        simp only [mlsNatPred] at *
        omega⟩
    }
    (LeftRightView.node newOptContent (unAddP left pred) (unAddP right pred)).pack

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `compute_new_np_and_ph`. -/
def computeNewNpAndPh {l: Nat}
  (optExtContent: Option tkt.NodeContent) (sibling: TreeSync Bytes tkt l) (parentParentHash: Bytes)
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
Port of `compute_leaf_parent_hash_from_path`.
Recompute the parent-hash of a leaf at the end of a path.
When `PathLeaf = LeafNodeData Bytes tkt`, the path type corresponds to `ExternalPathSync`,
and this function is used to compute the new leaf parent-hash before signature.
When `PathLeaf = LeafNode Bytes tkt`, the path type corresponds to `PathSync`,
and this function is used to check the validity of the path before applying it on the tree.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def computeLeafParentHashFromPath {PathLeaf: Type} {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: Path PathLeaf (Option tkt.NodeContent) l) (parentParentHash: Bytes): Result Bytes
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf _ => pure parentParentHash
  | .node _ child sibling, .node optExtContent pNext => do
    let (_, newParentParentHash) ← computeNewNpAndPh optExtContent sibling parentParentHash
    computeLeafParentHashFromPath child li pNext newParentParentHash

/-- Port of `get_leaf_tbs`. -/
def getLeafTbs (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: UInt32): Bytes :=
  serializeNE (LeafNodeTBS.mf tkt) {
    data := ln.data
    groupId := StaticOption.mk groupId
    leafIndex := StaticOption.mk leafIndex
  }

/--
Port of `leaf_is_valid`.
Check the signature inside a leaf.
-/
def leafIsValid (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Bool :=
  leafIndex < 2^32 && (
    let tbsBytes := getLeafTbs ln groupId leafIndex.toUInt32
    BytesLike.length tbsBytes < 2^30 &&
    verifyWithLabel ln.data.signatureKey.val "LeafNodeTBS" tbsBytes ln.signature.val
  )

/--
Port of `path_leaf_is_valid`.
Check the signature of the path's leaf.
MLS* requires `li: leaf_index l 0`; this precondition is not needed here.
-/
def pathLeafIsValid {l: Nat}
  (groupId: MlsBytes Bytes) (li: Nat) (p: PathSync Bytes tkt l): Bool
:=
  leafIsValid p.getPathLeaf groupId li

/--
Port of `path_is_parent_hash_valid`.
Check the parent-hash of the path's leaf.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def pathIsParentHashValid {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l): Bool
:=
  let newLp := p.getPathLeaf
  if h: newLp.data.source == .commit then
    match computeLeafParentHashFromPath t li p rootParentHash.val with
    | .success ph => ph == (newLp.data.parentHash.get h).val
    | _ => false
  else
    false

/--
Port of `path_is_filter_valid`.
Check that blank nodes in the path corresponds to filtered nodes.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def pathIsFilterValid {PathLeaf: Type} {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: Path PathLeaf (Option tkt.NodeContent) l): Bool
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ _, .leaf _ => true
  | .node _ child sibling, .node newOpn pNext =>
    (newOpn.isSome || isTreeEmpty sibling) && pathIsFilterValid child li pNext

/--
Port of `path_is_valid`.
Combine all the validity checks for paths, defined above.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def pathIsValid {l: Nat}
  (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l): Bool
:=
  let newLp := p.getPathLeaf
  -- TODO (as in MLS*): something stating that newLp is related to `leafAt t li`
  let signatureOk := pathLeafIsValid groupId li p
  let parentHashOk := pathIsParentHashValid t li p
  let filterOk := pathIsFilterValid t li p
  let sourceOk := newLp.data.source == .commit
  signatureOk && parentHashOk && filterOk && sourceOk

/--
Port of `external_path_to_path_aux`.
Auxiliary function, useful for proofs.
MLS* requires `(get_path_leaf p).source = LNS_update`, see `externalPathToPath`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def externalPathToPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (signKey: Bytes) (nonce: Bytes)
  : Result (LeafNode Bytes tkt)
:= do
  let computedParentHash ← computeLeafParentHashFromPath t li p rootParentHash.val
  let computedParentHash ← mkMlsBytes computedParentHash "external_path_to_path_aux" "computed_parent_hash"
  let lp := p.getPathLeaf
  let newLpData: LeafNodeData Bytes tkt := {
    lp with
    source := .commit
    lifetime := ()
    parentHash := computedParentHash
  }
  let newLpTbs ← do
    let leafIndex ← mkUInt32 li "external_path_to_path_aux" "li"
    pure (serializeNE (LeafNodeTBS.mf tkt) { data := newLpData, groupId, leafIndex })
  let newSignature ← signWithLabel signKey "LeafNodeTBS" newLpTbs nonce
  let newSignature ← mkMlsBytes newSignature "external_path_to_path_aux" "new_signature"
  pure { data := newLpData, signature := newSignature }

/--
Port of `external_path_to_path`.
Authenticate an `ExternalPathSync` by computing the leaf parent-hash, signing the leaf, and returns a `PathSync`.
MLS* requires `(get_path_leaf p).source == LNS_update`; otherwise, the leaf source is overwritten with `commit` anyway.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def externalPathToPath {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (signKey: Bytes) (nonce: Bytes)
  : Result (PathSync Bytes tkt l)
:= do
  let newLeaf ← externalPathToPathAux t li p groupId signKey nonce
  pure (p.setPathLeaf newLeaf)

/--
Port of `apply_path_aux`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes): Result (TreeSync Bytes tkt l)
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ position, .leaf lp => pure (ChildSiblingView.leaf (some lp) position).pack
  | .node _ child sibling, .node optExtContent pNext => do
    let (newOptContent, newParentParentHash) ← computeNewNpAndPh optExtContent sibling parentParentHash
    let newChild ← applyPathAux child li pNext newParentParentHash
    pure (ChildSiblingView.node newOptContent newChild sibling).pack

/--
Port of `apply_path`.
Apply a path on the tree, and compute the parent-hashes of internal nodes.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def applyPath {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  : Result (TreeSync Bytes tkt l)
:=
  applyPathAux t li p rootParentHash.val

/--
Port of `sign_leaf_node_data_key_package`.
MLS* requires `ln_data.source = LNS_key_package`; otherwise, this function fails.
-/
def signLeafNodeDataKeyPackage (lnData: LeafNodeData Bytes tkt)
  (signKey: Bytes) (nonce: Bytes) : Result (LeafNode Bytes tkt)
:= do
  if lnData.source != .keyPackage then
    Result.internalFailure "sign_leaf_node_data_key_package: source must be key_package"
  let lnTbs := serializeNE (LeafNodeTBS.mf tkt) { data := lnData, groupId := StaticOption.mk rootParentHash, leafIndex := StaticOption.mk 0 }
  let signature ← signWithLabel signKey "LeafNodeTBS" lnTbs nonce
  let signature ← mkMlsBytes signature "sign_leaf_node_data_key_package" "signature"
  pure { data := lnData, signature }

/--
Port of `sign_leaf_node_data_update`.
MLS* requires `ln_data.source = LNS_update`; otherwise, this function fails.
-/
def signLeafNodeDataUpdate (lnData: LeafNodeData Bytes tkt)
  (groupId: MlsBytes Bytes) (leafIndex: UInt32) (signKey: Bytes) (nonce: Bytes) : Result (LeafNode Bytes tkt)
:= do
  if lnData.source != .update then
    Result.internalFailure "sign_leaf_node_data_update: source must be update"
  let lnTbs := serializeNE (LeafNodeTBS.mf tkt) { data := lnData, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk leafIndex }
  let signature ← signWithLabel signKey "LeafNodeTBS" lnTbs nonce
  let signature ← mkMlsBytes signature "sign_leaf_node_data_update" "signature"
  pure { data := lnData, signature }

end CryptoBytes

end Mls.TreeSync
