module

public import MLS.Common.Code.Tree
public import MLS.TreeSync.Code.NetworkTypes

/-!
Port of `MLS.TreeSync.Types`.
-/

namespace MLS.TreeSync

open Comparse

/--
Port of `treesync`.
TreeSync's tree. Blank nodes are represented with `none`.
-/
public
abbrev TreeSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Tree (Option (LeafNode Bytes tkt)) (Option (ParentNode Bytes tkt))

/--
Port of `pathsync`.
An authenticated path. The leaf contains a parent-hash and a signature.
-/
public
abbrev PathSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Path (LeafNode Bytes tkt) (Option tkt.NodeContent)

/--
Port of `external_pathsync`.
An un-authenticated path, outputted by TreeKEM.
It lacks signature in the leaf, and the leaf parent hash must be re-computed.
-/
public
abbrev ExternalPathSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Path (LeafNodeData Bytes tkt) (Option tkt.NodeContent)

/-- Port of `one_tree`. -/
public
abbrev OneTreeSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) := (l: Nat) × TreeSync Bytes tkt l

/-- Port of `tree_list`. -/
public
abbrev TreeSyncList (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) := List (OneTreeSync Bytes tkt)

end MLS.TreeSync
