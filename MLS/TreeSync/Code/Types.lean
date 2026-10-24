import MLS.Common.Code.Tree
import MLS.TreeSync.Code.NetworkTypes

/-!
Port of `MLS.TreeSync.Types`.
-/

namespace MLS.TreeSync

open Comparse

/--
Port of `treesync`.
TreeSync's tree. Blank nodes are represented with `none`.
-/
abbrev TreeSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Tree (Option (LeafNode Bytes tkt)) (Option (ParentNode Bytes tkt))

/--
Port of `pathsync`.
An authenticated path. The leaf contains a parent-hash and a signature.
-/
abbrev PathSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Path (LeafNode Bytes tkt) (Option tkt.NodeContent)

/--
Port of `external_pathsync`.
An un-authenticated path, outputted by TreeKEM.
It lacks signature in the leaf, and the leaf parent hash must be re-computed.
-/
abbrev ExternalPathSync (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) :=
  Path (LeafNodeData Bytes tkt) (Option tkt.NodeContent)

end MLS.TreeSync
