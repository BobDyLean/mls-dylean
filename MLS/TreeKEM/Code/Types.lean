import MLS.Common.Code.Tree
import MLS.Common.Code.Crypto.Builtins
import MLS.TreeKEM.Code.NetworkTypes

/-!
Port of `MLS.TreeKEM.Types`.

Port-specific differences:
- HPKE keys are plain `Bytes` (see `MLS.Crypto.Builtins`), except in the network types
  (e.g. `HpkePublicKey Bytes` in `PrePathKEM`).
- Paths are not indexed by the position of the tree and the leaf index (see `MLS.Path`).
-/

namespace MLS.TreeKEM

open Comparse
open MLS

/-- Port of `treekem_leaf`. -/
structure TreeKEMLeaf (Bytes: Type) where
  publicKey: Bytes

/-- Port of `treekem_node`. -/
structure TreeKEMNode (Bytes: Type) where
  publicKey: Bytes
  unmergedLeaves: List Nat

/-- Port of `treekem`. -/
abbrev TreeKEM (Bytes: Type) :=
  Tree (Option (TreeKEMLeaf Bytes)) (Option (TreeKEMNode Bytes))

/-- Port of `treekem_priv`. -/
abbrev TreeKEMPriv (Bytes: Type) :=
  Path Bytes (Option Bytes)

/-- Port of `pre_pathkem`. -/
abbrev PrePathKEM (Bytes: Type) [BytesLike Bytes] :=
  Path (TreeKEMLeaf Bytes) (Option (HpkePublicKey Bytes))

/-- Port of `pathkem`. -/
abbrev PathKEM (Bytes: Type) [BytesLike Bytes] :=
  Path (TreeKEMLeaf Bytes) (Option (UpdatePathNode Bytes))

/-- Port of `path_secrets`. -/
abbrev PathSecrets (Bytes: Type) :=
  Path Bytes (Option Bytes)

end MLS.TreeKEM
