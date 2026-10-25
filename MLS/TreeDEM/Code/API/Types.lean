import MLS.Common.Code.Tree
import MLS.TreeSync.Code.NetworkTypes
import MLS.TreeDEM.Code.Keys

/-!
Port of `MLS.TreeDEM.API.Types`.

Port-specific differences:
- `my_leaf_index` is a `Nat` (MLS*'s `leaf_index tree_height 0`).
-/

namespace MLS.TreeDEM

open Comparse
open MLS MLS.TreeSync

/-- Port of `treedem_state`. -/
structure TreeDEMState (Bytes: Type) [BytesLike Bytes] where
  treeHeight: Nat
  myLeafIndex: Nat
  groupContext: GroupContext Bytes
  /-- TODO (as in MLS*): this need to be changed for forward secrecy -/
  encryptionSecret: Bytes
  senderDataSecret: Bytes
  membershipKey: Bytes
  mySignatureKey: Bytes
  myHandshakeRatchet: RatchetState Bytes
  myApplicationRatchet: RatchetState Bytes
  verificationKeys: Tree (Option (SignaturePublicKey Bytes)) Unit treeHeight

end MLS.TreeDEM
