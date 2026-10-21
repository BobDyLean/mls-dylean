import Mls.TreeSync.Operations

/-!
Port of `MLS.TreeSync.Invariants.ValidLeaves`.
-/

namespace Mls.TreeSync

open Comparse
open Mls

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
The "valid leaves" invariant:
every non-blank leaf has a valid signature.
-/
def validLeavesInvariant (groupId: MlsBytes Bytes): {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → Bool
  | _, _, .leaf none => true
  | _, i, .leaf (some ln) => leafIsValid ln groupId i.val
  | _, _, .node _ left right => validLeavesInvariant groupId left && validLeavesInvariant groupId right

end Mls.TreeSync
