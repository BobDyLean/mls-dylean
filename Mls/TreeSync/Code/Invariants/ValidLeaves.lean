import Mls.TreeSync.Code.Operations

/-!
Port of `MLS.TreeSync.Invariants.ValidLeaves`.
-/

namespace Mls.TreeSync

open Comparse
open Mls

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `valid_leaves_invariant`.
The "valid leaves" invariant:
every non-blank leaf has a valid signature.
-/
def validLeavesInvariant (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l): Bool :=
  match t.intoLeftRightView with
  | .leaf none _ => true
  | .leaf (some ln) position => leafIsValid ln groupId position
  | .node _ left right => validLeavesInvariant groupId left && validLeavesInvariant groupId right

end Mls.TreeSync
