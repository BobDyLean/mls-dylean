import MLS.Common.Code.Crypto.Derived

/-!
Port of `MLS.TreeDEM.Keys` (the parts needed by the ported tests).
-/

namespace MLS.TreeDEM

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

structure TreeContext where
  generation: UInt32

instance: LeftInverse TreeContext.generation TreeContext.mk := ⟨by intro _; rfl⟩
instance: RightInverse TreeContext.generation TreeContext.mk := ⟨by intro _; rfl⟩

def TreeContext.mf {Bytes: Type} [BytesLike Bytes]: NonExtensibleMessageFormat Bytes TreeContext :=
  .isomorphic .uint32BE TreeContext.mk TreeContext.generation
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `derive_tree_secret`. -/
def deriveTreeSecret (secret: Bytes) (label: String) (generation: Nat) (len: Nat): Result Bytes := do
  let generation ← mkUInt32 generation "derive_tree_secret" "generation"
  let treeContext := serializeNE TreeContext.mf { generation }
  expandWithLabel secret label treeContext len

end MLS.TreeDEM
