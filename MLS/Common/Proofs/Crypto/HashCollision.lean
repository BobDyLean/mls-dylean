module

public import MLS.Common.Code.Crypto.Builtins

/-!
Hash collisions, the target of the reductions of the security proofs
(e.g. `MLS.TreeSync.treeHashInj_spec`).

Port-specific differences:
- `is_hash_collision` is in MLS*'s `MLS.Crypto.Derived` (code); it is only used by proofs, hence lives here.
- `isHashCollision` takes the pair of bytes returned by the reductions (MLS* takes the two bytes separately).
-/

namespace MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `is_hash_collision`. -/
@[expose]
public
def isHashCollision: Bytes × Bytes → Bool
  | (b1, b2) => b1 != b2 && match CryptoBytes.hashHash b1, CryptoBytes.hashHash b2 with
    | .success h1, .success h2 => h1 == h2
    | _, _ => false

end MLS
