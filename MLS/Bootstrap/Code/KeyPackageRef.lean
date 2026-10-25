import MLS.Common.Code.Crypto.Derived
import MLS.Bootstrap.Code.NetworkTypes

/-!
Port of `MLS.Bootstrap.KeyPackageRef`.
-/

namespace MLS.Bootstrap

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `compute_key_package_ref`. -/
def computeKeyPackageRef (kp: KeyPackage Bytes TreeKEM.tkt): Result (KeyPackageRef Bytes) := do
  let kpBytes := serializeNE (KeyPackage.mf TreeKEM.tkt) kp
  let res ← makeKeypackageRef kpBytes
  mkMlsBytes res "compute_key_package_ref" "res"

end MLS.Bootstrap
