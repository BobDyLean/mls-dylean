module

public import MLS.Bootstrap.Code.KeyPackageRef
public import MLS.Common.SymbolicProofs.Crypto.Derived.RefHash

/-!
Port of `MLS.Bootstrap.Symbolic.KeyPackageRef`.
-/

namespace MLS.Bootstrap

open Comparse
open DY
open MLS

variable [HasSymbolicInvariants]

/-- Port of `compute_key_package_ref_is_knowable_by`. -/
public
theorem computeKeyPackageRef_knowableBy (tr: ProofTrace) (l: Label) (keyPackage: KeyPackage Bytes TreeKEM.tkt)
  (res: KeyPackageRef Bytes)
  (h: computeKeyPackageRef keyPackage = .success res)
  (hkp: (KeyPackage.mf TreeKEM.tkt).wf (Bytes.KnowableBy l · tr) keyPackage):
  res.val.KnowableBy l tr
:= by
  simp only [computeKeyPackageRef, Result.bind_eq_success, mkMlsBytes_eq_success] at h
  obtain ⟨kpRef, hkpRef, rfl⟩ := h
  exact makeKeypackageRef_knowableBy tr l _ _ hkpRef
    ((pred_serializeNE_iff (KeyPackage.mf TreeKEM.tkt) (Bytes.KnowableBy l · tr) keyPackage).2 hkp)

end MLS.Bootstrap
