module

public import MLS.Common.Code.Extensions

/-!
Port of `MLS.TreeSync.Extensions`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes]

/-! ## Extensions parser -/

/-- Port of `application_id_ext_nt`. -/
public
structure ApplicationIdExt (Bytes: Type) [BytesLike Bytes] where
  applicationId: MlsBytes Bytes

@[expose]
public
def ApplicationIdExt.f: MlsBytes Bytes → ApplicationIdExt Bytes :=
  ApplicationIdExt.mk

@[expose]
public
def ApplicationIdExt.g: ApplicationIdExt Bytes → MlsBytes Bytes :=
  ApplicationIdExt.applicationId

public
instance: LeftInverse (ApplicationIdExt.g (Bytes := Bytes)) ApplicationIdExt.f := ⟨by intro _; rfl⟩
public
instance: RightInverse (ApplicationIdExt.g (Bytes := Bytes)) ApplicationIdExt.f := ⟨by intro _; rfl⟩

@[expose]
public
def ApplicationIdExt.mf: NonExtensibleMessageFormat Bytes (ApplicationIdExt Bytes) :=
  .isomorphic MlsBytes.mf ApplicationIdExt.f ApplicationIdExt.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

@[simp]
public
theorem ApplicationIdExt.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: ApplicationIdExt Bytes):
  (ApplicationIdExt.mf (Bytes := Bytes)).wf pred x = pred x.applicationId.val
:= by
  simp [ApplicationIdExt.mf, ApplicationIdExt.g]

/-- Port of `get_application_id_extension`. -/
@[expose]
public
def getApplicationIdExtension (extensions: List (Extension Bytes)): Option (ApplicationIdExt Bytes) :=
  mkGetExtension .applicationId ApplicationIdExt.mf extensions

/-- Port of `set_application_id_extension`. -/
@[expose]
public
def setApplicationIdExtension (extensions: List (Extension Bytes)) (ext: ApplicationIdExt Bytes):
  Result (MlsList (Extension.mf (Bytes := Bytes)))
:=
  mkSetExtension .applicationId ApplicationIdExt.mf extensions ext

end MLS.TreeSync
