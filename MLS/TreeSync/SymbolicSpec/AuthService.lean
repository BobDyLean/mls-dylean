module

public import MLS.Comparse.Derived

/-!
Port of `MLS.TreeSync.Symbolic.AuthService`.

Port-specific differences:
- `dy_asp` (the instantiation of the Authentication Service for DY*) and its lemmas
  are not ported yet, as the other invariants of the symbolic specification
  (they will be in `MLS.TreeSync.SymbolicProofs.AuthService`).
-/

namespace MLS.TreeSync

open Comparse

/-- Port of `dy_as_token`. -/
public
structure DyAsToken where
  time: Nat

namespace DyAsToken

public
def f: Nat → DyAsToken :=
  fun time => { time }

public
def g: DyAsToken → Nat :=
  fun x => x.time

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end DyAsToken

variable {Bytes: Type} [BytesLike Bytes]

/-- Port of `ps_dy_as_token`. -/
public
def DyAsToken.mf: NonExtensibleMessageFormat Bytes DyAsToken :=
  .isomorphic .slowNat DyAsToken.f DyAsToken.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_dy_as_token_is_well_formed`. -/
@[simp]
public
theorem DyAsToken.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: DyAsToken):
  (DyAsToken.mf (Bytes := Bytes)).wf pred x = True
:= by
  simp [DyAsToken.mf]

end MLS.TreeSync
