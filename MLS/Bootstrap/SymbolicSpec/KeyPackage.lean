module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Bootstrap.Code.NetworkTypes
public import DY.Actions.ProtocolEvent

/-!
Port of `MLS.Bootstrap.Symbolic.KeyPackage`: the event logged when a key package is verified.

Port-specific differences:
- DyLean's events do not record the principal who triggered them (unlike DY*'s `trigger_event prin`):
  the principal is the field `prin` of the event.
- The event has no tag nor format (MLS*'s `event` instance).
- The labels are in `MLS.Bootstrap.SymbolicProofs.KeyPackage`; the predicates (`key_package_sign_pred`,
  `key_package_has_been_verified_pred`, …) and the lemmas are not ported yet.
-/

namespace MLS.Bootstrap

open Comparse
open DY
open MLS

/-- Port of `key_package_label`. -/
public
def keyPackageLabel: String := "KeyPackageTBS"

variable [HasSymbolicBytes]

/-- Port of `key_package_has_been_verified`. -/
public
structure KeyPackageHasBeenVerified where
  prin: Participant
  keyPackage: KeyPackage Bytes TreeKEM.tkt

variable [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]

/-- Port of `i_have_verified_key_package`. -/
public
def IHaveVerifiedKeyPackage (tr: ExecTrace) (me: Participant) (keyPackage: KeyPackage Bytes TreeKEM.tkt): Prop :=
  tr.EventLogged ({ prin := me, keyPackage }: KeyPackageHasBeenVerified)

/-- Port of `i_have_verified_every_key_package`. -/
public
def IHaveVerifiedEveryKeyPackage (tr: ExecTrace) (me: Participant) (joiners: List (KeyPackage Bytes TreeKEM.tkt)): Prop :=
  ∀ keyPackage ∈ joiners, IHaveVerifiedKeyPackage tr me keyPackage

end MLS.Bootstrap
