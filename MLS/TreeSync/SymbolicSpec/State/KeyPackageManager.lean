module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Bootstrap.Code.NetworkTypes
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeSync.Symbolic.State.KeyPackageManager`:
a map from key packages to the handle of the corresponding private state.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated.
- States are identified by handles (`Nat`) instead of session identifiers (`state_id`).
- The invariants (`key_package_manager_pred`, …) are in `MLS.TreeSync.SymbolicProofs.State.KeyPackageManager`.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS MLS.Bootstrap
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-! ## KeyPackage manager types -/

/-- Port of `key_package_manager_value`. -/
public
structure KeyPackageManagerValue where
  siPrivate: Nat

namespace KeyPackageManagerValue

public
def f: Nat → KeyPackageManagerValue :=
  fun siPrivate => { siPrivate }

public
def g: KeyPackageManagerValue → Nat :=
  fun x => x.siPrivate

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end KeyPackageManagerValue

/-- Port of `ps_key_package_manager_value`. -/
public
def KeyPackageManagerValue.mf: NonExtensibleMessageFormat Bytes KeyPackageManagerValue :=
  .isomorphic .unboundedNat KeyPackageManagerValue.f KeyPackageManagerValue.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_key_package_manager_value_is_well_formed`. -/
@[simp]
public
theorem KeyPackageManagerValue.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: KeyPackageManagerValue):
  KeyPackageManagerValue.mf.wf pred x = True
:= by
  simp [KeyPackageManagerValue.mf, KeyPackageManagerValue.g]

/-- Port of `key_package_manager_types`. -/
public
instance keyPackageManagerTypes (tkt: TreeKEMTypes Bytes): MapTypes (KeyPackage Bytes tkt) KeyPackageManagerValue where
  mfKey := KeyPackage.mf tkt
  mfValue := KeyPackageManagerValue.mf

/-! ## KeyPackage manager API -/

variable [ExecTraceTypes]

section

variable (tkt: TreeKEMTypes Bytes)
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]

/-- Port of `initialize_key_package_manager`. -/
public
def initializeKeyPackageManager (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap (KeyPackage Bytes tkt) KeyPackageManagerValue prin

/-- Port of `add_new_key_package_secret_session`. -/
public
def addNewKeyPackageSecretSession (prin: Participant) (sid: Nat)
  (key: KeyPackage Bytes tkt) (value: KeyPackageManagerValue): Traceful Nat
:=
  DySlop.Map.addKeyValue prin sid key value

/-- Port of `find_key_package_secret_session`. -/
public
def findKeyPackageSecretSession (prin: Participant) (sid: Nat) (key: KeyPackage Bytes tkt):
  Traceful KeyPackageManagerValue
:=
  DySlop.Map.findValue prin sid key

end

end MLS.TreeSync
