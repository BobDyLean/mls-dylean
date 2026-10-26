module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Common.Code.NetworkTypes
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeSync.Symbolic.State.GroupManager`:
a map from group identifiers to the handles of the public and private states of the group.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated.
- States are identified by handles (`Nat`) instead of session identifiers (`state_id`).
  As DyLean's states are immutable, the handle of the public state changes when it is updated:
  the group manager must then be updated too.
- The invariants (`group_manager_pred`, …) are not ported yet.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-! ## Group manager types -/

/-- Port of `group_manager_key`. -/
public
structure GroupManagerKey where
  groupId: MlsBytes Bytes

namespace GroupManagerKey

public
def f: MlsBytes Bytes → GroupManagerKey :=
  fun groupId => { groupId }

public
def g: GroupManagerKey → MlsBytes Bytes :=
  fun x => x.groupId

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end GroupManagerKey

/-- Port of `ps_group_manager_key`. -/
public
def GroupManagerKey.mf: NonExtensibleMessageFormat Bytes GroupManagerKey :=
  .isomorphic MlsBytes.mf GroupManagerKey.f GroupManagerKey.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_group_manager_key_is_well_formed`. -/
@[simp]
public
theorem GroupManagerKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupManagerKey):
  GroupManagerKey.mf.wf pred x = pred x.groupId.val
:= by
  simp [GroupManagerKey.mf, GroupManagerKey.g]

/-- Port of `group_manager_value`. -/
public
structure GroupManagerValue where
  siPublic: Nat
  siPrivate: Nat

namespace GroupManagerValue

public
def f: Nat × Nat → GroupManagerValue :=
  fun (siPublic, siPrivate) => { siPublic, siPrivate }

public
def g: GroupManagerValue → Nat × Nat :=
  fun { siPublic, siPrivate } => (siPublic, siPrivate)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end GroupManagerValue

/-- Port of `ps_group_manager_value`. -/
public
def GroupManagerValue.mf: NonExtensibleMessageFormat Bytes GroupManagerValue :=
  .isomorphic (.prod .slowNat .slowNat) GroupManagerValue.f GroupManagerValue.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_group_manager_value_is_well_formed`. -/
@[simp]
public
theorem GroupManagerValue.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: GroupManagerValue):
  GroupManagerValue.mf.wf pred x = True
:= by
  simp [GroupManagerValue.mf, GroupManagerValue.g]

/-- Port of `group_manager_types`. -/
public
instance groupManagerTypes: MapTypes GroupManagerKey GroupManagerValue where
  mfKey := GroupManagerKey.mf
  mfValue := GroupManagerValue.mf

/-! ## Group manager API -/

variable [ExecTraceTypes] [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map GroupManagerKey GroupManagerValue))]

/-- Port of `initialize_group_manager`. -/
public
def initializeGroupManager (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap GroupManagerKey GroupManagerValue prin

/-- Port of `add_new_group_sessions`. -/
public
def addNewGroupSessions (prin: Participant) (sid: Nat) (key: GroupManagerKey) (value: GroupManagerValue): Traceful Nat :=
  DySlop.Map.addKeyValue prin sid key value

/-- Port of `find_group_sessions`. -/
public
def findGroupSessions (prin: Participant) (sid: Nat) (key: GroupManagerKey): Traceful GroupManagerValue :=
  DySlop.Map.findValue prin sid key

end MLS.TreeSync
