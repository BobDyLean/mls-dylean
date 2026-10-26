module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeKEM.Code.NetworkTypes
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeKEM.Symbolic.State.UpdateCache`:
a map from the leaf nodes of our update proposals to the handles of the states of their private keys.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated,
  hence `rememberUpdateLeafSk` returns the new handle of the map.
- States are identified by handles (`Nat`) instead of session identifiers (`state_id`).
- The invariants (`update_cache_pred`, …) and the proofs are not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-- Port of `update_cache_key`. -/
public
structure UpdateCacheKey where
  leafNode: LeafNode Bytes tkt

namespace UpdateCacheKey

public
def f: LeafNode Bytes tkt → UpdateCacheKey :=
  fun leafNode => { leafNode }

public
def g: UpdateCacheKey → LeafNode Bytes tkt :=
  fun x => x.leafNode

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end UpdateCacheKey

/-- Port of `ps_update_cache_key`. -/
public
def UpdateCacheKey.mf: NonExtensibleMessageFormat Bytes UpdateCacheKey :=
  .isomorphic (LeafNode.mf tkt) UpdateCacheKey.f UpdateCacheKey.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_update_cache_key_is_well_formed`. -/
@[simp]
public
theorem UpdateCacheKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UpdateCacheKey):
  UpdateCacheKey.mf.wf pred x = (LeafNode.mf tkt).wf pred x.leafNode
:= by
  simp only [UpdateCacheKey.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, UpdateCacheKey.g]

/-- Port of `update_cache_value`. -/
public
structure UpdateCacheValue where
  leafSkSid: Nat

namespace UpdateCacheValue

public
def f: Nat → UpdateCacheValue :=
  fun leafSkSid => { leafSkSid }

public
def g: UpdateCacheValue → Nat :=
  fun x => x.leafSkSid

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end UpdateCacheValue

/-- Port of `ps_update_cache_value`. -/
public
def UpdateCacheValue.mf: NonExtensibleMessageFormat Bytes UpdateCacheValue :=
  .isomorphic .slowNat UpdateCacheValue.f UpdateCacheValue.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_update_cache_value_is_well_formed`. -/
@[simp]
public
theorem UpdateCacheValue.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: UpdateCacheValue):
  UpdateCacheValue.mf.wf pred x = True
:= by
  simp [UpdateCacheValue.mf, UpdateCacheValue.g]

/-- Port of `update_cache_types`. -/
public
instance updateCacheTypes: MapTypes UpdateCacheKey UpdateCacheValue where
  mfKey := UpdateCacheKey.mf
  mfValue := UpdateCacheValue.mf

/-! ## Update cache API -/

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map UpdateCacheKey UpdateCacheValue))]

/-- Port of `initialize_update_cache`. -/
public
def initializeUpdateCache (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap UpdateCacheKey UpdateCacheValue prin

/-- Port of `find_update_leaf_sk`. -/
public
def findUpdateLeafSk (me: Participant) (sid: Nat) (leafNode: LeafNode Bytes tkt): Traceful Nat := do
  let v: UpdateCacheValue ← DySlop.Map.findValue me sid ({ leafNode }: UpdateCacheKey)
  pure v.leafSkSid

/--
Port of `remember_update_leaf_sk`.
Returns the new handle of the update cache.
-/
public
def rememberUpdateLeafSk (me: Participant) (sid: Nat) (leafNode: LeafNode Bytes tkt) (leafSkSid: Nat): Traceful Nat :=
  DySlop.Map.addKeyValue me sid ({ leafNode }: UpdateCacheKey) ({ leafSkSid }: UpdateCacheValue)

end MLS.TreeKEM
