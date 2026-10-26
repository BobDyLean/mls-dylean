module

public import MLS.TreeKEM.Symbolic.State.OnePSKStore
public import DySlop.Lib.State.Map
public import MLS.Common.Code.Crypto.Derived

/-!
Port of `MLS.TreeKEM.Symbolic.State.PSKStore`: a map from pre-shared key identifiers to the handles of their states.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated,
  hence `rememberPsk` returns the new handle of the map.
- States are identified by handles (`Nat`) instead of session identifiers (`state_id`).
- Pre-shared key identifiers have no decidable equality: `retrievePsks` compares their serializations.
- The invariants (`psk_store_pred`, …) and the proofs are not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-! ## PSK ID → PSK state id -/

/-- Port of `psk_store_key`. -/
public
structure PskStoreKey where
  pskId: PreSharedKeyIdShort

namespace PskStoreKey

public
def f: PreSharedKeyIdShort → PskStoreKey :=
  fun pskId => { pskId }

public
def g: PskStoreKey → PreSharedKeyIdShort :=
  fun x => x.pskId

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end PskStoreKey

/-- Port of `ps_psk_store_key`. -/
public
def PskStoreKey.mf: NonExtensibleMessageFormat Bytes PskStoreKey :=
  .isomorphic PreSharedKeyIdShort.mf PskStoreKey.f PskStoreKey.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_psk_store_key_is_well_formed`. -/
@[simp]
public
theorem PskStoreKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PskStoreKey):
  PskStoreKey.mf.wf pred x = PreSharedKeyIdShort.mf.wf pred x.pskId
:= by
  simp only [PskStoreKey.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, PskStoreKey.g]

/-- Port of `psk_store_value`. -/
public
structure PskStoreValue where
  pskSid: Nat

namespace PskStoreValue

public
def f: Nat → PskStoreValue :=
  fun pskSid => { pskSid }

public
def g: PskStoreValue → Nat :=
  fun x => x.pskSid

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end PskStoreValue

/-- Port of `ps_psk_store_value`. -/
public
def PskStoreValue.mf: NonExtensibleMessageFormat Bytes PskStoreValue :=
  .isomorphic .slowNat PskStoreValue.f PskStoreValue.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_psk_store_value_is_well_formed`. -/
@[simp]
public
theorem PskStoreValue.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PskStoreValue):
  PskStoreValue.mf.wf pred x = True
:= by
  simp [PskStoreValue.mf, PskStoreValue.g]

/-- Port of `psk_store_types`. -/
public
instance pskStoreTypes: MapTypes PskStoreKey PskStoreValue where
  mfKey := PskStoreKey.mf
  mfValue := PskStoreValue.mf

/-! ## PSK Store API -/

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map PskStoreKey PskStoreValue))]

/-- Port of `initialize_psk_store`. -/
public
def initializePskStore (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap PskStoreKey PskStoreValue prin

variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT OnePskState)]

/-- Port of `retrieve_psks`. -/
public
def retrievePsks (me: Participant) (sid: Nat): List (PreSharedKeyId Bytes) → Traceful (List (PreSharedKeyId Bytes × Bytes))
  | [] => pure []
  | h :: t => do
    let value: PskStoreValue ← DySlop.Map.findValue me sid ({ pskId := shortenPreSharedKeyId h }: PskStoreKey)
    let (pskId, psk) ← getPsk me value.pskSid
    guard (serializeNE PreSharedKeyIdShort.mf pskId = serializeNE PreSharedKeyIdShort.mf (shortenPreSharedKeyId h))
    let pskTail ← retrievePsks me sid t
    pure ((h, psk) :: pskTail)

/--
Port of `remember_psk`.
Returns the new handle of the PSK store.
-/
public
def rememberPsk (me: Participant) (sid: Nat) (pskId: PreSharedKeyIdShort) (psk: Bytes): Traceful Nat := do
  let pskSid ← storePsk me pskId psk
  DySlop.Map.addKeyValue me sid ({ pskId }: PskStoreKey) ({ pskSid }: PskStoreValue)

end MLS.TreeKEM
