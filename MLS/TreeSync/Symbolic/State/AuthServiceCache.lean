module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Common.Code.NetworkTypes
public import MLS.TreeSync.Symbolic.AuthService
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeSync.Symbolic.State.AuthServiceCache`:
a map from (signature verification key, credential) to the tokens of the Authentication Service.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated.
- The invariants (`as_cache_pred`, …) are not ported yet.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS
open DySlop.Map (MapTypes Map)

variable [HasSymbolicBytes]

/-! ## AS cache types -/

/-- Port of `as_cache_key`. -/
public
structure AsCacheKey where
  verificationKey: SignaturePublicKey Bytes
  credential: Credential Bytes

namespace AsCacheKey

public
def f: SignaturePublicKey Bytes × Credential Bytes → AsCacheKey :=
  fun (verificationKey, credential) => { verificationKey, credential }

public
def g: AsCacheKey → SignaturePublicKey Bytes × Credential Bytes :=
  fun { verificationKey, credential } => (verificationKey, credential)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end AsCacheKey

/-- Port of `ps_as_cache_key`. -/
public
def AsCacheKey.mf: NonExtensibleMessageFormat Bytes AsCacheKey :=
  .isomorphic (.prod SignaturePublicKey.mf Credential.mf) AsCacheKey.f AsCacheKey.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_as_cache_key_is_well_formed`. -/
@[simp]
public
theorem AsCacheKey.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: AsCacheKey):
  AsCacheKey.mf.wf pred x = (pred x.verificationKey.val ∧ Credential.mf.wf pred x.credential)
:= by
  simp [AsCacheKey.mf, AsCacheKey.g]

/-- Port of `as_cache_value`. -/
public
structure AsCacheValue where
  token: DyAsToken

namespace AsCacheValue

public
def f: DyAsToken → AsCacheValue :=
  fun token => { token }

public
def g: AsCacheValue → DyAsToken :=
  fun x => x.token

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end AsCacheValue

/-- Port of `ps_as_cache_value`. -/
public
def AsCacheValue.mf: NonExtensibleMessageFormat Bytes AsCacheValue :=
  .isomorphic DyAsToken.mf AsCacheValue.f AsCacheValue.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_as_cache_value_is_well_formed`. -/
@[simp]
public
theorem AsCacheValue.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: AsCacheValue):
  AsCacheValue.mf.wf pred x = True
:= by
  simp [AsCacheValue.mf, AsCacheValue.g]

/-- Port of `as_cache_types`. -/
public
instance asCacheTypes: MapTypes AsCacheKey AsCacheValue where
  mfKey := AsCacheKey.mf
  mfValue := AsCacheValue.mf

/-! ## AS cache API -/

variable [ExecTraceTypes] [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT (Map AsCacheKey AsCacheValue))]

/-- Port of `initialize_as_cache`. -/
public
def initializeAsCache (prin: Participant): Traceful Nat :=
  DySlop.Map.initializeMap AsCacheKey AsCacheValue prin

/-- Port of `add_verified_credential`. -/
public
def addVerifiedCredential (prin: Participant) (sid: Nat) (key: AsCacheKey) (value: AsCacheValue): Traceful Nat :=
  DySlop.Map.addKeyValue prin sid key value

/-- Port of `find_verified_credential`. -/
public
def findVerifiedCredential (prin: Participant) (sid: Nat) (key: AsCacheKey): Traceful AsCacheValue :=
  DySlop.Map.findValue prin sid key

end MLS.TreeSync
