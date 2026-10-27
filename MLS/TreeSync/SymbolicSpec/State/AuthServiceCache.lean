module

public import MLS.Symbolic.Code.Symbolic
public import MLS.Common.Code.NetworkTypes
public import MLS.TreeSync.SymbolicSpec.AuthService
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.TreeSync.SymbolicSpec.State.SignatureKey
public import DySlop.Lib.State.Map

/-!
Port of `MLS.TreeSync.Symbolic.State.AuthServiceCache`:
a map from (signature verification key, credential) to the tokens of the Authentication Service.

Port-specific differences:
- The map is a DyLean local state (see `DySlop.Map`): its handle changes when it is updated.
- The invariants (`as_cache_pred`, …) are in `MLS.TreeSync.SymbolicProofs.State.AuthServiceCache`.
- `verifyCredential` is not in MLS*: it fills the AS cache (as an honest PKI),
  for the reachability configuration (`MLS.TreeKEM.SymbolicSpec.Reachability`) and the sanity checks.
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

/-! ## Credential verification -/

variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeSyncSignatureKeyState)]

/--
The authentication service of `me` verifies the credential of `who`, whose signature key state has handle
`whoSignatureKeySid`, and stores it in the AS cache of `me` (with handle `authServiceSid`).
Returns the new handle of the AS cache.
Not in MLS*, where the authentication service is not specified: it models an honest PKI,
which reads the verification key of `who` in its state.
The token is the current time: the signature key of `who` exists in the prefix of the trace before it.
-/
public
def verifyCredential (me: Participant) (authServiceSid: Nat) (who: Participant) (whoSignatureKeySid: Nat): Traceful Nat := do
  let verificationKey ← getSignatureKeyVk who whoSignatureKeySid
  let verificationKey ← extractResult (mkMlsBytes verificationKey "verifyCredential" "verificationKey")
  let some credential := principalToCredential (Bytes := Bytes) who | failure
  let time ← getTimestamp
  addVerifiedCredential me authServiceSid { verificationKey, credential } { token := { time } }

end MLS.TreeSync
