module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeKEM.Code.NetworkTypes

/-!
Port of `MLS.TreeKEM.Symbolic.State.OnePSKStore`: the state storing one pre-shared key.

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT OnePskState`): it has no tag.
- States are identified by handles instead of session identifiers.
- The label (`psk_label`) is in `MLS.TreeKEM.SymbolicProofs.State.OnePSKStore`;
  so are the invariants and proofs.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS

variable [HasSymbolicBytes]

/-! ## One PSK -/

/--
Port of `pre_shared_key_id_short`.
Like `PreSharedKeyId`, without psk_nonce etc.
-/
public
inductive PreSharedKeyIdShort where
  | externalPsk (pskId: MlsBytes Bytes)
  | resumptionPsk (groupId: MlsBytes Bytes) (epoch: UInt64)

namespace PreSharedKeyIdShort

/-- Exposed, as the compiler needs to compute the types of its values. -/
@[expose]
public
def internalType: Fin 2 → Type
  | 0 => MlsBytes Bytes
  | 1 => MlsBytes Bytes × UInt64

public
def internalType.mf: (t: Fin 2) → NonExtensibleMessageFormat Bytes (internalType t)
  | 0 => MlsBytes.mf
  | 1 => .prod MlsBytes.mf .uint64BE

public
instance: ∀ t, (internalType.mf t).IsNonAmbiguous
  | 0 | 1 => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
instance: ∀ t, (internalType.mf t).HasUniqueRepresentation
  | 0 | 1 => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
instance: ∀ t, (internalType.mf t).ParseConsumes
  | 0 | 1 => by
    dsimp only [internalType.mf, internalType]
    infer_instance

public
def f: (t: Fin 2) × internalType t → PreSharedKeyIdShort
  | ⟨0, pskId⟩ => .externalPsk pskId
  | ⟨1, (groupId, epoch)⟩ => .resumptionPsk groupId epoch

public
def g: PreSharedKeyIdShort → (t: Fin 2) × internalType t
  | .externalPsk pskId => ⟨0, pskId⟩
  | .resumptionPsk groupId epoch => ⟨1, (groupId, epoch)⟩

public
instance: LeftInverse g f := ⟨by
  intro ⟨t, x⟩
  match t, x with
  | 0, _ => rfl
  | 1, _ => rfl⟩
public
instance: RightInverse g f := ⟨by intro x; cases x <;> rfl⟩

end PreSharedKeyIdShort

/-- Port of `ps_pre_shared_key_id_short`. -/
public
def PreSharedKeyIdShort.mf: NonExtensibleMessageFormat Bytes PreSharedKeyIdShort :=
  .isomorphic (.sigma (.fin8 2 (by decide)) PreSharedKeyIdShort.internalType.mf) PreSharedKeyIdShort.f PreSharedKeyIdShort.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_pre_shared_key_id_short_is_well_formed`. -/
@[simp]
public
theorem PreSharedKeyIdShort.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: PreSharedKeyIdShort):
  PreSharedKeyIdShort.mf.wf pred x = (
    match x with
    | .externalPsk pskId => pred pskId.val
    | .resumptionPsk groupId _ => pred groupId.val
  )
:= by
  cases x <;> simp [PreSharedKeyIdShort.mf, PreSharedKeyIdShort.g] <;>
    simp [PreSharedKeyIdShort.internalType.mf, PreSharedKeyIdShort.internalType]

/-- Port of `shorten_pre_shared_key_id`. -/
public
def shortenPreSharedKeyId (pskId: PreSharedKeyId Bytes): PreSharedKeyIdShort :=
  match pskId with
  | .external pskId _ => .externalPsk pskId
  | .resumption _ pskGroupId pskEpoch _ => .resumptionPsk pskGroupId pskEpoch

/-- Port of `one_psk_state`. -/
public
structure OnePskState where
  pskId: PreSharedKeyIdShort
  psk: Bytes

namespace OnePskState

public
def f: PreSharedKeyIdShort × Bytes → OnePskState :=
  fun (pskId, psk) => { pskId, psk }

public
def g: OnePskState → PreSharedKeyIdShort × Bytes :=
  fun { pskId, psk } => (pskId, psk)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end OnePskState

/-- Port of `ps_one_psk_state`. -/
public
def OnePskState.mf: NonExtensibleMessageFormat Bytes OnePskState :=
  .isomorphic (.prod PreSharedKeyIdShort.mf .unboundedBytes) OnePskState.f OnePskState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_one_psk_state_is_well_formed`. -/
@[simp]
public
theorem OnePskState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: OnePskState):
  OnePskState.mf.wf pred x = (PreSharedKeyIdShort.mf.wf pred x.pskId ∧ pred x.psk)
:= by
  simp only [OnePskState.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, OnePskState.g,
    NonExtensibleMessageFormat.prod.wf_eq, NonExtensibleMessageFormat.unboundedBytes.wf_eq]

/-- Port of `local_state_one_psk_state` (for its format). -/
public
instance OnePskState.ps: ParseableSerializeableNE OnePskState :=
  .make OnePskState.mf

variable [ExecTraceTypes] [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT OnePskState)]

/-- Port of `get_psk`. -/
public
def getPsk (me: Participant) (pskSid: Nat): Traceful (PreSharedKeyIdShort × Bytes) := do
  let st: OnePskState ← PersistentLocalState.getLocalState me pskSid
  pure (st.pskId, st.psk)

/-- Port of `store_psk`. Returns the handle of the new state. -/
public
def storePsk (me: Participant) (pskId: PreSharedKeyIdShort) (psk: Bytes): Traceful Nat :=
  PersistentLocalState.storeLocalState me ({ pskId, psk }: OnePskState)

end MLS.TreeKEM
