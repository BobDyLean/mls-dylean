module

public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.TreeSync.Symbolic.State.SignatureKey`.

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState`):
  it has no tag (MLS*'s `local_state` instance).
- States are identified by handles instead of session identifiers: `mkSignatureKey` returns the handle of the new state.
- The usage and label of the signature key (the arguments of MLS*'s `my_mk_rand`)
  are ghost arguments of the proofs in DyLean (`Random.genRand`).
- The labels (`signature_key_label`, …) and the predicates (`is_signature_key_sk`, `is_signature_key_vk`)
  are in `MLS.TreeSync.SymbolicProofs.State.SignatureKey`;
  so are the state invariant (`treesync_signature_key_state_pred`) and the proofs.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS

/-- Port of `treesync_signature_key_state`. -/
public
structure TreeSyncSignatureKeyState [BytesFunctor] where
  signatureSk: Bytes

variable [HasSymbolicBytes]

namespace TreeSyncSignatureKeyState

public
def f: Bytes → TreeSyncSignatureKeyState :=
  fun signatureSk => { signatureSk }

public
def g: TreeSyncSignatureKeyState → Bytes :=
  fun x => x.signatureSk

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end TreeSyncSignatureKeyState

/-- Port of `ps_treesync_signature_key_state`. -/
public
def TreeSyncSignatureKeyState.mf: NonExtensibleMessageFormat Bytes TreeSyncSignatureKeyState :=
  .isomorphic .unboundedBytes TreeSyncSignatureKeyState.f TreeSyncSignatureKeyState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_treesync_signature_key_state_is_well_formed`. -/
@[simp]
public
theorem TreeSyncSignatureKeyState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeSyncSignatureKeyState):
  TreeSyncSignatureKeyState.mf.wf pred x = pred x.signatureSk
:= by
  simp [TreeSyncSignatureKeyState.mf, TreeSyncSignatureKeyState.g]

/-- Port of `local_state_treesync_signature_key_state` (for its format). -/
public
instance TreeSyncSignatureKeyState.ps: ParseableSerializeableNE TreeSyncSignatureKeyState :=
  .make TreeSyncSignatureKeyState.mf

variable [ExecTraceTypes] [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `mk_signature_key`. Returns the handle of the new state. -/
public
def mkSignatureKey (prin: Participant): Traceful Nat := do
  let sk ← Random.genRand 32
  PersistentLocalState.storeLocalState prin ({ signatureSk := sk }: TreeSyncSignatureKeyState)

/-- Port of `get_signature_key_sk`. -/
public
def getSignatureKeySk (prin: Participant) (sid: Nat): Traceful Bytes := do
  let st: TreeSyncSignatureKeyState ← PersistentLocalState.getLocalState prin sid
  pure st.signatureSk

/-- Port of `get_signature_key_vk`. -/
public
def getSignatureKeyVk (prin: Participant) (sid: Nat): Traceful Bytes := do
  let sk ← getSignatureKeySk prin sid
  pure (DySlop.Signature.vk sk)

end MLS.TreeSync
