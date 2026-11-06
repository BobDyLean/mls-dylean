module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeKEM.Code.API.KeySchedule.Types
public import MLS.Common.Code.Crypto.Derived

/-!
Port of `MLS.TreeKEM.Symbolic.State.EpochSecrets`: the states storing the secrets of an epoch
(one state per secret, so that each secret has its own label).

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT TreeKEMEpochSecret`): it has no tag.
- States are identified by handles instead of session identifiers.
- Group contexts have no decidable equality: `getEpochSecret` compares their serializations.
- The usages and labels (`mk_epoch_secret_usage`, `mk_group_secret_label`, …) are in
  `MLS.TreeKEM.SymbolicProofs.State.EpochSecrets`, with the invariants and proofs;
  so is `keyschedule_state_to_key`, which only the invariant uses.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS

/-! ## Local state -/

/-- Port of `epoch_secret_type`. -/
public
inductive EpochSecretType where
  | initSecret
  | senderDataSecret
  /-- The encryption secret should be managed by TreeDEM (once it is proved) -/
  | encryptionSecret
  | exporterSecret
  | externalSecret
  | confirmationKey
  | membershipKey
  | resumptionPsk
  | epochAuthenticator
deriving DecidableEq

namespace EpochSecretType

public
def ofFin: Fin 9 → EpochSecretType
  | 0 => .initSecret
  | 1 => .senderDataSecret
  | 2 => .encryptionSecret
  | 3 => .exporterSecret
  | 4 => .externalSecret
  | 5 => .confirmationKey
  | 6 => .membershipKey
  | 7 => .resumptionPsk
  | 8 => .epochAuthenticator

public
def toFin: EpochSecretType → Fin 9
  | .initSecret => 0
  | .senderDataSecret => 1
  | .encryptionSecret => 2
  | .exporterSecret => 3
  | .externalSecret => 4
  | .confirmationKey => 5
  | .membershipKey => 6
  | .resumptionPsk => 7
  | .epochAuthenticator => 8

public
instance: LeftInverse toFin ofFin := ⟨by intro x; revert x; decide⟩
public
instance: RightInverse toFin ofFin := ⟨by intro x; cases x <;> rfl⟩

end EpochSecretType

variable [HasSymbolicBytes]

/-- Port of `ps_epoch_secret_type`. -/
public
def EpochSecretType.mf: NonExtensibleMessageFormat Bytes EpochSecretType :=
  .isomorphic (.fin8 9 (by decide)) EpochSecretType.ofFin EpochSecretType.toFin
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_epoch_secret_type_is_well_formed`. -/
@[simp]
public
theorem EpochSecretType.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: EpochSecretType):
  EpochSecretType.mf.wf pred x = True
:= by
  simp [EpochSecretType.mf]

/-- Port of `treekem_epoch_secret`. -/
public
structure TreeKEMEpochSecret where
  ty: EpochSecretType
  context: GroupContext Bytes
  confirmationTag: Bytes
  secret: Bytes

namespace TreeKEMEpochSecret

public
def f: EpochSecretType × GroupContext Bytes × Bytes × Bytes → TreeKEMEpochSecret :=
  fun (ty, context, confirmationTag, secret) => { ty, context, confirmationTag, secret }

public
def g: TreeKEMEpochSecret → EpochSecretType × GroupContext Bytes × Bytes × Bytes :=
  fun { ty, context, confirmationTag, secret } => (ty, context, confirmationTag, secret)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end TreeKEMEpochSecret

/-- Port of `ps_treekem_epoch_secret`. -/
public
def TreeKEMEpochSecret.mf: NonExtensibleMessageFormat Bytes TreeKEMEpochSecret :=
  .isomorphic (.prod EpochSecretType.mf (.prod GroupContext.mf (.prod .unboundedBytes .unboundedBytes)))
    TreeKEMEpochSecret.f TreeKEMEpochSecret.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_treekem_epoch_secret_is_well_formed`. -/
@[simp]
public
theorem TreeKEMEpochSecret.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeKEMEpochSecret):
  TreeKEMEpochSecret.mf.wf pred x = (GroupContext.mf.wf pred x.context ∧ pred x.confirmationTag ∧ pred x.secret)
:= by
  simp only [TreeKEMEpochSecret.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, TreeKEMEpochSecret.g,
    NonExtensibleMessageFormat.prod.wf_eq, EpochSecretType.mf.wf_eq, NonExtensibleMessageFormat.unboundedBytes.wf_eq, true_and]

/-- Port of `local_state_treekem_epoch_secret` (for its format). -/
public
instance TreeKEMEpochSecret.ps: ParseableSerializeableNE TreeKEMEpochSecret :=
  .make TreeKEMEpochSecret.mf

/-! ## Traceful API -/

variable [ExecTraceTypes] [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeKEMEpochSecret)]

/-- Port of `store_epoch_secret`. Returns the handle of the new state. -/
public
def storeEpochSecret (me: Participant)
  (ty: EpochSecretType) (context: GroupContext Bytes) (confirmationTag: Bytes) (secret: Bytes): Traceful Nat
:=
  PersistentLocalState.storeLocalState me ({ ty, context, confirmationTag, secret }: TreeKEMEpochSecret)

/-- Port of `get_epoch_secret`. -/
public
def getEpochSecret (me: Participant)
  (sid: Nat) (ty: EpochSecretType) (context: GroupContext Bytes) (confirmationTag: Bytes): Traceful Bytes
:= do
  let st: TreeKEMEpochSecret ← PersistentLocalState.getLocalState me sid
  guard (st.ty = ty)
  guard (serializeNE GroupContext.mf st.context = serializeNE GroupContext.mf context)
  guard (st.confirmationTag = confirmationTag)
  pure st.secret

end MLS.TreeKEM
