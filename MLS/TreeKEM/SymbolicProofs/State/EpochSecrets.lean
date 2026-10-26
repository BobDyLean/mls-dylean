module

public import MLS.TreeKEM.SymbolicSpec.State.EpochSecrets
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.TreeSync.Proofs.TreeHash
public import MLS.TreeKEM.Code.Parsers
public import DySlop.Lib.Label

/-!
Port of the usages, labels and predicates of `MLS.TreeKEM.Symbolic.State.EpochSecrets`:
the usages and labels of the secrets of an epoch.

Port-specific differences:
- MLS*'s usage data `{group_context}` (`epoch_secret_usage_data`) is the serialized group context
  (the serialization of a structure with one field is the serialization of this field).
- DY*'s `typed_state_pred_label (mk_principal_epoch_secret_label_pred prin ty group_context)` is a DyLean label
  whose corruption is the compromise of an epoch secret state of `prin` with the type `ty` and the group context
  `group_context` (as `MLS.TreeSync.signatureKeyLabel`); `mk_principal_epoch_secret_label_pred` is inlined.
- MLS*'s `full_tree` (a tree at position `0`) is `OneTreeSync Bytes tkt` (a tree at any position):
  the tree hash determines the position.
- The lemmas on these labels (`mk_group_secret_label_eq`, `mk_group_secret_label_can_flow_my_label`, …),
  `key_is_authenticated_by_confirmation_tag`, the state invariant (`treekem_epoch_secret_state_pred`)
  and the proofs of the traceful functions are not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open MLS MLS.TreeSync

section Usages

variable [HasSymbolicBytes]

/-- Port of `mk_epoch_secret_usage`. -/
@[expose]
public
def mkEpochSecretUsage (ty: EpochSecretType) (groupContext: GroupContext Bytes): Usage :=
  let data := serializeNE GroupContext.mf groupContext
  match ty with
  | .initSecret => Usage.kdfExpandKey "MLS.TreeKEM.InitSecret" data
  | .senderDataSecret => Usage.kdfExpandKey "MLS.TreeDEM.SenderDataSecret" data
  | .encryptionSecret => Usage.kdfExpandKey "MLS.TreeDEM.EncryptionSecret" data
  | .exporterSecret => Usage.kdfExpandKey "MLS.TreeKEM.ExporterSecret" data
  | .externalSecret => Usage.nothing
  | .confirmationKey => Usage.macKey "MLS.TreeKEM.ConfirmationKey" data
  | .membershipKey => Usage.nothing
  | .resumptionPsk => Usage.nothing
  | .epochAuthenticator => Usage.nothing

end Usages

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMEpochSecret)]

/--
Port of `mk_principal_epoch_secret_label` (with `mk_principal_epoch_secret_label_pred`):
the secret of type `ty` of `prin` in the epoch with group context `groupContext` is corrupt
when an epoch secret state of `prin` with this type and group context is compromised.
-/
@[expose]
public
def mkPrincipalEpochSecretLabel (ty: EpochSecretType) (prin: Participant) (groupContext: GroupContext Bytes): Label where
  isCorrupt tr :=
    ∃ confirmationTag secret,
      PersistentLocalState.LocalStateCompromised prin ({ ty, context := groupContext, confirmationTag, secret }: TreeKEMEpochSecret) tr

end Labels

section GroupLabels

variable [HasSymbolicBytes] [ExecTraceTypes]

/-- Port of `mk_tree_secret_label_aux`. -/
@[expose]
public
def mkTreeSecretLabelAux {l: Nat} (mkLabel: Participant → GroupContext Bytes → Label)
  (groupContext: GroupContext Bytes) (t: TreeSync Bytes tkt l) (li: Nat): Label :=
  match leafAt t li with
  | none => Label.secret
  | some leafNode =>
    match credentialToPrincipal leafNode.data.credential with
    | none => Label.unknown
    | some prin => mkLabel prin groupContext

/-- Port of `mk_tree_secret_label`. -/
@[expose]
public
def mkTreeSecretLabel {l: Nat} (mkLabel: Participant → GroupContext Bytes → Label)
  (groupContext: GroupContext Bytes) (t: TreeSync Bytes tkt l): Label :=
  Label.bigJoin (mkTreeSecretLabelAux mkLabel groupContext t)

/-- Port of `tree_hash_full_tree_rel`. -/
@[expose]
public
def TreeHashFullTreeRel (tHash: Bytes) (ft: OneTreeSync Bytes tkt): Prop :=
  TreeHasHash ft.2 tHash

/-- Port of `mk_group_secret_label_aux`. -/
@[expose]
public
def mkGroupSecretLabelAux (mkLabel: Participant → GroupContext Bytes → Label)
  (groupContext: GroupContext Bytes) (ft: OneTreeSync Bytes tkt): Label :=
  (Label.ofProp (TreeHashFullTreeRel groupContext.treeHash.val ft)).meet (mkTreeSecretLabel mkLabel groupContext ft.2)

/-- Port of `mk_group_secret_label`. -/
@[expose]
public
def mkGroupSecretLabel (mkLabel: Participant → GroupContext Bytes → Label) (groupContext: GroupContext Bytes): Label :=
  Label.bigJoin (mkGroupSecretLabelAux mkLabel groupContext)

end GroupLabels

section Predicates

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMEpochSecret)]

/-- Port of `is_epoch_secret`. -/
@[expose]
public
def IsEpochSecret (tr: ProofTrace) (ty: EpochSecretType) (groupContext: GroupContext Bytes) (secret: Bytes): Prop :=
  secret.Invariant tr ∧
  (secret.label tr).canFlow (mkGroupSecretLabel (mkPrincipalEpochSecretLabel ty) groupContext) tr.erase ∧
  secret.HasUsage (mkEpochSecretUsage ty groupContext) tr

end Predicates

end MLS.TreeKEM
