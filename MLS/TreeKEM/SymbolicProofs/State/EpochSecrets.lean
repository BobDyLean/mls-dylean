module

public import MLS.TreeKEM.SymbolicSpec.State.EpochSecrets
public import MLS.TreeSync.SymbolicSpec.AuthService.CredentialInterpretation
public import MLS.TreeSync.Proofs.TreeHash
public import MLS.TreeKEM.Code.Parsers
public import DySlop.Lib.Label
public import MLS.TreeKEM.SymbolicProofs.ConfirmationTag
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeKEM.SymbolicSpec.State.EpochSecrets
import DY.Meta.Step

/-!
Port of the usages, labels, predicates and proofs of `MLS.TreeKEM.Symbolic.State.EpochSecrets`:
the usages and labels of the secrets of an epoch, the invariant of epoch secret states,
and the proofs of the traceful functions.

Port-specific differences:
- MLS*'s usage data `{group_context}` (`epoch_secret_usage_data`) is the serialized group context
  (the serialization of a structure with one field is the serialization of this field).
- DY*'s `typed_state_pred_label (mk_principal_epoch_secret_label_pred prin ty group_context)` is a DyLean label
  whose corruption is the compromise of an epoch secret state of `prin` with the type `ty` and the group context
  `group_context` (as `MLS.TreeSync.signatureKeyLabel`); `mk_principal_epoch_secret_label_pred` is inlined.
- MLS*'s `full_tree` (a tree at position `0`) is `OneTreeSync Bytes tkt` (a tree at any position):
  the tree hash determines the position.
- MLS*'s `leaf_index l 0` arguments (`i_am_in_tree_at`, …) are plain `Nat`s (`leafAt` is `none` outside the tree).
  MLS*'s `Some?.v` in `mk_tree_secret_label_is_corrupt` are existentials.
- The state predicate (`treekem_epoch_secret_state_pred`) is the DyLean state invariant `treekemEpochSecretStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_treekem_epoch_secret_state_invariant` is not needed.
- The proofs of the traceful functions (`store_epoch_secret_proof`, …) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the state. The `tr_out == tr` part of their postconditions is not ported.
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

/-- Port of `mk_group_secret_label_eq`. -/
public
theorem mkGroupSecretLabel_eq {l: Nat} (mkLabel: Participant → GroupContext Bytes → Label)
  (groupContext: GroupContext Bytes) (t: TreeSync Bytes tkt l)
  (h: TreeHasHash t groupContext.treeHash.val):
  mkGroupSecretLabel mkLabel groupContext = mkTreeSecretLabel mkLabel groupContext t
:= by
  apply Label.ext
  intro tr
  apply propext
  simp only [mkGroupSecretLabel, mkGroupSecretLabelAux, Label.bigJoin_isCorrupt, Label.meetIsCorrupt,
    Label.ofProp_isCorrupt, TreeHashFullTreeRel]
  constructor
  · rintro ⟨⟨l2, t2⟩, h2, hc⟩
    rcases treeHashInj_spec t t2 _ h h2 with heq | hcoll
    · obtain ⟨rfl, heq⟩ := Sigma.mk.inj heq
      rw [heq_eq_eq] at heq
      grind
    · exact absurd hcoll (not_isHashCollision _)
  · intro hc
    exact ⟨⟨l, t⟩, h, hc⟩

/-- Port of `mk_tree_secret_label_is_corrupt`. -/
public
theorem mkTreeSecretLabel_isCorrupt {l: Nat} (tr: ExecTrace) (mkLabel: Participant → GroupContext Bytes → Label)
  (groupContext: GroupContext Bytes) (t: TreeSync Bytes tkt l)
  (hcred: ∀ li ln, leafAt t li = some ln → (credentialToPrincipal ln.data.credential).isSome)
  (h: (mkTreeSecretLabel mkLabel groupContext t).isCorrupt tr):
  ∃ li ln prin,
    leafAt t li = some ln ∧ credentialToPrincipal ln.data.credential = some prin ∧
    (mkLabel prin groupContext).isCorrupt tr
:= by
  obtain ⟨li, h⟩ := h
  simp only [mkTreeSecretLabelAux] at h
  split at h
  · exact absurd h (Label.secretIsCorrupt tr)
  · split at h
    · grind
    · grind

/-- Port of `i_am_in_tree_at`. -/
@[expose]
public
def IAmInTreeAt {l: Nat} (me: Participant) (t: TreeSync Bytes tkt l) (li: Nat): Prop :=
  ∃ ln, leafAt t li = some ln ∧ credentialToPrincipal ln.data.credential = some me

/-- Port of `i_am_in_group_context_with_witness`. -/
@[expose]
public
def IAmInGroupContextWithWitness {l: Nat} (me: Participant) (groupContext: GroupContext Bytes)
  (t: TreeSync Bytes tkt l) (li: Nat): Prop :=
  TreeHashFullTreeRel groupContext.treeHash.val ⟨l, t⟩ ∧ IAmInTreeAt me t li

/-- Port of `i_am_in_group_context`. -/
@[expose]
public
def IAmInGroupContext (me: Participant) (groupContext: GroupContext Bytes): Prop :=
  ∃ (l: Nat) (t: TreeSync Bytes tkt l) (li: Nat), IAmInGroupContextWithWitness me groupContext t li

omit [ExecTraceTypes] in
/-- Port of `intro_i_am_in_group_context`. -/
public
theorem IAmInGroupContext.intro {l: Nat} (me: Participant) (groupContext: GroupContext Bytes)
  (t: TreeSync Bytes tkt l) (li: Nat) (h: IAmInGroupContextWithWitness me groupContext t li):
  IAmInGroupContext me groupContext
:=
  ⟨l, t, li, h⟩

/-- Port of `mk_group_secret_label_can_flow_my_label`. -/
public
theorem mkGroupSecretLabel_canFlow_myLabel (tr: ExecTrace) (me: Participant)
  (mkLabel: Participant → GroupContext Bytes → Label) (groupContext: GroupContext Bytes)
  (h: IAmInGroupContext me groupContext):
  (mkGroupSecretLabel mkLabel groupContext).canFlow (mkLabel me groupContext) tr
:= by
  obtain ⟨l, t, li, hrel, ln, hln, hprin⟩ := h
  rw [mkGroupSecretLabel_eq mkLabel groupContext t hrel]
  have := Label.bigJoin_canFlow (mkTreeSecretLabelAux mkLabel groupContext t) li tr
  simp only [mkTreeSecretLabelAux, hln, hprin] at this
  exact this

end GroupLabels

section ConfirmationTag

variable [HasSymbolicBytes]

/-- Port of `key_is_authenticated_by_confirmation_tag_with_witness`. -/
@[expose]
public
def KeyIsAuthenticatedByConfirmationTagWithWitness (st: TreeKEMKeyscheduleState Bytes) (ty: EpochSecretType)
  (confirmationTag secret: Bytes): Prop :=
  TreekemKeyscheduleStateAuthWeakExists st ∧
  st.epochKeys.confirmationTag = confirmationTag ∧
  keyscheduleStateToKey st ty = secret

/-- Port of `key_is_authenticated_by_confirmation_tag`. -/
@[expose]
public
def KeyIsAuthenticatedByConfirmationTag (ty: EpochSecretType) (confirmationTag secret: Bytes): Prop :=
  ∃ st, KeyIsAuthenticatedByConfirmationTagWithWitness st ty confirmationTag secret

end ConfirmationTag

section ConfirmationTagInj

variable [HasSymbolicInvariants]

/-- Port of `key_is_authenticated_by_confirmation_tag_inj`. -/
public
theorem KeyIsAuthenticatedByConfirmationTag.inj (ty: EpochSecretType) (confirmationTag secret1 secret2: Bytes)
  (h1: KeyIsAuthenticatedByConfirmationTag ty confirmationTag secret1)
  (h2: KeyIsAuthenticatedByConfirmationTag ty confirmationTag secret2):
  secret1 = secret2
:= by
  obtain ⟨st1, hst1, htag1, rfl⟩ := h1
  obtain ⟨st2, hst2, htag2, rfl⟩ := h2
  rw [TreekemKeyscheduleStateAuthWeakExists.inj st1 st2 hst1 hst2 (by grind)]

end ConfirmationTagInj

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

/-- Epoch secrets stay epoch secrets when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IsEpochSecret_later (tr1 tr2: ProofTrace) (ty: EpochSecretType) (groupContext: GroupContext Bytes) (secret: Bytes)
  : tr1 ≤ tr2 →
    IsEpochSecret tr1 ty groupContext secret →
    IsEpochSecret tr2 ty groupContext secret
:= by
  grind [IsEpochSecret]

grind_pattern IsEpochSecret_later => tr1 ≤ tr2, IsEpochSecret tr1 ty groupContext secret
grind_pattern [grind_later] IsEpochSecret_later => tr1 ≤ tr2, IsEpochSecret tr1 ty groupContext secret

/-- Port of `treekem_epoch_secret_state_pred`: the invariant of epoch secret states. -/
public
instance treekemEpochSecretStateInv: PersistentLocalState.CompromisableLocalStateInv TreeKEMEpochSecret where
  invariant prin st tr :=
    IAmInGroupContext prin st.context ∧
    GroupContext.mf.wf (Bytes.Publishable · tr) st.context ∧
    st.confirmationTag.Publishable tr ∧
    IsEpochSecret tr st.ty st.context st.secret ∧
    KeyIsAuthenticatedByConfirmationTag st.ty st.confirmationTag st.secret
  invariant_later prin st tr1 tr2 := by
    grind
  invariant_implies_KnowableBy prin st tr h := by
    obtain ⟨ty, context, confirmationTag, secret⟩ := st
    obtain ⟨hgroup, hcontext, htag, hsecret, -⟩ := h
    have hflow: (mkPrincipalEpochSecretLabel ty prin context).canFlow
        (PersistentLocalState.label prin ({ ty, context, confirmationTag, secret }: TreeKEMEpochSecret)) tr.erase := by
      simp only [Label.canFlow, mkPrincipalEpochSecretLabel]
      grind
    have := mkGroupSecretLabel_canFlow_myLabel tr.erase prin (mkPrincipalEpochSecretLabel ty) context hgroup
    have := wf_knowableBy_of_publishable GroupContext.mf
      (PersistentLocalState.label prin ({ ty, context, confirmationTag, secret }: TreeKEMEpochSecret)) tr context hcontext
    simp only [DY.Comparse.IsWellFormed, DY.Comparse.ParseableSerializeable.mf, DY.Comparse.ParseableSerializeableNE.mf,
      NonExtensibleMessageFormat.toExtensible.wf_eq, TreeKEMEpochSecret.mf.wf_eq]
    grind [IsEpochSecret, Bytes.Publishable, Bytes.KnowableBy, canFlowTrans]

end Predicates

section Proofs

open PersistentLocalState

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeKEMEpochSecret)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeKEMEpochSecret)]

/-- Port of `store_epoch_secret_proof`. -/
@[instance]
public
theorem storeEpochSecret.proof (me: Participant)
  (ty: EpochSecretType) (context: GroupContext Bytes) (confirmationTag: Bytes) (secret: Bytes):
  HoareTriple
    (storeEpochSecret me ty context confirmationTag secret)
    (fun tr =>
      IAmInGroupContext me context ∧
      GroupContext.mf.wf (Bytes.Publishable · tr) context ∧
      confirmationTag.Publishable tr ∧
      IsEpochSecret tr ty context secret ∧
      KeyIsAuthenticatedByConfirmationTag ty confirmationTag secret
    )
    (fun _ _ => True)
:= by
  unfold storeEpochSecret
  step by
    simp only [LocalStateInv.invariant]
    grind
  trivial

/-- Port of `get_epoch_secret_proof`. -/
@[instance]
public
theorem getEpochSecret.proof (me: Participant)
  (sid: Nat) (ty: EpochSecretType) (context: GroupContext Bytes) (confirmationTag: Bytes):
  HoareTriple
    (getEpochSecret me sid ty context confirmationTag)
    (fun _ => True)
    (fun secret tr =>
      IsEpochSecret tr ty context secret ∧
      KeyIsAuthenticatedByConfirmationTag ty confirmationTag secret
    )
:= by
  unfold getEpochSecret
  step
  step
  step
  step
  step
  simp only [LocalStateInv.invariant] at *
  grind

end Proofs

end MLS.TreeKEM
