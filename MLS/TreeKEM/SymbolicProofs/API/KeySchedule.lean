module

public import MLS.TreeKEM.SymbolicProofs.ConfirmationTag
public import MLS.TreeKEM.SymbolicProofs.KeySchedule

/-!
Port of `MLS.TreeKEM.Symbolic.API.KeySchedule`: the invariants of the key schedule states,
and the proofs that the functions of `MLS.TreeKEM.API.KeySchedule` establish them.

Port-specific differences:
- `compute_commit_secret_label` is `computeCommitSecretLabel`, in `MLS.TreeKEM.SymbolicProofs.KeySchedule`.
- Lemmas about functions returning a `Result` take the result and the success hypothesis
  (MLS*'s `match … with | Success … -> … | _ -> True`).
- MLS*'s `is_well_formed _ (is_publishable tr) group_context` is `GroupContext.mf.wf (Bytes.Publishable · tr) groupContext`.
- The namespace is MLS*'s module name `MLS.TreeKEM.Symbolic.API.KeySchedule`, as its names (`commit_proof`, …)
  are reused by other modules.
-/

namespace MLS.TreeKEM.Symbolic.API.KeySchedule

open Comparse
open DY
open MLS MLS.TreeSync MLS.Bootstrap MLS.TreeKEM MLS.TreeKEM.API.KeySchedule

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-! ## Invariants -/

/-- Port of `treekem_keyschedule_state_good`. -/
@[expose]
public
def TreekemKeyscheduleStateGood (tr: ProofTrace) (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes): Prop :=
  IsEpochSecret tr .senderDataSecret groupContext st.epochKeys.senderDataSecret ∧
  IsEpochSecret tr .exporterSecret groupContext st.epochKeys.exporterSecret ∧
  IsEpochSecret tr .externalSecret groupContext st.epochKeys.externalSecret ∧
  IsEpochSecret tr .membershipKey groupContext st.epochKeys.membershipKey ∧
  IsEpochSecret tr .resumptionPsk groupContext st.epochKeys.resumptionPsk ∧
  IsEpochSecret tr .epochAuthenticator groupContext st.epochKeys.epochAuthenticator ∧
  IsEpochSecret tr .initSecret groupContext st.initSecret ∧
  st.epochKeys.confirmationTag.Publishable tr

/--
Port of `treekem_keyschedule_state_label_good_aux`.
The last conjunct is useful to store the resumption PSK in the PSK store
(see MLS*'s comment: it cannot be put in `treekem_keyschedule_state_good`).
-/
@[expose]
public
def TreekemKeyscheduleStateLabelGoodAux (tr: ProofTrace) (epochSecretLabel: Label)
  (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes): Prop :=
  (epochSecretLabel.join (mkEpochSecretLabel .senderDataSecret groupContext)).canFlow (st.epochKeys.senderDataSecret.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .exporterSecret groupContext)).canFlow (st.epochKeys.exporterSecret.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .externalSecret groupContext)).canFlow (st.epochKeys.externalSecret.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .membershipKey groupContext)).canFlow (st.epochKeys.membershipKey.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .resumptionPsk groupContext)).canFlow (st.epochKeys.resumptionPsk.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .epochAuthenticator groupContext)).canFlow (st.epochKeys.epochAuthenticator.label tr) tr.erase ∧
  (epochSecretLabel.join (mkEpochSecretLabel .initSecret groupContext)).canFlow (st.initSecret.label tr) tr.erase ∧
  (st.epochKeys.resumptionPsk.label tr).canFlow (mkEpochSecretLabel .resumptionPsk groupContext) tr.erase

/-- Port of `compute_epoch_secret_label`. -/
@[expose]
public
def computeEpochSecretLabel (tr: ProofTrace) (initSecret: Bytes) (commitSecretLabel: Label)
  (joiners: List (KeyPackage Bytes tkt)) (psks: List (PreSharedKeyId Bytes × Bytes)): Label :=
  let initSecretLabel := initSecret.label tr
  let joinersLabel := (joiners.map keyPackageToInitLabel).foldr Label.join Label.secret
  let pskSecretLabel := psksLabel tr psks
  ((initSecretLabel.meet commitSecretLabel).join joinersLabel).meet pskSecretLabel

/-- Port of `treekem_keyschedule_state_label_good`. -/
@[expose]
public
def TreekemKeyscheduleStateLabelGood (tr: ProofTrace) (initSecret: Bytes) (commitSecretLabel: Label)
  (joiners: List (KeyPackage Bytes tkt)) (psks: List (PreSharedKeyId Bytes × Bytes))
  (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes): Prop :=
  TreekemKeyscheduleStateLabelGoodAux tr (computeEpochSecretLabel tr initSecret commitSecretLabel joiners psks) st groupContext

/-- Port of `treekem_keyschedule_state_label_good_later`. -/
public
theorem TreekemKeyscheduleStateLabelGood_later (tr1 tr2: ProofTrace)
  (initSecret: Bytes) (commitSecretLabel: Label) (joiners: List (KeyPackage Bytes tkt))
  (psks: List (PreSharedKeyId Bytes × Bytes)) (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes)
  (hinit: initSecret.Invariant tr1) (hpsks: PsksBytesInvariant tr1 psks)
  (hgood: TreekemKeyscheduleStateGood tr1 st groupContext):
  tr1 ≤ tr2 →
  TreekemKeyscheduleStateLabelGood tr1 initSecret commitSecretLabel joiners psks st groupContext →
  TreekemKeyscheduleStateLabelGood tr2 initSecret commitSecretLabel joiners psks st groupContext
:= by
  intro hle h
  unfold TreekemKeyscheduleStateLabelGood TreekemKeyscheduleStateLabelGoodAux computeEpochSecretLabel at *
  unfold TreekemKeyscheduleStateGood IsEpochSecret at hgood
  grind [Bytes.label_later_fast]

grind_pattern TreekemKeyscheduleStateLabelGood_later =>
  tr1 ≤ tr2,
  TreekemKeyscheduleStateLabelGood tr1 initSecret commitSecretLabel joiners psks st groupContext
grind_pattern [grind_later] TreekemKeyscheduleStateLabelGood_later =>
  tr1 ≤ tr2,
  TreekemKeyscheduleStateLabelGood tr1 initSecret commitSecretLabel joiners psks st groupContext

omit [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
/-- Port of `treekem_keyschedule_state_label_good_aux_can_flow`. -/
theorem TreekemKeyscheduleStateLabelGoodAux_canFlow (tr: ProofTrace) (epochLabel1 epochLabel2: Label)
  (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes)
  (h: TreekemKeyscheduleStateLabelGoodAux tr epochLabel1 st groupContext)
  (hflow: epochLabel2.canFlow epochLabel1 tr.erase):
  TreekemKeyscheduleStateLabelGoodAux tr epochLabel2 st groupContext
:= by
  unfold TreekemKeyscheduleStateLabelGoodAux at *
  grind [Label.canFlow]

/-- Port of `treekem_keyschedule_state_label_good_can_flow`. -/
public
theorem TreekemKeyscheduleStateLabelGood_canFlow (tr: ProofTrace)
  (initSecret: Bytes) (commitSecretLabel1 commitSecretLabel2: Label) (joiners: List (KeyPackage Bytes tkt))
  (psks: List (PreSharedKeyId Bytes × Bytes)) (st: TreeKEMKeyscheduleState Bytes) (groupContext: GroupContext Bytes)
  (h: TreekemKeyscheduleStateLabelGood tr initSecret commitSecretLabel1 joiners psks st groupContext)
  (hflow: commitSecretLabel2.canFlow commitSecretLabel1 tr.erase):
  TreekemKeyscheduleStateLabelGood tr initSecret commitSecretLabel2 joiners psks st groupContext
:= by
  apply TreekemKeyscheduleStateLabelGoodAux_canFlow tr _ _ st groupContext h
  grind [computeEpochSecretLabel, Label.canFlow]

/-! ## Proofs -/

omit [HasTreeKEMExecTrace]
  [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)] in
theorem GroupContext.wf_invariant_of_publishable (tr: ProofTrace) (groupContext: GroupContext Bytes)
  (h: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext):
  GroupContext.mf.wf (Bytes.Invariant · tr) groupContext
:=
  (pred_serializeNE_iff _ _ _).1 ((pred_serializeNE_iff _ (Bytes.Publishable · tr) _).2 h).1

variable [HasMlsKeyscheduleInvariants]

/-- Port of `create_from_epoch_secret_proof`. -/
public
theorem createFromEpochSecret_proof (tr: ProofTrace) (epochSecret: Bytes) (groupContext: GroupContext Bytes)
  (st: TreeKEMKeyscheduleState Bytes) (encryptionSecret: Bytes)
  (h: createFromEpochSecret epochSecret groupContext = .success (st, encryptionSecret))
  (hinv: epochSecret.Invariant tr) (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext)
  (husg: epochSecret.HasUsage (Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" (serializeNE GroupContext.mf groupContext)) tr):
  TreekemKeyscheduleStateGood tr st groupContext ∧
  TreekemKeyscheduleStateLabelGoodAux tr (epochSecret.label tr) st groupContext ∧
  TreekemKeyscheduleStateAuthWeak st epochSecret groupContext
:= by
  have hauth: TreekemKeyscheduleStateAuthWeak st epochSecret groupContext := by
    simp [TreekemKeyscheduleStateAuthWeak, h]
  simp only [createFromEpochSecret, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨senderDataSecret, h1, -, -, exporterSecret, h3, externalSecret, h4, confirmationKey, h5, confirmationTag, h6,
    membershipKey, h7, resumptionPsk, h8, epochAuthenticator, h9, initSecret, h10, rfl, -⟩ := h
  have := secretEpochToX_proof tr .senderDataSecret _ groupContext _ h1 hinv husg
  have := secretEpochToX_proof tr .exporterSecret _ groupContext _ h3 hinv husg
  have := secretEpochToX_proof tr .externalSecret _ groupContext _ h4 hinv husg
  have hconf := secretEpochToX_proof tr .confirmationKey _ groupContext _ h5 hinv husg
  have := secretEpochToX_proof tr .membershipKey _ groupContext _ h7 hinv husg
  have := secretEpochToX_proof tr .resumptionPsk _ groupContext _ h8 hinv husg
  have := secretEpochToX_proof tr .epochAuthenticator _ groupContext _ h9 hinv husg
  have := secretEpochToX_proof tr .initSecret _ groupContext _ h10 hinv husg
  simp only [GroupContext.mf.wf_eq] at hgc
  have := computeConfirmationTag_proof tr confirmationKey _ confirmationTag h6 hconf.1 hgc.2.2.1 ⟨groupContext, hconf.2.1⟩
  refine ⟨?_, ?_, hauth⟩ <;>
    simp only [TreekemKeyscheduleStateGood, TreekemKeyscheduleStateLabelGoodAux, IsEpochSecret, mkEpochSecretLabel] at * <;>
    grind [Label.canFlow]

/-- Port of `create_from_joiner_secret_proof`. -/
public
theorem createFromJoinerSecret_proof (tr: ProofTrace) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupContext: GroupContext Bytes) (st: TreeKEMKeyscheduleState Bytes) (encryptionSecret: Bytes)
  (h: createFromJoinerSecret joinerSecret psks groupContext = .success (st, encryptionSecret))
  (hjoiner: joinerSecret.Invariant tr) (hpsks: PsksBytesInvariant tr psks)
  (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext):
  TreekemKeyscheduleStateGood tr st groupContext ∧
  TreekemKeyscheduleStateAuthStrong st joinerSecret psks groupContext
:= by
  simp only [createFromJoinerSecret, Result.bind_eq_success] at h
  obtain ⟨epochSecret, h1, h2⟩ := h
  obtain ⟨hinv, husg, -⟩ := secretJoinerToEpoch_proof tr joinerSecret psks groupContext epochSecret h1 hjoiner hpsks
    (GroupContext.wf_invariant_of_publishable tr groupContext hgc)
  obtain ⟨hgood, -, -⟩ := createFromEpochSecret_proof tr epochSecret groupContext st encryptionSecret h2 hinv hgc husg
  refine ⟨hgood, ?_⟩
  simp [TreekemKeyscheduleStateAuthStrong, h1, h2]

/-- Port of `commit_proof`. `joiners` is the de-hash of the confirmed transcript hash. -/
public
theorem commit_proof (tr: ProofTrace) (st: TreeKEMKeyscheduleState Bytes) (optCommitSecret: Option Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)) (groupContext: GroupContext Bytes) (joiners: List (KeyPackage Bytes tkt))
  (newSt: TreeKEMKeyscheduleState Bytes) (encryptionSecret: Bytes) (welcomeSecrets: SecretsForWelcome Bytes)
  (h: commit st optCommitSecret psks groupContext = .success (newSt, encryptionSecret, welcomeSecrets))
  (hjoiners: TxHashContainsJoiners groupContext.confirmedTranscriptHash.val joiners)
  (hinit: st.initSecret.Invariant tr) (hcommit: ∀ commitSecret ∈ optCommitSecret, commitSecret.Invariant tr)
  (hpsks: PsksBytesInvariant tr psks) (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext):
  TreekemKeyscheduleStateGood tr newSt groupContext ∧
  TreekemKeyscheduleStateLabelGood tr st.initSecret (computeCommitSecretLabel tr optCommitSecret) joiners psks newSt groupContext ∧
  TreekemKeyscheduleStateAuthStrong newSt welcomeSecrets.joinerSecret psks groupContext ∧
  TreekemKeyscheduleStateAuthStrongExists newSt ∧
  welcomeSecrets.joinerSecret.KnowableBy ((joiners.map keyPackageToInitLabel).foldr Label.join Label.secret) tr
:= by
  simp only [commit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨joinerSecret, h1, epochSecret, h2, -, -, ⟨newSt', encryptionSecret'⟩, h3, rfl, -, rfl⟩ := h
  have hgcInv := GroupContext.wf_invariant_of_publishable tr groupContext hgc
  obtain ⟨hjInv, -, hjLabel⟩ := secretInitToJoiner_proof tr st.initSecret optCommitSecret groupContext joiners
    joinerSecret h1 hjoiners hinit hcommit hgcInv
  obtain ⟨heInv, heUsg, heLabel⟩ := secretJoinerToEpoch_proof tr joinerSecret psks groupContext epochSecret h2 hjInv
    hpsks hgcInv
  obtain ⟨hgood, hlabel, -⟩ := createFromEpochSecret_proof tr epochSecret groupContext newSt' encryptionSecret' h3 heInv
    hgc heUsg
  have hauth: TreekemKeyscheduleStateAuthStrong newSt' joinerSecret psks groupContext := by
    simp [TreekemKeyscheduleStateAuthStrong, h2, h3]
  refine ⟨hgood, ?_, hauth, ⟨_, _, _, hauth⟩, hjInv, ?_⟩
  · apply TreekemKeyscheduleStateLabelGoodAux_canFlow tr _ _ newSt' groupContext hlabel
    grind [computeEpochSecretLabel, Label.canFlow]
  · grind [Label.canFlow]

end MLS.TreeKEM.Symbolic.API.KeySchedule
