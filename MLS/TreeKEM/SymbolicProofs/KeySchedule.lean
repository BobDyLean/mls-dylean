module

public import MLS.TreeKEM.Code.KeySchedule
public import MLS.TreeDEM.Code.Message.Transcript
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeKEM.SymbolicProofs.PSK
public import MLS.TreeKEM.SymbolicProofs.State.EpochSecrets
public import MLS.TreeKEM.SymbolicProofs.State.OnePSKStore
public import MLS.Common.SymbolicProofs.Crypto.Derived.ExpandWithLabel
public import DySlop.Lib.Crypto.MAC.Split
import all MLS.TreeKEM.Code.KeySchedule

/-!
Port of `MLS.TreeKEM.Symbolic.KeySchedule`: the usages and labels of the key schedule,
and the proofs of the functions of `MLS.TreeKEM.KeySchedule`.

Port-specific differences:
- The witness of `commit_is_last_in_tx_hash` (MLS*'s `lbytes bytes (hash_output_length #bytes)` for the
  interim transcript hash) contains the length of the interim transcript hash as a conjunct.
- MLS*'s reductions to hash collisions with a `Pure` specification (`compute_confirmed_transcript_hash_inj`, …)
  are functions with a `_spec` theorem, returning the hash inputs (not `(empty, empty)`) when the inputs are equal;
  `proposalOrRefsRelInj` recurses on the tail when the head does not give a hash collision
  (instead of when the heads are equal).
- The local ExpandWithLabel usages and MAC predicates are `ExpandWithLabelUsage.Local` / `MacPred.Local`,
  and MLS*'s `has_mls_keyschedule_invariants` is the class `HasMlsKeyscheduleInvariants`,
  whose fields are scoped instances in `MLS.TreeKEM`.
- `expand_usage_confirmation_tag` is not used by MLS* (`compute_confirmation_tag` is a MAC): it is not ported.
- Lemmas about functions returning a `Result` take the result and the success hypothesis
  (MLS*'s `match … with | Success … -> … | _ -> True`); MLS*'s `match opt_commit_secret` in the label of the joiner secret
  is `computeCommitSecretLabel` (port of `compute_commit_secret_label` from `MLS.TreeKEM.Symbolic.API.KeySchedule`),
  the meet with a public label being equivalent to the other label.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open DySlop DySlop.KdfExpand DySlop.Mac
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap

/-! ## Joiners in the transcript hash -/

section TranscriptHash

variable {Bytes: Type} [CryptoBytes Bytes]

/-- Port of `commit_is_last_in_tx_hash_aux`. The witness contains the interim transcript hash and its length. -/
@[expose]
public
def CommitIsLastInTxHashAux (commit: Commit Bytes) (confirmedTranscriptHash: Bytes)
  (witness: ConfirmedTranscriptHashInput Bytes × Bytes): Prop :=
  computeConfirmedTranscriptHash witness.1 witness.2 = .success confirmedTranscriptHash ∧
  BytesLike.length witness.2 = CryptoBytes.hashOutputLength Bytes ∧
  witness.1.content.content = { contentType := .commit, content := commit }

/-- Port of `commit_is_last_in_tx_hash`. -/
@[expose]
public
def CommitIsLastInTxHash (commit: Commit Bytes) (confirmedTranscriptHash: Bytes): Prop :=
  ∃ witness, CommitIsLastInTxHashAux commit confirmedTranscriptHash witness

/-- Port of `proposal_or_ref_rel`. -/
@[expose]
public
def ProposalOrRefRel (por: ProposalOrRef Bytes) (p: Proposal Bytes): Prop :=
  match por with
  | .proposal p' => p = p'
  | .reference ref => makeProposalRef (serializeNE Proposal.mf p) = .success ref.val

/-- Port of `proposal_or_refs_rel`. -/
@[expose]
public
def ProposalOrRefsRel: List (ProposalOrRef Bytes) → List (Proposal Bytes) → Prop
  | [], [] => True
  | h1 :: t1, h2 :: t2 => ProposalOrRefRel h1 h2 ∧ ProposalOrRefsRel t1 t2
  | _, _ => False

/-- Port of `proposals_to_key_packages`. -/
@[expose]
public
def proposalsToKeyPackages: List (Proposal Bytes) → List (KeyPackage Bytes tkt)
  | [] => []
  | .add { keyPackage } :: t => keyPackage :: proposalsToKeyPackages t
  | _ :: t => proposalsToKeyPackages t

/-- Port of `tx_hash_contains_joiners_with_witness`. -/
public
def TxHashContainsJoinersWithWitness (confirmedTranscriptHash: Bytes) (joiners: List (KeyPackage Bytes tkt))
  (witness: Commit Bytes × List (Proposal Bytes)): Prop :=
  CommitIsLastInTxHash witness.1 confirmedTranscriptHash ∧
  ProposalOrRefsRel witness.1.proposals.val witness.2 ∧
  joiners = proposalsToKeyPackages witness.2

/-- Port of `tx_hash_contains_joiners`. -/
public
def TxHashContainsJoiners (confirmedTranscriptHash: Bytes) (joiners: List (KeyPackage Bytes tkt)): Prop :=
  ∃ witness, TxHashContainsJoinersWithWitness confirmedTranscriptHash joiners witness

/-- Port of `intro_tx_hash_contains_joiners`. -/
public
theorem TxHashContainsJoiners.intro (confirmedTranscriptHash: Bytes) (joiners: List (KeyPackage Bytes tkt))
  (commit: Commit Bytes) (proposals: List (Proposal Bytes))
  (hcommit: CommitIsLastInTxHash commit confirmedTranscriptHash)
  (hproposals: ProposalOrRefsRel commit.proposals.val proposals)
  (hjoiners: joiners = proposalsToKeyPackages proposals):
  TxHashContainsJoiners confirmedTranscriptHash joiners
:=
  ⟨(commit, proposals), hcommit, hproposals, hjoiners⟩

/-- Port of `compute_confirmed_transcript_hash_inj`. -/
public
def computeConfirmedTranscriptHashInj (txHashInput1: ConfirmedTranscriptHashInput Bytes) (interimTranscriptHash1: Bytes)
  (txHashInput2: ConfirmedTranscriptHashInput Bytes) (interimTranscriptHash2: Bytes): Bytes × Bytes :=
  (BytesLike.concat interimTranscriptHash1 (serializeNE ConfirmedTranscriptHashInput.mf txHashInput1),
    BytesLike.concat interimTranscriptHash2 (serializeNE ConfirmedTranscriptHashInput.mf txHashInput2))

public
theorem computeConfirmedTranscriptHash_eq_success (txHashInput: ConfirmedTranscriptHashInput Bytes)
  (interimTranscriptHash res: Bytes):
  computeConfirmedTranscriptHash txHashInput interimTranscriptHash = .success res ↔
    txHashInput.content.content.contentType = .commit ∧
    CryptoBytes.hashHash (BytesLike.concat interimTranscriptHash (serializeNE ConfirmedTranscriptHashInput.mf txHashInput)) =
      .success res
:= by
  unfold computeConfirmedTranscriptHash
  split <;> simp_all [Result.internalFailure]

/-- Specification of `computeConfirmedTranscriptHashInj` (MLS*'s postcondition of `compute_confirmed_transcript_hash_inj`). -/
public
theorem computeConfirmedTranscriptHashInj_spec (txHashInput1: ConfirmedTranscriptHashInput Bytes) (interimTranscriptHash1: Bytes)
  (txHashInput2: ConfirmedTranscriptHashInput Bytes) (interimTranscriptHash2: Bytes) (res: Bytes)
  (h1: computeConfirmedTranscriptHash txHashInput1 interimTranscriptHash1 = .success res)
  (h2: computeConfirmedTranscriptHash txHashInput2 interimTranscriptHash2 = .success res)
  (hlen1: BytesLike.length interimTranscriptHash1 = CryptoBytes.hashOutputLength Bytes)
  (hlen2: BytesLike.length interimTranscriptHash2 = CryptoBytes.hashOutputLength Bytes):
  (txHashInput1 = txHashInput2 ∧ interimTranscriptHash1 = interimTranscriptHash2) ∨
  isHashCollision (computeConfirmedTranscriptHashInj txHashInput1 interimTranscriptHash1 txHashInput2 interimTranscriptHash2)
:= by
  grind [computeConfirmedTranscriptHash_eq_success, computeConfirmedTranscriptHashInj, isHashCollision, concat_inj]

/-- Port of `commit_is_last_in_tx_hash_aux_lemma`. -/
public
def commitIsLastInTxHashAuxInj (witness1 witness2: ConfirmedTranscriptHashInput Bytes × Bytes): Bytes × Bytes :=
  computeConfirmedTranscriptHashInj witness1.1 witness1.2 witness2.1 witness2.2

/-- Specification of `commitIsLastInTxHashAuxInj` (MLS*'s postcondition of `commit_is_last_in_tx_hash_aux_lemma`). -/
public
theorem commitIsLastInTxHashAuxInj_spec (commit1 commit2: Commit Bytes) (confirmedTranscriptHash: Bytes)
  (witness1 witness2: ConfirmedTranscriptHashInput Bytes × Bytes)
  (h1: CommitIsLastInTxHashAux commit1 confirmedTranscriptHash witness1)
  (h2: CommitIsLastInTxHashAux commit2 confirmedTranscriptHash witness2):
  commit1 = commit2 ∨ isHashCollision (commitIsLastInTxHashAuxInj witness1 witness2)
:= by
  grind [CommitIsLastInTxHashAux, commitIsLastInTxHashAuxInj, computeConfirmedTranscriptHashInj_spec]

/-- Port of `proposal_or_ref_rel_lemma`. -/
public
def proposalOrRefRelInj (por: ProposalOrRef Bytes) (p1 p2: Proposal Bytes): Bytes × Bytes :=
  match por with
  | .proposal _ => (BytesLike.empty, BytesLike.empty)
  | .reference _ => makeProposalRefInj (serializeNE Proposal.mf p1) (serializeNE Proposal.mf p2)

/-- Specification of `proposalOrRefRelInj` (MLS*'s postcondition of `proposal_or_ref_rel_lemma`). -/
public
theorem proposalOrRefRelInj_spec (por: ProposalOrRef Bytes) (p1 p2: Proposal Bytes)
  (h1: ProposalOrRefRel por p1) (h2: ProposalOrRefRel por p2):
  p1 = p2 ∨ isHashCollision (proposalOrRefRelInj por p1 p2)
:= by
  cases por <;> grind [ProposalOrRefRel, proposalOrRefRelInj, makeProposalRefInj_spec]

/-- Port of `proposal_or_refs_rel_lemma`. -/
public
def proposalOrRefsRelInj: List (ProposalOrRef Bytes) → List (Proposal Bytes) → List (Proposal Bytes) → Bytes × Bytes
  | hpor :: tpor, h1 :: t1, h2 :: t2 =>
    if isHashCollision (proposalOrRefRelInj hpor h1 h2) then
      proposalOrRefRelInj hpor h1 h2
    else
      proposalOrRefsRelInj tpor t1 t2
  | _, _, _ => (BytesLike.empty, BytesLike.empty)

/-- Specification of `proposalOrRefsRelInj` (MLS*'s postcondition of `proposal_or_refs_rel_lemma`). -/
public
theorem proposalOrRefsRelInj_spec (pors: List (ProposalOrRef Bytes)) (ps1 ps2: List (Proposal Bytes))
  (h1: ProposalOrRefsRel pors ps1) (h2: ProposalOrRefsRel pors ps2):
  ps1 = ps2 ∨ isHashCollision (proposalOrRefsRelInj pors ps1 ps2)
:= by
  induction pors generalizing ps1 ps2 <;> cases ps1 <;> cases ps2 <;>
    grind [ProposalOrRefsRel, proposalOrRefsRelInj, proposalOrRefRelInj_spec]

end TranscriptHash

section TranscriptHashSymbolic

variable [HasSymbolicBytes]

/-- Port of `commit_is_last_in_tx_hash_inj_lemma`. -/
public
theorem CommitIsLastInTxHash.inj (commit1 commit2: Commit Bytes) (confirmedTranscriptHash: Bytes)
  (h1: CommitIsLastInTxHash commit1 confirmedTranscriptHash) (h2: CommitIsLastInTxHash commit2 confirmedTranscriptHash):
  commit1 = commit2
:= by
  obtain ⟨w1, h1⟩ := h1
  obtain ⟨w2, h2⟩ := h2
  have := not_isHashCollision (commitIsLastInTxHashAuxInj w1 w2)
  grind [commitIsLastInTxHashAuxInj_spec]

/-- On symbolic bytes, the proposals of a list of proposals or references are unique. -/
theorem ProposalOrRefsRel.inj (pors: List (ProposalOrRef Bytes)) (ps1 ps2: List (Proposal Bytes))
  (h1: ProposalOrRefsRel pors ps1) (h2: ProposalOrRefsRel pors ps2):
  ps1 = ps2
:= by
  have := not_isHashCollision (proposalOrRefsRelInj pors ps1 ps2)
  grind [proposalOrRefsRelInj_spec]

end TranscriptHashSymbolic

/-! ## Labels -/

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `confirmed_transcript_hash_to_init_label_aux`. -/
public
def confirmedTranscriptHashToInitLabelAux (confirmedTranscriptHash: Bytes)
  (witness: Commit Bytes × List (Proposal Bytes)): Label :=
  (Label.ofProp (
    CommitIsLastInTxHash witness.1 confirmedTranscriptHash ∧
    ProposalOrRefsRel witness.1.proposals.val witness.2
  )).meet
    (((proposalsToKeyPackages witness.2).map keyPackageToInitLabel).foldr Label.join Label.secret)

/-- Port of `confirmed_transcript_hash_to_init_label`. -/
public
def confirmedTranscriptHashToInitLabel (confirmedTranscriptHash: Bytes): Label :=
  Label.bigJoin (confirmedTranscriptHashToInitLabelAux confirmedTranscriptHash)

/-- Port of `confirmed_transcript_hash_to_init_label_eq`. -/
public
theorem confirmedTranscriptHashToInitLabel_eq (confirmedTranscriptHash: Bytes) (joiners: List (KeyPackage Bytes tkt))
  (h: TxHashContainsJoiners confirmedTranscriptHash joiners):
  confirmedTranscriptHashToInitLabel confirmedTranscriptHash = (joiners.map keyPackageToInitLabel).foldr Label.join Label.secret
:= by
  obtain ⟨⟨commit, proposals⟩, hcommit, hproposals, rfl⟩ := h
  ext tr
  simp only [confirmedTranscriptHashToInitLabel, Label.bigJoin_isCorrupt, confirmedTranscriptHashToInitLabelAux,
    Label.meetIsCorrupt, Label.ofProp_isCorrupt]
  constructor
  · grind [CommitIsLastInTxHash.inj, ProposalOrRefsRel.inj]
  · intro
    refine ⟨(commit, proposals), ?_⟩
    grind

/-- Port of `mk_resumption_psk_label`. -/
@[expose]
public
def mkResumptionPskLabel (me: Participant) (groupContext: GroupContext Bytes): Label :=
  pskLabel me (.resumptionPsk groupContext.groupId groupContext.epoch)

/-- Port of `mk_epoch_secret_label`. -/
@[expose]
public
def mkEpochSecretLabel (ty: EpochSecretType) (groupContext: GroupContext Bytes): Label :=
  let baseEpochSecretLabel := mkGroupSecretLabel (mkPrincipalEpochSecretLabel ty) groupContext
  match ty with
  | .resumptionPsk => baseEpochSecretLabel.join (mkGroupSecretLabel mkResumptionPskLabel groupContext)
  | _ => baseEpochSecretLabel

end Labels

/-! ## Usages -/

section Usages

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `expand_usage_extractedkey_joiner`. -/
public
def expandUsageExtractedkeyJoiner: ExpandWithLabelUsage.Local ["joiner"] :=
  .single {
    getUsage _ _ _ := Usage.kdfExpandKey "MLS.TreeKEM.JoinerSecret" BytesLike.empty
    getLabel _ prkLabel context _ :=
      match GroupContext.mf.toExtensible.parse context with
      | some groupContext => prkLabel.join (confirmedTranscriptHashToInitLabel groupContext.confirmedTranscriptHash.val)
      | none => Label.pub
    getLabel_lemma tr _ prkLabel context _ _ := by
      split <;> grind
  }

/-- Port of `expand_usage_extractedkey_epoch`. -/
public
def expandUsageExtractedkeyEpoch: ExpandWithLabelUsage.Local ["epoch"] :=
  .single {
    getUsage _ context _ := Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" context
    getLabel _ prkLabel _ _ := prkLabel
    getLabel_lemma := by grind
  }

/-- The group context of the usage data of a secret (MLS*'s `let KdfExpandKey _ data = prk_usage in parse … data`). -/
public
def usageGroupContext (usg: Usage): Option (GroupContext Bytes) :=
  usg.data.bind GroupContext.mf.toExtensible.parse

/-- Port of `mk_epoch_expandwithlabel_usage`. -/
public
def mkEpochExpandwithlabelUsage (ty: EpochSecretType): ExpandWithLabelUsage where
  getUsage prkUsage _ _ :=
    match usageGroupContext prkUsage with
    | some groupContext => mkEpochSecretUsage ty groupContext
    | none => Usage.nothing
  getLabel prkUsage prkLabel _ _ :=
    match usageGroupContext prkUsage with
    | some groupContext => prkLabel.join (mkEpochSecretLabel ty groupContext)
    | none => Label.pub
  getLabel_lemma tr prkUsage prkLabel _ _ _ := by
    split <;> grind

/-- Port of `expand_usage_extractedkey_welcome`. -/
public
def expandUsageExtractedkeyWelcome: ExpandWithLabelUsage.Local ["welcome"] :=
  .single (.secret (Usage.kdfExpandKey "MLS.Bootstrap.WelcomeSecret" BytesLike.empty))

/-- Port of `expand_usage_epoch_senderdata`. -/
public
def expandUsageEpochSenderdata: ExpandWithLabelUsage.Local ["sender data"] :=
  .single (mkEpochExpandwithlabelUsage .senderDataSecret)

/-- Port of `expand_usage_epoch_encryption`. -/
public
def expandUsageEpochEncryption: ExpandWithLabelUsage.Local ["encryption"] :=
  .single (mkEpochExpandwithlabelUsage .encryptionSecret)

/-- Port of `expand_usage_epoch_exporter`. -/
public
def expandUsageEpochExporter: ExpandWithLabelUsage.Local ["exporter"] :=
  .single (mkEpochExpandwithlabelUsage .exporterSecret)

/-- Port of `expand_usage_epoch_external`. -/
public
def expandUsageEpochExternal: ExpandWithLabelUsage.Local ["external"] :=
  .single (mkEpochExpandwithlabelUsage .externalSecret)

/-- Port of `expand_usage_epoch_confirmation`. -/
public
def expandUsageEpochConfirmation: ExpandWithLabelUsage.Local ["confirm"] :=
  .single (mkEpochExpandwithlabelUsage .confirmationKey)

/-- Port of `expand_usage_epoch_membership`. -/
public
def expandUsageEpochMembership: ExpandWithLabelUsage.Local ["membership"] :=
  .single (mkEpochExpandwithlabelUsage .membershipKey)

/-- Port of `expand_usage_epoch_resumption`. -/
public
def expandUsageEpochResumption: ExpandWithLabelUsage.Local ["resumption"] :=
  .single (mkEpochExpandwithlabelUsage .resumptionPsk)

/-- Port of `expand_usage_epoch_authentication`. -/
public
def expandUsageEpochAuthentication: ExpandWithLabelUsage.Local ["authentication"] :=
  .single (mkEpochExpandwithlabelUsage .epochAuthenticator)

/-- Port of `expand_usage_epoch_init`. -/
public
def expandUsageEpochInit: ExpandWithLabelUsage.Local ["init"] :=
  .single (mkEpochExpandwithlabelUsage .initSecret)

/-- Port of `expand_usage_confirmation_tag`. -/
public
def expandUsageConfirmationTag: KdfExpandUsage.Local ["MLS.TreeKEM.ConfirmationKey"] :=
  .single {
    getUsage _ _ := Usage.nothing
    getLabel _ _ _ := Label.pub
    getLabel_lemma tr _ prkLabel _ _ := Label.pubCanFlow prkLabel tr
  }

end Usages

section MacPredicate

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `confirmation_mac_pred`. -/
public
def confirmationMacPred: MacPred.Local ["MLS.TreeKEM.ConfirmationKey"] :=
  .single { pred _ _ _ _ := True }

/-- Port of the `pred_later` field of `confirmation_mac_pred`. -/
public
theorem confirmationMacPredProof [BytesInvariants]: MacPred.LocalProof confirmationMacPred :=
  MacPred.LocalProof.single fun _ _ _ _ _ _ _ _ _ => trivial

end MacPredicate

section Invariants

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/--
Port of `has_mls_keyschedule_invariants`.
The fields are scoped instances in the namespace `MLS.TreeKEM`; the top-level protocol provides them
(`instance: HasMlsKeyscheduleInvariants where`).
-/
public
class HasMlsKeyscheduleInvariants: Prop where
  [joiner: ExpandWithLabelUsage.Has "KDF.ExtractedKey" expandUsageExtractedkeyJoiner]
  [welcome: ExpandWithLabelUsage.Has "KDF.ExtractedKey" expandUsageExtractedkeyWelcome]
  [epoch: ExpandWithLabelUsage.Has "KDF.ExtractedKey" expandUsageExtractedkeyEpoch]
  [epochSenderdata: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochSenderdata]
  [epochEncryption: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochEncryption]
  [epochExporter: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochExporter]
  [epochExternal: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochExternal]
  [epochConfirmation: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochConfirmation]
  [epochMembership: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochMembership]
  [epochResumption: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochResumption]
  [epochAuthentication: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochAuthentication]
  [epochInit: ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" expandUsageEpochInit]
  [confirmation: MacPred.Has confirmationMacPred]
  [psk: HasMlsPskInvariants]

attribute [scoped instance] HasMlsKeyscheduleInvariants.joiner
attribute [scoped instance] HasMlsKeyscheduleInvariants.welcome
attribute [scoped instance] HasMlsKeyscheduleInvariants.epoch
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochSenderdata
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochEncryption
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochExporter
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochExternal
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochConfirmation
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochMembership
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochResumption
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochAuthentication
attribute [scoped instance] HasMlsKeyscheduleInvariants.epochInit
attribute [scoped instance] HasMlsKeyscheduleInvariants.confirmation
attribute [scoped instance] HasMlsKeyscheduleInvariants.psk

end Invariants

/-! ## Secrets of an epoch -/

section EpochSecrets

variable {Bytes: Type} [CryptoBytes Bytes]

/--
Port of `secret_epoch_to_X`.
The proof is the same for all these functions, this helper allows to factorize the proof.
-/
@[expose]
public
def secretEpochToX (ty: EpochSecretType): Bytes → Result Bytes :=
  match ty with
  | .initSecret => secretEpochToInit
  | .senderDataSecret => secretEpochToSenderData
  | .encryptionSecret => secretEpochToEncryption
  | .exporterSecret => secretEpochToExporter
  | .externalSecret => secretEpochToExternal
  | .confirmationKey => secretEpochToConfirmation
  | .membershipKey => secretEpochToMembership
  | .resumptionPsk => secretEpochToResumption
  | .epochAuthenticator => secretEpochToAuthentication

/-- Port of `secret_epoch_to_X_string`. -/
public
def secretEpochToXString (ty: EpochSecretType): String :=
  match ty with
  | .initSecret => "init"
  | .senderDataSecret => "sender data"
  | .encryptionSecret => "encryption"
  | .exporterSecret => "exporter"
  | .externalSecret => "external"
  | .confirmationKey => "confirm"
  | .membershipKey => "membership"
  | .resumptionPsk => "resumption"
  | .epochAuthenticator => "authentication"

theorem secretEpochToX_eq (ty: EpochSecretType) (epochSecret: Bytes):
  secretEpochToX ty epochSecret = deriveSecret epochSecret (secretEpochToXString ty)
:= by
  cases ty <;> rfl

end EpochSecrets

/-! ## Proofs -/

section Code

variable [HasSymbolicBytes]

theorem secretInitToJoiner_eq_success (initSecret: Bytes) (optCommitSecret: Option Bytes)
  (groupContext: GroupContext Bytes) (joinerSecret: Bytes)
  (h: secretInitToJoiner initSecret optCommitSecret groupContext = .success joinerSecret):
  expandWithLabel (DySlop.KdfExtract.kdfExtract initSecret (optCommitSecret.getD zeroVector)) "joiner"
    (serializeNE GroupContext.mf groupContext) (CryptoBytes.kdfLength Bytes) = .success joinerSecret
:= by
  cases optCommitSecret <;> simpa [secretInitToJoiner] using h

theorem secretJoinerToWelcome_eq_success (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (welcomeSecret: Bytes)
  (h: secretJoinerToWelcome joinerSecret psks = .success welcomeSecret):
  ∃ pskSecret, computePskSecret psks = .success pskSecret ∧
    expandWithLabel (DySlop.KdfExtract.kdfExtract joinerSecret pskSecret) "welcome" BytesLike.empty
      (CryptoBytes.kdfLength Bytes) = .success welcomeSecret
:= by
  simpa [secretJoinerToWelcome, secretJoinerToWelcomeInternal, deriveSecret] using h

theorem usageGroupContext_kdfExpandKey (tag: String) (groupContext: GroupContext Bytes):
  usageGroupContext (Usage.kdfExpandKey tag (serializeNE GroupContext.mf groupContext)) = some groupContext
:= by
  have := ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv GroupContext.mf.toExtensible groupContext
  simp [usageGroupContext, Usage.kdfExpandKey, serializeNE, this]

end Code

section Proofs

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `compute_commit_secret_label` (from `MLS.TreeKEM.Symbolic.API.KeySchedule`). -/
@[expose]
public
def computeCommitSecretLabel (tr: ProofTrace) (optCommitSecret: Option Bytes): Label :=
  match optCommitSecret with
  | none => Label.pub
  | some commitSecret => commitSecret.label tr

variable [HasMlsKeyscheduleInvariants]

/--
Port of `secret_init_to_joiner_proof`.
MLS*'s `match opt_commit_secret` in the label of the joiner secret is `computeCommitSecretLabel`
(when there is no commit secret, the meet with `Label.pub` is equivalent to the label of the init secret).
-/
public
theorem secretInitToJoiner_proof (tr: ProofTrace) (initSecret: Bytes) (optCommitSecret: Option Bytes)
  (groupContext: GroupContext Bytes) (joiners: List (KeyPackage Bytes tkt)) (joinerSecret: Bytes)
  (h: secretInitToJoiner initSecret optCommitSecret groupContext = .success joinerSecret)
  (hjoiners: TxHashContainsJoiners groupContext.confirmedTranscriptHash.val joiners)
  (hinit: initSecret.Invariant tr) (hcommit: ∀ commitSecret ∈ optCommitSecret, commitSecret.Invariant tr)
  (hgc: GroupContext.mf.wf (Bytes.Invariant · tr) groupContext):
  joinerSecret.Invariant tr ∧
  joinerSecret.HasUsage (Usage.kdfExpandKey "MLS.TreeKEM.JoinerSecret" BytesLike.empty) tr ∧
  (joinerSecret.label tr).equivalent
    (((initSecret.label tr).meet (computeCommitSecretLabel tr optCommitSecret)).join
      ((joiners.map keyPackageToInitLabel).foldr Label.join Label.secret)) tr.erase
:= by
  have hcs: (optCommitSecret.getD zeroVector).Invariant tr ∧
      ((optCommitSecret.getD zeroVector).label tr).equivalent (computeCommitSecretLabel tr optCommitSecret) tr.erase := by
    have := zeroVector_label tr
    have := zeroVector_publishable tr
    cases optCommitSecret <;> simp only [Option.getD, computeCommitSecretLabel] <;> grind [Bytes.Publishable]
  have hctx := (pred_serializeNE_iff GroupContext.mf (Bytes.Invariant · tr) groupContext).2 hgc
  obtain ⟨hinv, husg, hlab⟩ := expandWithLabel.Invariant expandUsageExtractedkeyJoiner "KDF.ExtractedKey" tr _
    DySlop.KdfExtract.extractedKeyUsage "joiner" _ _ joinerSecret (secretInitToJoiner_eq_success _ _ _ _ h)
    (by simp [hinit, hcs.1]) hctx (DySlop.KdfExtract.kdfExtract.HasUsage _ _ tr) rfl rfl (by simp)
  have hparse := ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv GroupContext.mf.toExtensible groupContext
  simp only [expandUsageExtractedkeyJoiner, ExpandWithLabelUsage.Local.getUsage_single,
    ExpandWithLabelUsage.Local.getLabel_single, serializeNE, hparse, DySlop.KdfExtract.kdfExtract.label,
    confirmedTranscriptHashToInitLabel_eq _ _ hjoiners] at husg hlab
  grind [Label.canFlow]

/-- Port of `secret_joiner_to_welcome_proof`. -/
public
theorem secretJoinerToWelcome_proof (tr: ProofTrace) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (welcomeSecret: Bytes)
  (h: secretJoinerToWelcome joinerSecret psks = .success welcomeSecret)
  (hjoiner: joinerSecret.Invariant tr) (hpsks: PsksBytesInvariant tr psks):
  welcomeSecret.Invariant tr ∧
  welcomeSecret.HasUsage (Usage.kdfExpandKey "MLS.Bootstrap.WelcomeSecret" BytesLike.empty) tr ∧
  (welcomeSecret.label tr).equivalent ((joinerSecret.label tr).meet (psksLabel tr psks)) tr.erase
:= by
  obtain ⟨pskSecret, hpsk, hexp⟩ := secretJoinerToWelcome_eq_success _ _ _ h
  obtain ⟨hpskInv, hpskLabel⟩ := computePskSecret_proof tr psks pskSecret hpsk hpsks
  obtain ⟨hinv, husg, hlab⟩ := expandWithLabel.Invariant expandUsageExtractedkeyWelcome "KDF.ExtractedKey" tr _
    DySlop.KdfExtract.extractedKeyUsage "welcome" _ _ welcomeSecret hexp (by simp [hjoiner, hpskInv])
    (BytesCompatiblePred.pred_empty (pred := (Bytes.Invariant · tr))) (DySlop.KdfExtract.kdfExtract.HasUsage _ _ tr)
    rfl rfl (by simp)
  simp only [expandUsageExtractedkeyWelcome, ExpandWithLabelUsage.Local.getUsage_single,
    ExpandWithLabelUsage.Local.getLabel_single, ExpandWithLabelUsage.secret, DySlop.KdfExtract.kdfExtract.label] at husg hlab
  grind [Label.canFlow]

/-- Port of `secret_joiner_to_epoch_proof`. -/
public
theorem secretJoinerToEpoch_proof (tr: ProofTrace) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupContext: GroupContext Bytes) (epochSecret: Bytes)
  (h: secretJoinerToEpoch joinerSecret psks groupContext = .success epochSecret)
  (hjoiner: joinerSecret.Invariant tr) (hpsks: PsksBytesInvariant tr psks)
  (hgc: GroupContext.mf.wf (Bytes.Invariant · tr) groupContext):
  epochSecret.Invariant tr ∧
  epochSecret.HasUsage (Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" (serializeNE GroupContext.mf groupContext)) tr ∧
  (epochSecret.label tr).equivalent ((joinerSecret.label tr).meet (psksLabel tr psks)) tr.erase
:= by
  obtain ⟨pskSecret, hpsk, hexp⟩ := secretJoinerToEpoch_eq_success _ _ _ _ h
  obtain ⟨hpskInv, hpskLabel⟩ := computePskSecret_proof tr psks pskSecret hpsk hpsks
  have hctx := (pred_serializeNE_iff GroupContext.mf (Bytes.Invariant · tr) groupContext).2 hgc
  obtain ⟨hinv, husg, hlab⟩ := expandWithLabel.Invariant expandUsageExtractedkeyEpoch "KDF.ExtractedKey" tr _
    DySlop.KdfExtract.extractedKeyUsage "epoch" _ _ epochSecret hexp (by simp [hjoiner, hpskInv]) hctx
    (DySlop.KdfExtract.kdfExtract.HasUsage _ _ tr) rfl rfl (by simp)
  simp only [expandUsageExtractedkeyEpoch, ExpandWithLabelUsage.Local.getUsage_single,
    ExpandWithLabelUsage.Local.getLabel_single, DySlop.KdfExtract.kdfExtract.label] at husg hlab
  grind [Label.canFlow]

omit [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
  [HasMlsKeyscheduleInvariants] in
/-- `secretEpochToX_proof` for a local ExpandWithLabel usage built by `mkEpochExpandwithlabelUsage`. -/
theorem secretEpochToX_proof_aux (tr: ProofTrace) (label: String) (l: ExpandWithLabelUsage.Local [label])
  [ExpandWithLabelUsage.Has "MLS.TreeKEM.EpochSecret" l] (ty: EpochSecretType)
  (hl: l = .single (mkEpochExpandwithlabelUsage ty))
  (epochSecret: Bytes) (groupContext: GroupContext Bytes) (xSecret: Bytes)
  (h: expandWithLabel epochSecret label BytesLike.empty (CryptoBytes.kdfLength Bytes) = .success xSecret)
  (hinv: epochSecret.Invariant tr)
  (husg: epochSecret.HasUsage (Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" (serializeNE GroupContext.mf groupContext)) tr):
  xSecret.Invariant tr ∧
  xSecret.HasUsage (mkEpochSecretUsage ty groupContext) tr ∧
  (xSecret.label tr).equivalent ((epochSecret.label tr).join (mkEpochSecretLabel ty groupContext)) tr.erase
:= by
  have := expandWithLabel.Invariant l "MLS.TreeKEM.EpochSecret" tr epochSecret _ label _ _ xSecret h hinv
    (BytesCompatiblePred.pred_empty (pred := (Bytes.Invariant · tr))) husg rfl rfl (by simp)
  subst hl
  simpa [ExpandWithLabelUsage.Local.getUsage_single, ExpandWithLabelUsage.Local.getLabel_single,
    mkEpochExpandwithlabelUsage, usageGroupContext_kdfExpandKey] using this

/-- Port of `secret_epoch_to_X_proof`. -/
public
theorem secretEpochToX_proof (tr: ProofTrace) (ty: EpochSecretType) (epochSecret: Bytes)
  (groupContext: GroupContext Bytes) (xSecret: Bytes)
  (h: secretEpochToX ty epochSecret = .success xSecret)
  (hinv: epochSecret.Invariant tr)
  (husg: epochSecret.HasUsage (Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" (serializeNE GroupContext.mf groupContext)) tr):
  xSecret.Invariant tr ∧
  xSecret.HasUsage (mkEpochSecretUsage ty groupContext) tr ∧
  (xSecret.label tr).equivalent ((epochSecret.label tr).join (mkEpochSecretLabel ty groupContext)) tr.erase
:= by
  rw [secretEpochToX_eq] at h
  cases ty
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochInit _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochSenderdata _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochEncryption _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochExporter _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochExternal _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochConfirmation _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochMembership _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochResumption _ rfl _ _ _ h hinv husg
  · exact secretEpochToX_proof_aux tr _ expandUsageEpochAuthentication _ rfl _ _ _ h hinv husg

/-- Port of `compute_confirmation_tag_proof`. -/
public
theorem computeConfirmationTag_proof (tr: ProofTrace) (confirmationKey confirmedTranscriptHash: Bytes)
  (confirmationTag: Bytes)
  (h: computeConfirmationTag confirmationKey confirmedTranscriptHash = .success confirmationTag)
  (hkey: confirmationKey.Invariant tr) (hcth: confirmedTranscriptHash.Publishable tr)
  (husg: ∃ groupContext, confirmationKey.HasUsage (mkEpochSecretUsage .confirmationKey groupContext) tr):
  confirmationTag.Publishable tr
:= by
  simp only [computeConfirmationTag, cryptoBytesBytes_hmacHmac, Result.success.injEq] at h
  subst h
  obtain ⟨groupContext, husg⟩ := husg
  have hmac: (mkEpochSecretUsage .confirmationKey groupContext).type = "MacKey" ∧
      (mkEpochSecretUsage .confirmationKey groupContext).tag = "MLS.TreeKEM.ConfirmationKey" := by
    simp [mkEpochSecretUsage, Usage.macKey]
  have hpred := MacPred.Has.pred_eq (l := confirmationMacPred) _ confirmationKey confirmedTranscriptHash tr hmac.1
    (by simp [hmac.2])
  rw [confirmationMacPred, MacPred.Local.pred_single _ _ _ _ _ hmac.1 hmac.2] at hpred
  have := DySlop.Mac.macCompute.Invariant _ _ confirmedTranscriptHash tr hkey hcth.1 husg
  grind [DySlop.Mac.macCompute.label]

end Proofs

end MLS.TreeKEM
