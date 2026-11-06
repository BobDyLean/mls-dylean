module

public import MLS.Bootstrap.Code.Welcome
public import MLS.TreeKEM.SymbolicSpec.EpochEvent
public import MLS.TreeKEM.SymbolicProofs.ConfirmationTag
public import MLS.TreeSync.SymbolicProofs.LeafNodeSignature
public import MLS.TreeSync.Proofs.Invariants.AuthService
public import MLS.TreeSync.Proofs.TreeHash
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.Bootstrap.Code.Welcome

/-!
Port of `MLS.Bootstrap.Symbolic.GroupInfo`: the signature predicate of group infos,
and the proofs of their signature and verification.

Port-specific differences:
- The events of the predicate are on the erased trace (`tr.erase`), as in DyLean's examples;
  the principal of the inviter's event is its field `prin`.
- MLS*'s `has_group_info_tbs_invariant` is `SignWithLabelPred.Has groupInfoSignPred`.
- MLS*'s `ProcessedCommit? inviter_ev.how /\ joiners_are_stale_participants …` is a `match` on `inviterEv.how`
  (as `MLS.TreeKEM.HasSameEventAsMe`).
- MLS*'s `get_signer_verification_key_proof` uses `Some?.v (leaf_at tree inviter)` and
  `Some?.v (credential_to_principal …)`: the lemma concludes with their existence.
  MLS* requires the tree and the tokens to be at position `0` (`treesync bytes tkt l 0`);
  here, they have the same position (`hpos`).
- Lemmas about functions returning a `Result` take the result and the success hypothesis
  (MLS*'s `match … with | Success … -> … | _ -> True`).
- DY*'s `is_corrupt tr (signature_key_label …)` is `(signatureKeyLabel …).isCorrupt tr.erase`.
-/

namespace MLS.Bootstrap

open Comparse
open DY
open DySlop DySlop.Signature
open MLS MLS.TreeSync MLS.TreeKEM

/-! ## Signature invariant -/

/-- Port of `group_info_label`. -/
public
def groupInfoLabel: String := "GroupInfoTBS"

section Predicates

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]

/-- Port of `group_info_sign_pred_aux_with_witness`. -/
@[expose]
public
def GroupInfoSignPredAuxWithWitness (groupContext: GroupContext Bytes) (confirmationTag: Bytes)
  (inviterEv: IAmInGroup) (joinerSecret: Bytes): Prop :=
  inviterEv.groupContext = groupContext ∧
  confirmationTag = inviterEv.epochKeys.epochKeys.confirmationTag ∧
  TreekemKeyscheduleStateAuthStrong inviterEv.epochKeys joinerSecret inviterEv.psks groupContext ∧
  TreeHasHash inviterEv.tree groupContext.treeHash.val ∧
  match inviterEv.how with
  | .processedCommit x => JoinersAreStaleParticipants inviterEv.tree x.joiners
  | _ => False

/-- Port of `group_info_sign_pred_aux`. -/
@[expose]
public
def GroupInfoSignPredAux (tr: ExecTrace) (inviterId: Participant) (groupContext: GroupContext Bytes)
  (confirmationTag: Bytes): Prop :=
  ∃ inviterEv joinerSecret,
    GroupInfoSignPredAuxWithWitness groupContext confirmationTag inviterEv joinerSecret ∧
    inviterEv.prin = inviterId ∧
    tr.EventLogged inviterEv

omit [ProofTraceTypes] in
/-- `group_info_sign_pred_aux` stays true when the trace grows (MLS* uses an SMT pattern). -/
public
theorem GroupInfoSignPredAux_le (tr1 tr2: ExecTrace) (inviterId: Participant) (groupContext: GroupContext Bytes)
  (confirmationTag: Bytes)
  : tr1 ≤ tr2 →
    GroupInfoSignPredAux tr1 inviterId groupContext confirmationTag →
    GroupInfoSignPredAux tr2 inviterId groupContext confirmationTag
:= by
  grind [GroupInfoSignPredAux]

grind_pattern GroupInfoSignPredAux_le => tr1 ≤ tr2, GroupInfoSignPredAux tr1 inviterId groupContext confirmationTag
grind_pattern [grind_later] GroupInfoSignPredAux_le =>
  tr1 ≤ tr2,
  GroupInfoSignPredAux tr1 inviterId groupContext confirmationTag

/-- The pred field of `group_info_sign_pred`. -/
public
def GroupInfoTbsPred (skUsg: Usage) (groupInfoTbsBytes: Bytes) (tr: ProofTrace): Prop :=
  match GroupInfoTBS.mf.toExtensible.parse groupInfoTbsBytes with
  | none => False
  | some groupInfoTbs =>
    ∃ inviterId,
      skUsg = mkMlsSigkeyUsage inviterId ∧
      GroupInfoSignPredAux tr.erase inviterId groupInfoTbs.groupContext groupInfoTbs.confirmationTag.val

/-- Port of `group_info_sign_pred` (with `group_info_tbs_tag_and_invariant`). -/
public
def groupInfoSignPred: SignWithLabelPred.Local ["GroupInfoTBS"] :=
  .single { pred skUsg _vk groupInfoTbsBytes tr := GroupInfoTbsPred skUsg groupInfoTbsBytes tr }

/-- Port of the `pred_later` field of `group_info_sign_pred`. -/
public
theorem groupInfoSignPredProof [BytesInvariants]: SignWithLabelPred.LocalProof groupInfoSignPred :=
  .single fun skUsg _vk groupInfoTbsBytes tr1 tr2 _ _ hle h => by
    change GroupInfoTbsPred skUsg groupInfoTbsBytes tr1 at h
    change GroupInfoTbsPred skUsg groupInfoTbsBytes tr2
    unfold GroupInfoTbsPred GroupInfoSignPredAux at *
    split at h <;> grind

/-- The group info signature predicate of `inviterId`, on a serialized `GroupInfoTBS`. -/
theorem groupInfoTbsPred_serializeNE (inviterId: Participant) (groupInfoTbs: GroupInfoTBS Bytes) (tr: ProofTrace):
  GroupInfoTbsPred (mkMlsSigkeyUsage inviterId) (serializeNE GroupInfoTBS.mf groupInfoTbs) tr ↔
    GroupInfoSignPredAux tr.erase inviterId groupInfoTbs.groupContext groupInfoTbs.confirmationTag.val
:= by
  simp [GroupInfoTbsPred, mkMlsSigkeyUsage_injective.eq_iff]

end Predicates

/-! ## Associated theorems -/

section Proofs

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

omit [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)] in
/--
Port of `get_signer_verification_key_proof`.
The postcondition also states that `vk` is the signature key of the inviter's leaf node,
which MLS*'s callers get from the definition of `get_signer_verification_key`.
-/
public
theorem getSignerVerificationKey_proof (tr: ProofTrace) {tkt: TreeKEMTypes Bytes} {l: Nat}
  (tree: TreeSync Bytes tkt l) (groupInfo: GroupInfo Bytes) (tokens: ASTokens DyAsToken l) (vk: Bytes)
  (h: getSignerVerificationKey tree groupInfo = .success vk)
  (hpos: tree.position = tokens.position) (hok: allCredentialsOk (dyAsp tr) tree tokens):
  groupInfo.tbs.signer.toNat < 2^l ∧
  ∃ inviterLeafNode inviterId,
    leafAt tree groupInfo.tbs.signer.toNat = some inviterLeafNode ∧
    credentialToPrincipal inviterLeafNode.data.credential = some inviterId ∧
    vk = inviterLeafNode.data.signatureKey.val ∧
    IsSignatureKeyVk tr inviterId vk
:= by
  unfold getSignerVerificationKey at h
  split at h
  · simp [Result.error] at h
  split at h
  · simp [Result.error] at h
  rename_i hsigner ln hln
  simp only [Result.pure_eq_success] at h
  subst h
  have hone := allCredentialsOk_elim tree tokens groupInfo.tbs.signer.toNat hpos hok
  simp only [oneCredentialOk, hln] at hone
  split at hone
  · obtain ⟨inviterId, hcp, hvk⟩ := isSignatureKeyVk_of_credentialOk tr _ _ _ hone
    refine ⟨?_, ln, inviterId, ?_⟩ <;> grind
  all_goals exfalso; grind

variable [SignWithLabelPred.Has groupInfoSignPred]

/--
Port of `sign_welcome_group_info_proof`.
MLS* requires `rand: sign_nonce bytes`, which is not needed.
-/
public
theorem signWelcomeGroupInfo_proof (tr: ProofTrace) (me: Participant) (sk: Bytes) (groupInfoTbs: GroupInfoTBS Bytes)
  (rand: Bytes) (groupInfo: GroupInfo Bytes)
  (h: signWelcomeGroupInfo sk groupInfoTbs rand = .success groupInfo)
  (hpred: GroupInfoSignPredAux tr.erase me groupInfoTbs.groupContext groupInfoTbs.confirmationTag.val)
  (hsk: IsSignatureKeySk tr me sk)
  (htbs: GroupInfoTBS.mf.wf (Bytes.Publishable · tr) groupInfoTbs)
  (hrand: rand.Invariant tr) (hrandUsg: rand.HasUsage Usage.sigNonce tr)
  (hflow: (sk.label tr).canFlow (rand.label tr) tr.erase):
  GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo
:= by
  simp only [signWelcomeGroupInfo, Result.bind_eq_success, mkMlsBytes_eq_success, Result.pure_eq_success] at h
  obtain ⟨signature, hsign, signature', rfl, rfl⟩ := h
  have htbs' := (pred_serializeNE_iff GroupInfoTBS.mf (Bytes.Publishable · tr) groupInfoTbs).2 htbs
  have hs := signWithLabel.Invariant groupInfoSignPred tr me sk "GroupInfoTBS" _ rand _ hsign
    hsk.1 hrand htbs'.1 hsk.2.2 hrandUsg hflow (by simp)
    (Or.inl ((groupInfoTbsPred_serializeNE _ _ _).2 hpred))
  rw [GroupInfo.mf.wf_eq]
  grind [Bytes.Publishable, canFlowTrans]

/--
Port of `verify_welcome_group_info_proof`.
When the signature of a group info verifies, and the key schedule state of the joiner is authenticated
by the confirmation tag of the group info, then either the signature key of the inviter is corrupt,
or the inviter has the same epoch event as the joiner.
-/
public
theorem verifyWelcomeGroupInfo_proof (tr: ProofTrace) (inviterId: Participant) (vk: Bytes) (groupInfo: GroupInfo Bytes)
  (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)) (keyscheduleSt: TreeKEMKeyscheduleState Bytes)
  (hverif: verifyWelcomeGroupInfo vk groupInfo = true)
  (hwf: GroupInfo.mf.wf (Bytes.Invariant · tr) groupInfo)
  (hvk: IsSignatureKeyVk tr inviterId vk)
  (hauth: TreekemKeyscheduleStateAuthStrong keyscheduleSt joinerSecret psks groupInfo.tbs.groupContext)
  (htag: groupInfo.tbs.confirmationTag.val = keyscheduleSt.epochKeys.confirmationTag):
  (signatureKeyLabel inviterId vk).isCorrupt tr.erase ∨
  InviterHasSameEventAsMe tr.erase inviterId groupInfo.tbs.groupContext psks keyscheduleSt
:= by
  rw [GroupInfo.mf.wf_eq] at hwf
  have htbs := (pred_serializeNE_iff GroupInfoTBS.mf (Bytes.Invariant · tr) groupInfo.tbs).2 hwf.1
  rcases verifyWithLabel.Invariant groupInfoSignPred tr inviterId vk "GroupInfoTBS" _ _ hvk.1.1 htbs hwf.2 hvk.2.2
    hverif (by simp) with hpred | hpub
  · right
    obtain ⟨inviterEv, inviterJoinerSecret, ⟨hgc, hct, hauth', -, hhow⟩, hevPrin, hev⟩ :=
      (groupInfoTbsPred_serializeNE _ _ _).1 hpred
    have := TreekemKeyscheduleStateAuthStrong.inj _ _ _ _ _ _ _ _ hauth' hauth (hct.symm.trans htag)
    refine ⟨inviterEv, ?_⟩
    grind [HasSameEventAsMe]
  · left
    rw [canFlowPubEqIsCorrupt, ← hvk.2.1]
    exact hpub

end Proofs

end MLS.Bootstrap
