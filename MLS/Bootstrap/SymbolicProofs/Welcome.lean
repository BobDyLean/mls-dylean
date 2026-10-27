module

public import MLS.Bootstrap.Code.Welcome
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.KeyPackageRef
public import MLS.TreeKEM.SymbolicProofs.Tree.Operations
public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.Common.SymbolicProofs.Crypto.Derived.EncryptWithLabel
public import MLS.Symbolic.SymbolicProofs.Randomness
public import DySlop.Lib.Crypto.AEAD.Split
public import MLS.TreeKEM.SymbolicProofs.KeySchedule
import all MLS.Bootstrap.SymbolicSpec.KeyPackage

/-!
Port of `MLS.Bootstrap.Symbolic.Welcome`: the HPKE predicate of the group secrets of a Welcome message,
the AEAD predicate of its group info, and the proofs of the encryption and decryption of the group secrets.

Port-specific differences:
- The local EncryptWithLabel and AEAD predicates are `EncryptWithLabelPred.Local` / `AeadPred.Local`,
  and MLS*'s `has_bootstrap_crypto_invariants` is the class `HasBootstrapCryptoInvariants`,
  whose fields are scoped instances in `MLS.Bootstrap`
  (it also contains HPKE's invariants, part of MLS*'s `has_mls_encryptwithlabel_pred`).
- Lemmas about functions returning a `Result` take the result and the success hypothesis
  (MLS*'s `match … with | Success … -> … | _ -> True`).
- `for_allP p l` is `∀ x ∈ l, p x`.
- MLS* uses `Some?.v (key_package_to_principal key_package)` and requires `Some? (key_package_to_principal key_package)`:
  the lemmas take the principal `prin` with a hypothesis `keyPackageToPrincipal keyPackage = some prin`.
-/

namespace MLS.Bootstrap

open Comparse
open DY DY.Comparse
open DySlop DySlop.HPKE DySlop.Aead
open MLS MLS.TreeSync MLS.TreeKEM

/-! ## Predicates -/

section Predicates

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMNodeKeysState)]

/-- The pred field of `mls_hpke_welcome_pred`. -/
@[expose]
public
def WelcomeHpkePred [BytesWellFormed] [GetUsage] [GetLabel] (usgData msg: Bytes) (tr: ProofTrace): Prop :=
  match InitKeyUsageT.mf.toExtensible.parse usgData, GroupSecrets.mf.toExtensible.parse msg with
  | some data, some groupSecrets =>
    let pskIds := serializeNE (MlsList.mf PreSharedKeyId.mf) groupSecrets.psks
    pskIds.WellFormed tr ∧
    (pskIds.label tr).canFlow Label.pub tr.erase ∧
    -- see `MLS.TreeKEM.DecodedPathSecretGood`
    ∀ pathSecret ∈ groupSecrets.pathSecret,
      (pathSecret.pathSecret.val.label tr).canFlow (nodeKeyLabel data.me data.leafPublicKey) tr.erase ∧
      ∃ d, pathSecret.pathSecret.val.HasUsage (Usage.kdfExpandKey "MLS.PathSecret" d) tr
  | _, _ => False

/-- Port of `mls_hpke_welcome_pred`. -/
@[expose]
public
def mlsHpkeWelcomePred: EncryptWithLabelPred.Local ["Welcome"] :=
  .single { pred usgData msg _context tr := WelcomeHpkePred usgData msg tr }

/-- Port of the `pred_later` field of `mls_hpke_welcome_pred`. -/
public
theorem mlsHpkeWelcomePredProof
  [BytesInvariants] [BytesInvariants.Has DY.Literal.invariants] [BytesInvariants.Has DY.Concat.invariants]:
  EncryptWithLabelPred.LocalProof mlsHpkeWelcomePred :=
  EncryptWithLabelPred.LocalProof.single fun usgData msg _ tr1 tr2 hmsg _ hle h => by
    change WelcomeHpkePred usgData msg tr1 at h
    change WelcomeHpkePred usgData msg tr2
    unfold WelcomeHpkePred at *
    cases hdata: InitKeyUsageT.mf.toExtensible.parse usgData <;>
      cases hgs: GroupSecrets.mf.toExtensible.parse msg <;> simp only [hdata, hgs] at h ⊢
    rename_i groupSecrets
    have hwf := wf_of_parse GroupSecrets.mf (Bytes.WellFormed · tr1) msg groupSecrets hgs hmsg
    grind [Label.canFlowLater, Bytes.HasUsage_later, GroupSecrets.mf.wf_eq, MlsOption.mf.wf_eq, PathSecret.mf.wf_eq]

end Predicates

section AeadPredicate

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes]

/-- The pred field of `aead_group_info_pred`. -/
@[expose]
public
def AeadGroupInfoPred [BytesWellFormed] [GetUsage] [GetLabel] (msg: Bytes) (tr: ProofTrace): Prop :=
  match GroupInfo.mf.toExtensible.parse msg with
  | none => False
  | some groupInfo => ((serializeNE GroupContext.mf groupInfo.tbs.groupContext).label tr).canFlow Label.pub tr.erase

/-- Port of `aead_group_info_pred`. -/
@[expose]
public
def aeadGroupInfoPred: AeadPred.Local ["MLS.Bootstrap.WelcomeKey"] :=
  .single { pred _keyUsg _key _nonce msg _ad tr := AeadGroupInfoPred msg tr }

/-- Port of the `pred_later` field of `aead_group_info_pred`. -/
public
theorem aeadGroupInfoPredProof
  [BytesInvariants] [BytesInvariants.Has DY.Literal.invariants] [BytesInvariants.Has DY.Concat.invariants]:
  AeadPred.LocalProof aeadGroupInfoPred :=
  AeadPred.LocalProof.single fun _ _ _ msg _ tr1 tr2 _ _ hmsg _ hle h => by
    change AeadGroupInfoPred msg tr1 at h
    change AeadGroupInfoPred msg tr2
    unfold AeadGroupInfoPred at *
    cases hgi: GroupInfo.mf.toExtensible.parse msg <;> simp only [hgi] at h ⊢
    rename_i groupInfo
    have hwf := wf_of_parse GroupInfo.mf (Bytes.WellFormed · tr1) msg groupInfo hgi hmsg
    have := (pred_serializeNE_iff GroupContext.mf (Bytes.WellFormed · tr1) groupInfo.tbs.groupContext).2
      (by simp_all)
    grind [Label.canFlowLater]

end AeadPredicate

section Invariants

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/--
Port of `has_bootstrap_crypto_invariants`
(with HPKE's invariants, part of MLS*'s `has_mls_encryptwithlabel_pred`).
The fields are scoped instances in the namespace `MLS.Bootstrap`; the top-level protocol provides them
(`instance: HasBootstrapCryptoInvariants where`).
-/
public
class HasBootstrapCryptoInvariants: Prop where
  [encryptWelcome: EncryptWithLabelPred.Has "MLS.InitHpkeKey" mlsHpkeWelcomePred]
  [aeadGroupInfo: AeadPred.Has aeadGroupInfoPred]
  [hpkeKdfExpand: KdfExpand.KdfExpandUsage.Has HPKE.kdfExpandUsage]
  [hpkeAead: AeadPred.Has HPKE.aeadPred]
  [keySchedule: HasMlsKeyscheduleInvariants]

attribute [scoped instance] HasBootstrapCryptoInvariants.encryptWelcome
attribute [scoped instance] HasBootstrapCryptoInvariants.aeadGroupInfo
attribute [scoped instance] HasBootstrapCryptoInvariants.hpkeKdfExpand
attribute [scoped instance] HasBootstrapCryptoInvariants.hpkeAead
attribute [scoped instance] HasBootstrapCryptoInvariants.keySchedule

end Invariants

/-! ## Decryption -/

/-- Port of `find_my_encrypted_group_secret_spec`. -/
theorem findMyEncryptedGroupSecret_spec {Bytes: Type} [CryptoBytes Bytes] {a: Type}
  (kpRefToKpSecrets: Bytes → Option a) (l: List (EncryptedGroupSecrets Bytes))
  (newMember: KeyPackageRef Bytes) (kpSecrets: a) (encryptedGroupSecrets: HpkeCiphertext Bytes)
  (h: findMyEncryptedGroupSecret kpRefToKpSecrets l = some (newMember, kpSecrets, encryptedGroupSecrets)):
  kpRefToKpSecrets newMember.val = some kpSecrets ∧ { newMember, encryptedGroupSecrets } ∈ l
:= by
  induction l with
  | nil => grind [findMyEncryptedGroupSecret]
  | cons hd t ih =>
    cases hd
    grind [findMyEncryptedGroupSecret]

section PskIds

variable [HasSymbolicInvariants]

/-- Port of `psk_ids_good`. -/
@[expose]
public
def PskIdsGood (tr: ProofTrace) (pskIds: List (PreSharedKeyId Bytes)): Prop :=
  ∀ pskId ∈ pskIds, PreSharedKeyId.mf.wf (Bytes.Publishable · tr) pskId

/-- Port of `psk_ids_good_later`. -/
public
theorem PskIdsGood_later (tr1 tr2: ProofTrace) (pskIds: List (PreSharedKeyId Bytes))
  : tr1 ≤ tr2 →
    PskIdsGood tr1 pskIds →
    PskIdsGood tr2 pskIds
:= by
  intro hle h pskId hpskId
  have := h pskId hpskId
  cases pskId <;> simp only [PreSharedKeyId.mf.wf_eq] at this ⊢ <;> grind

grind_pattern PskIdsGood_later => tr1 ≤ tr2, PskIdsGood tr1 pskIds
grind_pattern [grind_later] PskIdsGood_later => tr1 ≤ tr2, PskIdsGood tr1 pskIds

/-- `PskIdsGood` is the well-formedness of the serialized list of pre-shared key identifiers. -/
theorem pskIdsGood_iff (tr: ProofTrace) (pskIds: MlsList (PreSharedKeyId.mf (Bytes := Bytes))):
  PskIdsGood tr pskIds.val ↔ (serializeNE (MlsList.mf PreSharedKeyId.mf) pskIds).Publishable tr
:= by
  rw [pred_serializeNE_iff (MlsList.mf PreSharedKeyId.mf) (Bytes.Publishable · tr), MlsList.mf.wf_eq]
  rfl

/-- Publishable pre-shared key identifiers are knowable by any label. -/
theorem PreSharedKeyId.wf_knowableBy_of_publishable (tr: ProofTrace) (l: Label) (pskId: PreSharedKeyId Bytes)
  (h: PreSharedKeyId.mf.wf (Bytes.Publishable · tr) pskId):
  PreSharedKeyId.mf.wf (Bytes.KnowableBy l · tr) pskId
:= by
  cases pskId <;> simp only [PreSharedKeyId.mf.wf_eq] at h ⊢ <;> grind [canFlowTrans]

end PskIds

section Code

variable [HasSymbolicBytes]

theorem mkHpkeKemOutput_eq_success (b: Bytes) (funName varName: String) (x: Bytes)
  (h: mkHpkeKemOutput b funName varName = .success x):
  x = b
:= by
  unfold mkHpkeKemOutput at h
  split at h <;> simp_all [Result.error]

theorem mkHpkePublicKey_eq_success (b: Bytes) (funName varName: String) (x: Bytes)
  (h: mkHpkePublicKey b funName varName = .success x):
  x = b
:= by
  unfold mkHpkePublicKey at h
  split at h <;> simp_all [Result.error]

end Code

section Decrypt

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [HasBootstrapCryptoInvariants]

/--
Port of `_decrypt_group_secrets_proof`.
MLS* requires `my_hpke_sk: hpke_private_key bytes`, which is not needed.
-/
public
theorem decryptGroupSecrets'_proof (tr: ProofTrace) (me: Participant) (myLeafPk: Bytes)
  (myHpkeSk: Bytes) (myHpkeCiphertext: HpkeCiphertext Bytes) (ad: Bytes) (groupSecrets: GroupSecrets Bytes)
  (h: decryptGroupSecrets' myHpkeSk myHpkeCiphertext ad = .success groupSecrets)
  (hsk: myHpkeSk.Invariant tr) (hskUsg: myHpkeSk.HasUsage (initKeyUsage me myLeafPk) tr)
  (hkemOutput: myHpkeCiphertext.kemOutput.val.Invariant tr) (hciphertext: myHpkeCiphertext.ciphertext.val.Invariant tr)
  (had: ad.Invariant tr):
  GroupSecrets.mf.wf (Bytes.Invariant · tr) groupSecrets ∧
  PskIdsGood tr groupSecrets.psks.val ∧
  ∀ pathSecret ∈ groupSecrets.pathSecret, DecodedPathSecretGood me myLeafPk pathSecret.pathSecret.val tr
:= by
  simp only [decryptGroupSecrets', Result.bind_eq_success, Result.fromOption_eq_success] at h
  obtain ⟨kemOutput, hkem, gsBytes, hdec, hparse⟩ := h
  obtain rfl := mkHpkeKemOutput_eq_success _ _ _ _ hkem
  obtain ⟨hknow, hor⟩ := decryptWithLabel.Invariant mlsHpkeWelcomePred "MLS.InitHpkeKey" (initKeyUsageData me myLeafPk) tr
    myHpkeSk "Welcome" ad _ _ gsBytes hdec hsk hskUsg hkemOutput had hciphertext (by simp)
  have hwf := wf_of_parse GroupSecrets.mf (Bytes.Invariant · tr) gsBytes groupSecrets hparse hknow.1
  refine ⟨hwf, ?_⟩
  rcases hor with hpred | hpub
  · -- the predicate holds
    simp only [mlsHpkeWelcomePred, EncryptWithLabelPred.Local.pred_single, WelcomeHpkePred, initKeyUsageData,
      parse_serializeNE, hparse] at hpred
    simp only [GroupSecrets.mf.wf_eq, MlsOption.mf.wf_eq] at hwf
    have := (pred_serializeNE_iff (MlsList.mf PreSharedKeyId.mf) (Bytes.Invariant · tr) groupSecrets.psks).2
      (by simpa using hwf.2.2)
    grind [pskIdsGood_iff, Bytes.Publishable, DecodedPathSecretGood, PathSecret.mf.wf_eq]
  · -- the group secrets are public
    have hwfPub := wf_of_parse GroupSecrets.mf (Bytes.Publishable · tr) gsBytes groupSecrets hparse hpub
    simp only [GroupSecrets.mf.wf_eq, MlsOption.mf.wf_eq] at hwfPub
    refine ⟨hwfPub.2.2, fun ps hps => ⟨?_, ?_, BytesLike.empty, ?_⟩⟩ <;>
      grind [Bytes.Publishable, canFlowTrans, Bytes.HasUsage_public, PathSecret.mf.wf_eq]

end Decrypt

section KpSecrets

variable [HasSymbolicInvariants]

/-- Port of `one_kp_secrets_good`. MLS*'s `match` on the result of `kp_secrets_to_hpke_sk` is a `∀`. -/
@[expose]
public
def OneKpSecretsGood {a: Type} (tr: ProofTrace) (me: Participant)
  (kpSecretsToHpkeSk: a → Result Bytes) (kpSecretsToKeyPackage: a → KeyPackage Bytes TreeKEM.tkt) (kpSecrets: a): Prop :=
  ∀ hpkeSk, kpSecretsToHpkeSk kpSecrets = .success hpkeSk →
    hpkeSk.Invariant tr ∧
    hpkeSk.HasUsage (initKeyUsage me (kpSecretsToKeyPackage kpSecrets).tbs.leafNode.data.content.val) tr ∧
    credentialToPrincipal (kpSecretsToKeyPackage kpSecrets).tbs.leafNode.data.credential = some me

/-- `OneKpSecretsGood` is preserved when the trace grows (MLS* uses an SMT pattern). -/
public
theorem OneKpSecretsGood_later {a: Type} (tr1 tr2: ProofTrace) (me: Participant)
  (kpSecretsToHpkeSk: a → Result Bytes) (kpSecretsToKeyPackage: a → KeyPackage Bytes TreeKEM.tkt) (kpSecrets: a)
  : tr1 ≤ tr2 →
    OneKpSecretsGood tr1 me kpSecretsToHpkeSk kpSecretsToKeyPackage kpSecrets →
    OneKpSecretsGood tr2 me kpSecretsToHpkeSk kpSecretsToKeyPackage kpSecrets
:= by
  grind [OneKpSecretsGood]

grind_pattern OneKpSecretsGood_later =>
  tr1 ≤ tr2,
  OneKpSecretsGood tr1 me kpSecretsToHpkeSk kpSecretsToKeyPackage kpSecrets
grind_pattern [grind_later] OneKpSecretsGood_later =>
  tr1 ≤ tr2,
  OneKpSecretsGood tr1 me kpSecretsToHpkeSk kpSecretsToKeyPackage kpSecrets

/-- Port of `kp_secrets_good`. -/
@[expose]
public
def KpSecretsGood {a: Type} (tr: ProofTrace) (me: Participant)
  (kpSecretsToHpkeSk: a → Result Bytes) (kpSecretsToKeyPackage: a → KeyPackage Bytes TreeKEM.tkt)
  (kpRefToKpSecrets: Bytes → Option a): Prop :=
  ∀ kpRef, ∀ kpSecrets ∈ kpRefToKpSecrets kpRef, OneKpSecretsGood tr me kpSecretsToHpkeSk kpSecretsToKeyPackage kpSecrets

end KpSecrets

section DecryptGroupSecrets

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [HasBootstrapCryptoInvariants]

/-- Port of `decrypt_group_secrets_proof`. -/
public
theorem decryptGroupSecrets_proof {a: Type} (tr: ProofTrace) (me: Participant) (welcome: Welcome Bytes)
  (kpRefToKpSecrets: Bytes → Option a) (kpSecretsToHpkeSk: a → Result Bytes)
  (kpSecretsToKeyPackage: a → KeyPackage Bytes TreeKEM.tkt)
  (groupSecrets: GroupSecrets Bytes) (myKpRef: KeyPackageRef Bytes) (myKpSecrets: a)
  (h: decryptGroupSecrets welcome kpRefToKpSecrets kpSecretsToHpkeSk = .success (groupSecrets, (myKpRef, myKpSecrets)))
  (hwelcome: Welcome.mf.wf (Bytes.Invariant · tr) welcome)
  (hkp: KpSecretsGood tr me kpSecretsToHpkeSk kpSecretsToKeyPackage kpRefToKpSecrets):
  GroupSecrets.mf.wf (Bytes.Invariant · tr) groupSecrets ∧
  PskIdsGood tr groupSecrets.psks.val ∧
  kpRefToKpSecrets myKpRef.val = some myKpSecrets ∧
  ∀ pathSecret ∈ groupSecrets.pathSecret,
    DecodedPathSecretGood me (kpSecretsToKeyPackage myKpSecrets).tbs.leafNode.data.content.val pathSecret.pathSecret.val tr
:= by
  simp only [decryptGroupSecrets, Result.bind_eq_success, Result.fromOption_eq_success, Result.pure_eq_success] at h
  obtain ⟨⟨kpRef, kpSecrets, ct⟩, hfind, hpkeSk, hsk, gs, hdec, ⟨rfl, rfl, rfl⟩⟩ := h
  obtain ⟨hkpRef, hmem⟩ := findMyEncryptedGroupSecret_spec _ _ _ _ _ hfind
  rw [Welcome.mf.wf_eq] at hwelcome
  have hct := hwelcome.1 _ hmem
  rw [EncryptedGroupSecrets.mf.wf_eq, HpkeCiphertext.mf.wf_eq] at hct
  obtain ⟨hskInv, hskUsg, -⟩ := hkp _ _ hkpRef hpkeSk hsk
  have := decryptGroupSecrets'_proof tr me _ _ _ _ _ hdec hskInv hskUsg hct.2.1 hct.2.2 hwelcome.2
  grind

end DecryptGroupSecrets

/-! ## Encryption -/

/--
Port of `mk_group_secrets_proof`.
MLS*'s `match` on the path secrets is an equation on `Option.map`.
-/
theorem mkGroupSecrets_proof {Bytes: Type} [BytesLike Bytes]
  (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes)) (pathSecret: Option Bytes) (groupSecrets: GroupSecrets Bytes)
  (h: mkGroupSecrets joinerSecret psks pathSecret = .success groupSecrets):
  groupSecrets.joinerSecret.val = joinerSecret ∧
  groupSecrets.psks.val = psks ∧
  groupSecrets.pathSecret.map (·.pathSecret.val) = pathSecret
:= by
  cases pathSecret <;>
    simp only [mkGroupSecrets, Result.bind_eq_success, mkMlsBytes_eq_success, mkMlsList_eq_success,
      Result.pure_eq_success] at h <;> grind

section EncryptOne

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [HasKeyPackageInvariant] [HasBootstrapCryptoInvariants]

/--
Port of `encrypt_one_group_secrets_proof`.
MLS* requires `Some? (key_package_to_principal key_package)`, whose value is `prin` (here `hprin`);
it also requires `entropy: lbytes bytes (hpke_private_key_length #bytes)`, which is not needed.
-/
public
theorem encryptOneGroupSecrets_proof (tr: ProofTrace) (me prin: Participant)
  (keyPackage: KeyPackage Bytes TreeKEM.tkt) (encryptedGroupInfo: Bytes) (groupSecrets: GroupSecrets Bytes) (entropy: Bytes)
  (res: EncryptedGroupSecrets Bytes)
  (h: encryptOneGroupSecrets keyPackage encryptedGroupInfo groupSecrets entropy = .success res)
  (hprin: keyPackageToPrincipal keyPackage = some prin)
  (hkp: (KeyPackage.mf TreeKEM.tkt).wf (Bytes.Publishable · tr) keyPackage)
  (hegi: encryptedGroupInfo.Publishable tr)
  (hjoiner: groupSecrets.joinerSecret.val.KnowableBy (keyPackageToInitLabel keyPackage) tr)
  (hps: ∀ pathSecret ∈ groupSecrets.pathSecret,
    pathSecret.pathSecret.val.KnowableBy (keyPackageToInitLabel keyPackage) tr ∧
    (pathSecret.pathSecret.val.label tr).canFlow (nodeKeyLabel prin keyPackage.tbs.leafNode.data.content.val) tr.erase ∧
    ∃ d, pathSecret.pathSecret.val.HasUsage (Usage.kdfExpandKey "MLS.PathSecret" d) tr)
  (hpsks: PskIdsGood tr groupSecrets.psks.val)
  (hentropy: entropy.Invariant tr) (hentropyLabel: entropy.label tr = keyPackageToInitLabel keyPackage)
  (hentropyUsg: entropy.HasUsage (entropyUsageForInitKey prin keyPackage.tbs.leafNode.data.content.val) tr)
  (hev: IHaveVerifiedKeyPackage tr.erase me keyPackage) (hinv: tr.Invariant):
  EncryptedGroupSecrets.mf.wf (Bytes.Publishable · tr) res
:= by
  simp only [encryptOneGroupSecrets, Result.bind_eq_success, mkMlsBytes_eq_success, Result.pure_eq_success] at h
  obtain ⟨kpRef, hkpRef, pk, hpk, ⟨kemOutput, ciphertext⟩, henc, kemOutput', rfl, ciphertext', rfl, rfl⟩ := h
  obtain rfl := mkHpkePublicKey_eq_success _ _ _ _ hpk
  obtain ⟨prin', hcp, hflow, hor⟩ := keyPackageToInitLabel_lemma tr me keyPackage hev hinv
  obtain rfl: prin = prin' := by simp_all
  -- the group secrets are knowable by the init label of the key package
  have hgs: GroupSecrets.mf.wf (Bytes.KnowableBy (keyPackageToInitLabel keyPackage) · tr) groupSecrets := by
    simp only [GroupSecrets.mf.wf_eq, MlsOption.mf.wf_eq]
    refine ⟨hjoiner, ?_, fun pskId hpskId => PreSharedKeyId.wf_knowableBy_of_publishable _ _ _ (hpsks pskId hpskId)⟩
    split <;> grind [PathSecret.mf.wf_eq]
  have hgsBytes := (pred_serializeNE_iff GroupSecrets.mf (Bytes.KnowableBy (keyPackageToInitLabel keyPackage) · tr) _).2 hgs
  have hkp' := hkp
  rw [KeyPackage.mf.wf_eq, KeyPackageTBS.mf.wf_eq] at hkp'
  have hres := encryptWithLabel.Invariant mlsHpkeWelcomePred "MLS.InitHpkeKey"
    (initKeyUsageData prin keyPackage.tbs.leafNode.data.content.val) tr _ "Welcome" encryptedGroupInfo _ entropy
    _ _ henc hkp'.1.1.1 hentropy hegi.1 hgsBytes.1 (hentropyLabel ▸ hgsBytes.2) (hentropyLabel ▸ hflow)
    hentropyUsg ?_ (by simp)
  · have := computeKeyPackageRef_knowableBy tr Label.pub keyPackage kpRef hkpRef hkp
    simp only [EncryptedGroupSecrets.mf.wf_eq, HpkeCiphertext.mf.wf_eq]
    exact ⟨this, hres⟩
  rcases hor with husg | hpub
  · -- the init key has the init key usage: the predicate holds
    refine Or.inl ⟨husg, ?_⟩
    simp only [mlsHpkeWelcomePred, EncryptWithLabelPred.Local.pred_single, WelcomeHpkePred, initKeyUsageData,
      parse_serializeNE]
    have := (pskIdsGood_iff tr _).1 hpsks
    grind [Bytes.Publishable]
  · -- the init label of the key package is public
    grind

end EncryptOne

section EncryptGroupSecrets

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `one_opt_path_secret_good`. -/
@[expose]
public
def OneOptPathSecretGood (tr: ProofTrace) (x: KeyPackage Bytes TreeKEM.tkt × Option Bytes): Prop :=
  ∀ pathSecret ∈ x.2,
    ∃ prin, keyPackageToPrincipal x.1 = some prin ∧
      pathSecret.KnowableBy (keyPackageToInitLabel x.1) tr ∧
      (pathSecret.label tr).canFlow (nodeKeyLabel prin x.1.tbs.leafNode.data.content.val) tr.erase ∧
      ∃ d, pathSecret.HasUsage (Usage.kdfExpandKey "MLS.PathSecret" d) tr

/-- Port of `all_opt_path_secret_good`. -/
@[expose]
public
def AllOptPathSecretGood (tr: ProofTrace) (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes)): Prop :=
  ∀ x ∈ keyPackages, OneOptPathSecretGood tr x

/-- Port of `all_opt_path_secret_good_later`. -/
public
theorem AllOptPathSecretGood_later (tr1 tr2: ProofTrace) (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes))
  : tr1 ≤ tr2 →
    AllOptPathSecretGood tr1 keyPackages →
    AllOptPathSecretGood tr2 keyPackages
:= by
  intro hle h x hx ps hps
  grind [OneOptPathSecretGood, AllOptPathSecretGood, Bytes.KnowableBy, Label.canFlowLater, Bytes.label_later,
    Bytes.HasUsage_later]

grind_pattern AllOptPathSecretGood_later => tr1 ≤ tr2, AllOptPathSecretGood tr1 keyPackages
grind_pattern [grind_later] AllOptPathSecretGood_later => tr1 ≤ tr2, AllOptPathSecretGood tr1 keyPackages

/-- Port of `encrypt_group_secrets_entropy_ghost_data`. -/
@[expose]
public
def encryptGroupSecretsEntropyGhostData: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes) → RandomnessGhostData
  | [] => []
  | (keyPackage, _) :: keyPackages =>
    (match keyPackageToPrincipal keyPackage with
      | some prin => (entropyUsageForInitKey prin keyPackage.tbs.leafNode.data.content.val, keyPackageToInitLabel keyPackage)
      | none => (Usage.nothing, Label.unknown)) ::
    encryptGroupSecretsEntropyGhostData keyPackages

variable [TraceInvariant] [HasKeyPackageInvariant] [HasBootstrapCryptoInvariants]

/--
Port of `encrypt_group_secrets_proof`.
MLS* requires `rand: randomness bytes (encrypt_welcome_entropy_length key_packages)`, which is not needed.
-/
public
theorem encryptGroupSecrets_proof (tr: ProofTrace) (me: Participant)
  (encryptedGroupInfo joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes))
  (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes)) (rand: Randomness Bytes)
  (res: List (EncryptedGroupSecrets Bytes))
  (h: encryptGroupSecrets encryptedGroupInfo joinerSecret psks keyPackages rand = .success res)
  (hegi: encryptedGroupInfo.Publishable tr)
  (hkps: ∀ kp ∈ keyPackages.map Prod.fst, (KeyPackage.mf TreeKEM.tkt).wf (Bytes.Publishable · tr) kp)
  (hev: IHaveVerifiedEveryKeyPackage tr.erase me (keyPackages.map Prod.fst))
  (hps: AllOptPathSecretGood tr keyPackages)
  (hjoiner: joinerSecret.KnowableBy
    (((keyPackages.map Prod.fst).map keyPackageToInitLabel).foldr Label.join Label.secret) tr)
  (hpsks: PskIdsGood tr psks)
  (hrand: RandomnessHasGhostData tr rand (encryptGroupSecretsEntropyGhostData keyPackages))
  (hinv: tr.Invariant):
  ∀ encryptedGroupSecrets ∈ res, EncryptedGroupSecrets.mf.wf (Bytes.Publishable · tr) encryptedGroupSecrets
:= by
  induction keyPackages generalizing rand res with
  | nil =>
    simp only [encryptGroupSecrets, Result.pure_eq_success] at h
    simp [← h]
  | cons x keyPackages ih =>
    obtain ⟨kp, pathSecret⟩ := x
    simp only [encryptGroupSecrets, Result.bind_eq_success, Result.pure_eq_success] at h
    obtain ⟨⟨randCur, randNext⟩, hdest, groupSecrets, hgs, resHead, hhead, resTail, htail, rfl⟩ := h
    simp only [IHaveVerifiedEveryKeyPackage, AllOptPathSecretGood, Bytes.KnowableBy, Label.joinEq, List.map_cons,
      List.mem_cons, forall_eq_or_imp, List.foldr_cons] at hkps hjoiner hev hps
    obtain ⟨prin, hprin, -⟩ := keyPackageToInitLabel_lemma tr me kp hev.1 hinv
    simp only [encryptGroupSecretsEntropyGhostData, hprin] at hrand
    obtain ⟨hcur, hcurUsg, hcurLabel, hnext⟩ := RandomnessHasGhostData.dest _ _ _ _ _ _ _ hrand hdest
    have := mkGroupSecrets_proof _ _ _ _ hgs
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, ih randNext resTail htail hkps.2 hev.2 hps.2 ⟨hjoiner.1, hjoiner.2.2⟩ hnext⟩
    apply encryptOneGroupSecrets_proof tr me prin kp encryptedGroupInfo groupSecrets randCur resHead
    case hps =>
      intro ps hps'
      have := Option.mem_map_of_mem (·.pathSecret.val) hps'
      grind [OneOptPathSecretGood]
    all_goals grind [Bytes.KnowableBy]

end EncryptGroupSecrets

/-! ## Group info -/

section GroupInfo

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [HasBootstrapCryptoInvariants]

/-- The AEAD predicate on the key of the group info of a Welcome message. -/
theorem aeadPred_welcomeKey (key nonce msg ad: Bytes) (tr: ProofTrace):
  AeadPred.pred (Usage.aeadKey "MLS.Bootstrap.WelcomeKey" BytesLike.empty) key nonce msg ad tr = AeadGroupInfoPred msg tr
:= by
  rw [AeadPred.Has.pred_eq (l := aeadGroupInfoPred) _ _ _ _ _ _ rfl (by simp [Usage.aeadKey]), aeadGroupInfoPred,
    AeadPred.Local.pred_single (tag := "MLS.Bootstrap.WelcomeKey") _
      (Usage.aeadKey "MLS.Bootstrap.WelcomeKey" BytesLike.empty) key nonce msg ad tr rfl rfl]
  rfl

omit [HasTreeKEMExecTrace] [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
  [HasBootstrapCryptoInvariants] in
/-- The group context of a group info, when the group info satisfies the AEAD predicate of Welcome messages. -/
theorem groupContext_publishable_of_aeadGroupInfoPred (tr: ProofTrace) (groupInfoBytes: Bytes) (groupInfo: GroupInfo Bytes)
  (hparse: GroupInfo.mf.toExtensible.parse groupInfoBytes = some groupInfo)
  (hwf: GroupInfo.mf.wf (Bytes.Invariant · tr) groupInfo) (hpred: AeadGroupInfoPred groupInfoBytes tr):
  GroupContext.mf.wf (Bytes.Publishable · tr) groupInfo.tbs.groupContext
:= by
  simp only [AeadGroupInfoPred, hparse] at hpred
  simp only [GroupInfo.mf.wf_eq, GroupInfoTBS.mf.wf_eq] at hwf
  have := (pred_serializeNE_iff GroupContext.mf (Bytes.Invariant · tr) _).2 hwf.1.1
  exact (pred_serializeNE_iff GroupContext.mf (Bytes.Publishable · tr) _).1 ⟨this, hpred⟩

/-- Port of `decrypt_group_info_proof`. -/
public
theorem decryptGroupInfo_proof (tr: ProofTrace) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (encryptedGroupInfo: Bytes) (groupInfo: GroupInfo Bytes)
  (h: decryptGroupInfo joinerSecret psks encryptedGroupInfo = .success groupInfo)
  (hegi: encryptedGroupInfo.Invariant tr) (hjoiner: joinerSecret.Invariant tr) (hpsks: PsksBytesInvariant tr psks):
  GroupInfo.mf.wf (Bytes.Invariant · tr) groupInfo ∧
  GroupContext.mf.wf (Bytes.Publishable · tr) groupInfo.tbs.groupContext
:= by
  simp only [decryptGroupInfo, Result.bind_eq_success, Result.fromOption_eq_success] at h
  obtain ⟨welcomeSecret, hws, welcomeKey, hkey, welcomeNonce, hnonce, groupInfoBytes, hdec, hparse⟩ := h
  obtain ⟨hwsInv, hwsUsg, -⟩ := secretJoinerToWelcome_proof tr _ _ _ hws hjoiner hpsks
  obtain ⟨hkeyInv, hkeyUsg, -⟩ := welcomeSecretToKey_proof tr _ _ hkey hwsInv hwsUsg
  have hnonceInv := welcomeSecretToNonce_proof tr _ _ hnonce hwsInv hwsUsg
  have hdec': DySlop.Aead.aeadDec welcomeKey welcomeNonce encryptedGroupInfo BytesLike.empty = some groupInfoBytes := by
    simp only [CryptoBytes.aeadDecrypt] at hdec
    split at hdec <;> simp_all [Result.error]
  have hd := DySlop.Aead.aeadDec.Invariant welcomeKey welcomeNonce encryptedGroupInfo BytesLike.empty tr hkeyInv
    hnonceInv.1 hegi (BytesCompatiblePred.pred_empty (pred := (Bytes.Invariant · tr)))
  simp only [hdec'] at hd
  obtain ⟨hknow, hor⟩ := hd
  have hwf := wf_of_parse GroupInfo.mf (Bytes.Invariant · tr) groupInfoBytes groupInfo hparse hknow.1
  refine ⟨hwf, ?_⟩
  rcases hor with hpred | hpub
  · have := hpred _ hkeyUsg rfl
    rw [aeadPred_welcomeKey] at this
    exact groupContext_publishable_of_aeadGroupInfoPred tr _ _ hparse hwf this
  · -- the welcome key is publishable, hence the group info
    have hgiPub: groupInfoBytes.Publishable tr := by grind [Bytes.Publishable, Bytes.KnowableBy, canFlowTrans]
    have := wf_of_parse GroupInfo.mf (Bytes.Publishable · tr) groupInfoBytes groupInfo hparse hgiPub
    grind [GroupInfo.mf.wf_eq, GroupInfoTBS.mf.wf_eq]

/-- Port of `encrypt_group_info_proof`. -/
public
theorem encryptGroupInfo_proof (tr: ProofTrace) (joinerSecret: Bytes) (psks: List (PreSharedKeyId Bytes × Bytes))
  (groupInfo: GroupInfo Bytes) (encryptedGroupInfo: MlsBytes Bytes)
  (h: encryptGroupInfo joinerSecret psks groupInfo = .success encryptedGroupInfo)
  (hjoiner: joinerSecret.Invariant tr) (hgi: GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo)
  (hpsks: PsksBytesInvariant tr psks):
  encryptedGroupInfo.val.Publishable tr
:= by
  simp only [encryptGroupInfo, Result.bind_eq_success, mkMlsBytes_eq_success, CryptoBytes.aeadEncrypt,
    Result.pure_eq_success] at h
  obtain ⟨welcomeSecret, hws, welcomeKey, hkey, welcomeNonce, hnonce, _, rfl, heq⟩ := h
  rw [← heq]
  obtain ⟨hwsInv, hwsUsg, -⟩ := secretJoinerToWelcome_proof tr _ _ _ hws hjoiner hpsks
  obtain ⟨hkeyInv, hkeyUsg, -⟩ := welcomeSecretToKey_proof tr _ _ hkey hwsInv hwsUsg
  have hnonceInv := welcomeSecretToNonce_proof tr _ _ hnonce hwsInv hwsUsg
  have hgiBytes := (pred_serializeNE_iff GroupInfo.mf (Bytes.Publishable · tr) groupInfo).2 hgi
  have hempty := BytesCompatiblePred.pred_empty (pred := (Bytes.Publishable · tr))
  refine ⟨DySlop.Aead.aeadEnc.Invariant welcomeKey _ welcomeNonce _ _ tr hkeyInv hnonceInv.1 hgiBytes.1 hempty.1
    hnonceInv.2 hempty.2 (canFlowTrans _ _ _ _ hgiBytes.2 (Label.pubCanFlow _ _)) hkeyUsg (Or.inl ⟨rfl, ?_⟩), ?_⟩
  · rw [aeadPred_welcomeKey]
    simp only [AeadGroupInfoPred, parse_serializeNE]
    simp only [GroupInfo.mf.wf_eq, GroupInfoTBS.mf.wf_eq] at hgi
    exact ((pred_serializeNE_iff GroupContext.mf (Bytes.Publishable · tr) _).2 hgi.1.1).2
  · grind [DySlop.Aead.aeadEnc.label]

variable [TraceInvariant] [HasKeyPackageInvariant]

/--
Port of `encrypt_welcome_proof`.
MLS* requires `rand: randomness bytes (encrypt_welcome_entropy_length key_packages)`, which is not needed.
-/
public
theorem encryptWelcome_proof (tr: ProofTrace) (me: Participant) (groupInfo: GroupInfo Bytes) (joinerSecret: Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)) (keyPackages: List (KeyPackage Bytes TreeKEM.tkt × Option Bytes))
  (rand: Randomness Bytes) (welcome: Welcome Bytes)
  (h: encryptWelcome groupInfo joinerSecret psks keyPackages rand = .success welcome)
  (hjoiner: joinerSecret.Invariant tr)
  (hgi: GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo)
  (hkps: ∀ kp ∈ keyPackages.map Prod.fst, (KeyPackage.mf TreeKEM.tkt).wf (Bytes.Publishable · tr) kp)
  (hev: IHaveVerifiedEveryKeyPackage tr.erase me (keyPackages.map Prod.fst))
  (hps: AllOptPathSecretGood tr keyPackages)
  (hjoinerLabel: joinerSecret.KnowableBy
    (((keyPackages.map Prod.fst).map keyPackageToInitLabel).foldr Label.join Label.secret) tr)
  (hpsks: PsksBytesInvariant tr psks)
  (hrand: RandomnessHasGhostData tr rand (encryptGroupSecretsEntropyGhostData keyPackages))
  (hinv: tr.Invariant):
  Welcome.mf.wf (Bytes.Publishable · tr) welcome
:= by
  simp only [encryptWelcome, Result.bind_eq_success, mkMlsList_eq_success, Result.pure_eq_success] at h
  obtain ⟨encryptedGroupInfo, hegi, groupSecrets, hgs, groupSecrets', rfl, rfl⟩ := h
  have hegiPub := encryptGroupInfo_proof tr _ _ _ _ hegi hjoiner hgi hpsks
  have hpskIds: PskIdsGood tr (psks.map Prod.fst) := by
    simpa [PskIdsGood] using hpsks.1
  have := encryptGroupSecrets_proof tr me _ _ _ _ rand _ hgs hegiPub hkps hev hps hjoinerLabel hpskIds hrand hinv
  simp only [Welcome.mf.wf_eq]
  exact ⟨this, hegiPub⟩

end GroupInfo

end MLS.Bootstrap
