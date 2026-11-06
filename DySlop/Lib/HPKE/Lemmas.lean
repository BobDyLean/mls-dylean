/-
  Port of `DY.Lib.HPKE.Lemmas`: security theorems about HPKE, in a modular and reusable way.

  The proofs are parametrized by a global HPKE predicate `HpkePred` (DY*'s `hpke_crypto_predicate`),
  compiled to a local AEAD predicate (`aeadPred`), with a local KDF.Expand usage (`kdfExpandUsage`),
  both for the usage tag `"DY.Lib.HPKE"`: the protocol combines them with
  `#combine into AeadPred, AeadPredProof from DySlop.HPKE, ...` and `#combine into KdfExpandUsage from DySlop.HPKE, ...`,
  and the lemmas assume `[KdfExpandUsage.Has kdfExpandUsage] [AeadPred.Has aeadPred]` (DY*'s `has_hpke_invariants`).

  Proof sketch (as in DY*):
  - the shared secret is a `KdfExpandKey` with usage tag "DY.Lib.HPKE",
    whose usage data is the serialized HPKE usage (`InternalUsage`),
  - when the shared secret goes into KDF.Expand with `info`,
    we obtain an `AeadKey` with usage tag "DY.Lib.HPKE" whose usage data contains `info` and the HPKE usage
    (`AeadUsageData`, see `kdfExpandUsage`),
  - when encrypting or decrypting with AEAD, `plaintext` and `ad` are authenticated by AEAD,
    the HPKE usage and `info` are authenticated in the usage data of the AEAD key.
-/

module

public import DySlop.Lib.HPKE.Spec
public import DySlop.Lib.Crypto.KdfExpand.Split
public import DySlop.Lib.Crypto.AEAD.Split
import all DySlop.Lib.HPKE.Spec

open DY DY.Comparse
open DySlop.SplitFunction DySlop.KdfExpand DySlop.Aead

namespace DySlop.HPKE

section Types

variable [BytesFunctor]

/-- Port of `internal_hpke_usage`. -/
public
structure InternalUsage where
  usageTag: String
  usageData: Bytes

/-- Port of `hpke_aead_usage_data`. -/
public
structure AeadUsageData where
  hpkeUsg: InternalUsage
  info: Bytes

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `hpke_crypto_predicate` (without `pred_later`, see `HpkePred.Later`) and of `hpke_crypto_invariants`. -/
public
class HpkePred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → (usage: String × Bytes) → (msg info ad: Bytes) → ProofTrace → Prop

/-- Port of the `pred_later` field of `hpke_crypto_predicate`: the HPKE predicate `lpred` stays true when the trace grows. -/
@[expose, reducible]
public
def HpkePred.Later [BytesInvariants] (lpred: HpkePred): Prop :=
  [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
  ∀ usage msg info ad tr1 tr2,
    msg.WellFormed tr1 →
    info.WellFormed tr1 →
    ad.WellFormed tr1 →
    tr1 ≤ tr2 →
    HpkePred.pred (self := lpred) usage msg info ad tr1 →
    HpkePred.pred (self := lpred) usage msg info ad tr2

/-- The global HPKE predicate stays true when the trace grows. -/
public
class HpkePredProof [BytesInvariants] [hpkePred: HpkePred]: Prop where
  pred_later: hpkePred.Later

end Types

section Definitions

variable [HasHpkeBytes]

public
instance InternalUsage.ps: ParseableSerializeableNE InternalUsage := .make <|
  .triviallyIsomorphic (.prod .unboundedString .unboundedBytes)
    (fun ⟨usageTag, usageData⟩ => { usageTag, usageData })
    (fun { usageTag, usageData } => ⟨usageTag, usageData⟩)

public
instance AeadUsageData.ps: ParseableSerializeable AeadUsageData := .make <|
  .triviallyIsomorphic (.prod ParseableSerializeableNE.mf .bytes)
    (fun ⟨hpkeUsg, info⟩ => { hpkeUsg, info })
    (fun { hpkeUsg, info } => ⟨hpkeUsg, info⟩)

/-- The usage of the shared secret, for the HPKE usage `usg`. -/
public
def sharedSecretUsage (usg: String × Bytes): Usage :=
  Usage.kdfExpandKey "DY.Lib.HPKE" (serialize ({ usageTag := usg.1, usageData := usg.2 }: InternalUsage))

/-- Port of `mk_hpke_sk_usage`. -/
@[expose]
public
def mkHpkeSkUsage (usg: String × Bytes): Usage :=
  Usage.kemKey (sharedSecretUsage usg)

/-- Port of `mk_hpke_entropy_usage`. -/
@[expose]
public
def mkHpkeEntropyUsage (usg: String × Bytes): Usage :=
  Usage.kemNonce (sharedSecretUsage usg)

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `hpke_kdf_expand_usage`. -/
@[expose, instance_reducible]
public
def kdfExpandLocalUsage: KdfExpandUsage where
  getUsage prkUsage info :=
    match (parse info: Option LabeledExpandInfo), (prkUsage.data.bind parse: Option InternalUsage) with
    | some { label := "key", info, .. }, some hpkeUsg =>
      Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg, info }: AeadUsageData))
    | _, _ => Usage.nothing
  getLabel _ prkLabel info :=
    match (parse info: Option LabeledExpandInfo) with
    | some { label := "base_nonce", .. } => Label.pub
    | _ => prkLabel
  getLabel_lemma _ _ prkLabel info _ := by
    split <;> grind

omit [ProofTraceTypes] in
public
theorem kdfExpandLocalUsage_getUsage (prkUsage: Usage) (info: Bytes)
  : KdfExpandUsage.getUsage (self := kdfExpandLocalUsage) prkUsage info = (
      match (parse info: Option LabeledExpandInfo), (prkUsage.data.bind parse: Option InternalUsage) with
      | some { label := "key", info, .. }, some hpkeUsg =>
        Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg, info }: AeadUsageData))
      | _, _ => Usage.nothing
    )
:= rfl

omit [ProofTraceTypes] in
public
theorem kdfExpandLocalUsage_getLabel (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
  : KdfExpandUsage.getLabel (self := kdfExpandLocalUsage) prkUsage prkLabel info = (
      match (parse info: Option LabeledExpandInfo) with
      | some { label := "base_nonce", .. } => Label.pub
      | _ => prkLabel
    )
:= rfl

/-- Port of `hpke_kdf_expand_tag_and_usage`. -/
public
def kdfExpandUsage: KdfExpandUsage.Local ["DY.Lib.HPKE"] :=
  .single kdfExpandLocalUsage

/-- Port of `hpke_aead_pred`. -/
@[expose, instance_reducible]
public
def aeadLocalPred [HpkePred]: AeadPred where
  pred := fun [BytesWellFormed] [GetUsage] [GetLabel] keyUsage _ _ msg ad tr =>
    match (keyUsage.data.bind parse: Option AeadUsageData) with
    | some { hpkeUsg, info } =>
      info.WellFormed tr ∧ (
        (msg.label tr).canFlow Label.pub tr.erase ∨
        HpkePred.pred (hpkeUsg.usageTag, hpkeUsg.usageData) msg info ad tr
      )
    | none => False

theorem aeadLocalPred_pred [HpkePred] [BytesWellFormed] [GetUsage] [GetLabel]
  (keyUsage: Usage) (key nonce msg ad: Bytes) (tr: ProofTrace)
  : AeadPred.pred (self := aeadLocalPred) keyUsage key nonce msg ad tr = (
      match (keyUsage.data.bind parse: Option AeadUsageData) with
      | some { hpkeUsg, info } =>
        info.WellFormed tr ∧ (
          (msg.label tr).canFlow Label.pub tr.erase ∨
          HpkePred.pred (hpkeUsg.usageTag, hpkeUsg.usageData) msg info ad tr
        )
      | none => False
    )
:= rfl

/-- Port of `hpke_aead_tag_and_pred`. -/
public
def aeadPred [HpkePred]: AeadPred.Local ["DY.Lib.HPKE"] :=
  .single aeadLocalPred

/-- Port of the `pred_later` field of `hpke_aead_pred`. -/
public
theorem aeadPredProof [BytesInvariants] [HpkePred] [HpkePredProof]: AeadPred.LocalProof aeadPred :=
  .single fun keyUsg _ _ msg ad tr1 tr2 _ _ h_msg h_ad h_le h => by
    have := HpkePredProof.pred_later (hpkePred := inferInstance)
    rw [aeadLocalPred_pred] at h ⊢
    split at h <;> grind

end Definitions

/-- The predicates and bytes invariants used by the HPKE theorems (see `HasHpkeBytes`). -/
public
class HasHpkeInvariants extends HasHpkeBytes where
  [execTraceTypes: ExecTraceTypes]
  [proofTraceTypes: ProofTraceTypes]
  [kdfExpandUsage: KdfExpandUsage]
  [hpkePred: HpkePred]
  [aeadPred: AeadPred]
  [bytesInv: BytesInvariants]
  [bytesInv0: BytesInvariants.Has DY.Literal.invariants]
  [bytesInv1: BytesInvariants.Has DY.Concat.invariants]
  [bytesInv2: BytesInvariants.Has DySlop.Kem.invariants]
  [bytesInv3: BytesInvariants.Has DySlop.KdfExpand.invariants]
  [bytesInv4: BytesInvariants.Has DySlop.Aead.invariants]

attribute [reducible, scoped instance] HasHpkeInvariants.execTraceTypes
attribute [reducible, scoped instance] HasHpkeInvariants.proofTraceTypes
attribute [reducible, scoped instance] HasHpkeInvariants.kdfExpandUsage
attribute [reducible, scoped instance] HasHpkeInvariants.hpkePred
attribute [reducible, scoped instance] HasHpkeInvariants.aeadPred
attribute [reducible, scoped instance] HasHpkeInvariants.bytesInv
attribute [           scoped instance] HasHpkeInvariants.bytesInv0
attribute [           scoped instance] HasHpkeInvariants.bytesInv1
attribute [           scoped instance] HasHpkeInvariants.bytesInv2
attribute [           scoped instance] HasHpkeInvariants.bytesInv3
attribute [           scoped instance] HasHpkeInvariants.bytesInv4

section PublicKey

variable [BytesFunctor] [BytesFunctor.Has DySlop.Kem.SubF] [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `get_hpke_sk_label`. -/
public
noncomputable abbrev _root_.DY.Bytes.hpkeSkLabel [GetLabel] (pk: Bytes) (tr: ProofTrace): Label :=
  pk.kemSkLabel tr

/-- Port of `has_hpke_sk_usage`. -/
public
abbrev _root_.DY.Bytes.HpkeSkHasUsage [GetUsage] [GetLabel] (pk: Bytes) (usg: Usage) (tr: ProofTrace): Prop :=
  pk.KemSkHasUsage usg tr

end PublicKey

section Lemmas

variable [HasHpkeInvariants]

/-- `serialize_wf_lemma` for `LabeledExpandInfo`. -/
theorem LabeledExpandInfo.pred_serialize
  {τ: Type} (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: LabeledExpandInfo) (tr: τ)
  : pre x.info tr →
    pre (serialize x) tr
:= by
  intro h
  rw [IsWellFormed_FormatRel pre _ x tr (serialize_FormatRel x), IsWellFormed]
  show (Comparse.ExtensibleMessageFormat.triviallyIsomorphic
    (.prod .uint16 (.prod .unboundedString .bytes)) _ _ _ _: Comparse.ExtensibleMessageFormat Bytes LabeledExpandInfo).wf (pre · tr) x
  simpa using h

/-- The usage of the AEAD key. -/
theorem getUsage_key
  [h: KdfExpandUsage.Has kdfExpandUsage] (usg: String × Bytes) (info: Bytes)
  : KdfExpandUsage.getUsage (sharedSecretUsage usg) (serialize ({ len := 32, label := "key", info }: LabeledExpandInfo)) =
    Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg := ⟨usg.1, usg.2⟩, info }: AeadUsageData))
:= by
  rw [h.getUsage_eq _ _ rfl (by simp [sharedSecretUsage, Usage.kdfExpandKey])]
  unfold kdfExpandUsage
  rw [KdfExpandUsage.Local.getUsage_single (tag := "DY.Lib.HPKE") kdfExpandLocalUsage (sharedSecretUsage usg) _ rfl rfl]
  simp [kdfExpandLocalUsage_getUsage, sharedSecretUsage, Usage.kdfExpandKey]

/-- The label of the AEAD key. -/
theorem getLabel_key
  [h: KdfExpandUsage.Has kdfExpandUsage] (usg: String × Bytes) (prkLabel: Label) (len: UInt16) (info: Bytes)
  : KdfExpandUsage.getLabel (sharedSecretUsage usg) prkLabel (serialize ({ len, label := "key", info }: LabeledExpandInfo)) = prkLabel
:= by
  rw [h.getLabel_eq _ _ _ rfl (by simp [sharedSecretUsage, Usage.kdfExpandKey])]
  unfold kdfExpandUsage
  rw [KdfExpandUsage.Local.getLabel_single (tag := "DY.Lib.HPKE") kdfExpandLocalUsage (sharedSecretUsage usg) prkLabel _ rfl rfl]
  simp only [kdfExpandLocalUsage_getLabel, parse_serialize_inv]
  split <;> simp_all

/-- The label of the AEAD nonce. -/
theorem getLabel_baseNonce
  [h: KdfExpandUsage.Has kdfExpandUsage] (usg: String × Bytes) (prkLabel: Label) (len: UInt16) (info: Bytes)
  : KdfExpandUsage.getLabel (sharedSecretUsage usg) prkLabel (serialize ({ len, label := "base_nonce", info }: LabeledExpandInfo)) = Label.pub
:= by
  rw [h.getLabel_eq _ _ _ rfl (by simp [sharedSecretUsage, Usage.kdfExpandKey])]
  unfold kdfExpandUsage
  rw [KdfExpandUsage.Local.getLabel_single (tag := "DY.Lib.HPKE") kdfExpandLocalUsage (sharedSecretUsage usg) prkLabel _ rfl rfl]
  simp [kdfExpandLocalUsage_getLabel]

/-- The AEAD predicate for the AEAD key of HPKE. -/
theorem aeadPred_eq
  [h: AeadPred.Has aeadPred] [BytesWellFormed] [GetUsage] [GetLabel]
  (usg: String × Bytes) (info key nonce msg ad: Bytes) (tr: ProofTrace)
  : AeadPred.pred (Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg := ⟨usg.1, usg.2⟩, info }: AeadUsageData))) key nonce msg ad tr =
    (info.WellFormed tr ∧ ((msg.label tr).canFlow Label.pub tr.erase ∨ HpkePred.pred usg msg info ad tr))
:= by
  rw [h.pred_eq _ _ _ _ _ _ rfl (by simp [Usage.aeadKey])]
  unfold aeadPred
  rw [AeadPred.Local.pred_single (tag := "DY.Lib.HPKE") aeadLocalPred _ key nonce msg ad tr rfl rfl, aeadLocalPred_pred]
  simp [Usage.aeadKey]

end Lemmas

section Theorems

variable [HasHpkeInvariants]

/-- Port of `bytes_invariant_hpke_pk`. -/
public
theorem hpkePk.Invariant (sk: Bytes) (tr: ProofTrace)
  : (hpkePk sk).Invariant tr = sk.Invariant tr
:=
  DySlop.Kem.kemPk.Invariant sk tr

/-- Port of `get_label_hpke_pk`. -/
public
theorem hpkePk.label (sk: Bytes) (tr: ProofTrace)
  : (hpkePk sk).label tr = Label.pub
:=
  DySlop.Kem.kemPk.label sk tr

/-- Port of `has_hpke_sk_usage_hpke_pk`. -/
public
theorem HpkeSkHasUsage_hpkePk (sk: Bytes) (usg: Usage) (tr: ProofTrace)
  : (hpkePk sk).HpkeSkHasUsage usg tr = sk.HasUsage usg tr
:=
  Bytes.KemSkHasUsage_kemPk sk usg tr

/-- Port of `get_hpke_sk_label_hpke_pk`. -/
public
theorem hpkeSkLabel_hpkePk (sk: Bytes) (tr: ProofTrace)
  : (hpkePk sk).hpkeSkLabel tr = sk.label tr
:=
  Bytes.kemSkLabel_kemPk sk tr


/-- The AEAD key and nonce derived from a shared secret with the usage of an HPKE shared secret. -/
theorem labeledExpand_key_nonce
  [KdfExpandUsage.Has kdfExpandUsage]
  (ss info: Bytes) (usg: String × Bytes) (tr: ProofTrace)
  : ss.Invariant tr →
    info.Invariant tr →
    ss.HasUsage (sharedSecretUsage usg) tr →
    (labeledExpand ss "key" info 32).Invariant tr ∧
    (labeledExpand ss "key" info 32).HasUsage
      (Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg := ⟨usg.1, usg.2⟩, info }: AeadUsageData))) tr ∧
    ((labeledExpand ss "key" info 32).label tr).equivalent (ss.label tr) tr.erase ∧
    (labeledExpand ss "base_nonce" info 32).Invariant tr ∧
    ((labeledExpand ss "base_nonce" info 32).label tr).equivalent Label.pub tr.erase
:= by
  intro h_ss h_info h_usg
  have := LabeledExpandInfo.pred_serialize Bytes.Invariant { len := 32, label := "key", info } tr h_info
  have := LabeledExpandInfo.pred_serialize Bytes.Invariant { len := 32, label := "base_nonce", info } tr h_info
  have := getUsage_key usg info
  have := getLabel_key usg (ss.label tr) 32 info
  have := getLabel_baseNonce usg (ss.label tr) 32 info
  simp only [labeledExpand]
  grind [DySlop.KdfExpand.kdfExpand.HasUsage, DySlop.KdfExpand.kdfExpand.label_equivalent, sharedSecretUsage, Usage.kdfExpandKey]

/-- Port of `bytes_invariant_hpke_enc`. -/
public
theorem hpkeEnc.Invariant
  [BytesInvariantsProofs] [KdfExpandUsage.Has kdfExpandUsage] [AeadPred.Has aeadPred]
  (tr: ProofTrace) (pkR entropy msg info ad: Bytes) (usg: String × Bytes)
  : pkR.Invariant tr →
    entropy.Invariant tr →
    msg.Invariant tr →
    info.Invariant tr →
    ad.Publishable tr →
    -- the message must flow to the shared secret (derived from the entropy), a requirement of AEAD
    (msg.label tr).canFlow (entropy.label tr) tr.erase →
    -- the shared secret (derived from the entropy) must flow to the secret key, a requirement of KEM
    (entropy.label tr).canFlow (pkR.hpkeSkLabel tr) tr.erase →
    -- the entropy and public key must agree on the usage, or the entropy (hence shared secret) must be publishable:
    -- without this precondition, there could be cross-protocol attacks
    entropy.HasUsage (mkHpkeEntropyUsage usg) tr →
    (
      (
        pkR.HpkeSkHasUsage (mkHpkeSkUsage usg) tr ∧
        HpkePred.pred usg msg info ad tr
      ) ∨ (
        (entropy.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (hpkeEnc pkR entropy msg info ad).1.Publishable tr ∧
    (hpkeEnc pkR entropy msg info ad).2.Publishable tr
:= by
  intro h_pk h_entropy h_msg h_info h_ad h_msgFlow h_entropyFlow h_entropyUsg h_honest
  obtain ⟨h_enc, h_ss, h_ssLabel, h_ssUsg⟩ :=
    DySlop.Kem.kemEncap.Invariant pkR entropy (sharedSecretUsage usg) tr h_pk h_entropy h_entropyUsg (by grind [mkHpkeSkUsage])
  have := labeledExpand_key_nonce _ info usg tr h_ss h_info h_ssUsg
  have := aeadPred_eq usg info (labeledExpand (DySlop.Kem.kemEncap pkR entropy).2 "key" info 32)
    (labeledExpand (DySlop.Kem.kemEncap pkR entropy).2 "base_nonce" info 32) msg ad tr
  have := Bytes.Invariant_implies_WellFormed info tr h_info
  simp only [hpkeEnc, Bytes.Publishable, DySlop.Aead.aeadEnc.label] at *
  refine ⟨h_enc, ?_, Label.pubCanFlow _ _⟩
  apply DySlop.Aead.aeadEnc.Invariant _ (Usage.aeadKey "DY.Lib.HPKE" (serialize ({ hpkeUsg := ⟨usg.1, usg.2⟩, info }: AeadUsageData)))
  all_goals grind [canFlowTrans, Usage.aeadKey]

/--
  Port of `bytes_invariant_hpke_dec`.
  Instead of a `match` on the result of `hpkeDec`, it takes the plaintext and the proof that decryption succeeds.
-/
public
theorem hpkeDec.Invariant
  [KdfExpandUsage.Has kdfExpandUsage] [AeadPred.Has aeadPred]
  (tr: ProofTrace) (skR enc ciphertext info ad: Bytes) (usg: String × Bytes) (plaintext: Bytes)
  : hpkeDec skR (enc, ciphertext) info ad = some plaintext →
    skR.Invariant tr →
    skR.HasUsage (mkHpkeSkUsage usg) tr →
    enc.Invariant tr →
    ciphertext.Invariant tr →
    info.Invariant tr →
    ad.Invariant tr →
    plaintext.KnowableBy (skR.label tr) tr ∧
    (HpkePred.pred usg plaintext info ad tr ∨ plaintext.Publishable tr)
:= by
  intro h_dec h_sk h_skUsg h_enc h_ciphertext h_info h_ad
  have h_ssUsg := DySlop.Kem.kemDecap.HasUsage skR (sharedSecretUsage usg) enc tr h_sk h_enc h_skUsg
  have h_ssInv := DySlop.Kem.kemDecap.Invariant skR enc tr h_sk h_enc
  simp only [hpkeDec] at h_dec
  cases h_decap: DySlop.Kem.kemDecap skR enc with
  | none => simp [h_decap] at h_dec
  | some ss =>
    simp only [h_decap] at h_ssUsg h_ssInv h_dec
    obtain ⟨h_key, h_keyUsg, h_keyLabel, h_nonce, -⟩ := labeledExpand_key_nonce ss info usg tr h_ssInv.1 h_info h_ssUsg
    have h_aeadDec := DySlop.Aead.aeadDec.Invariant _ _ ciphertext ad tr h_key h_nonce h_ciphertext h_ad
    simp only [h_dec] at h_aeadDec
    have := aeadPred_eq usg info (labeledExpand ss "key" info 32) (labeledExpand ss "base_nonce" info 32) plaintext ad tr
    grind [canFlowTrans, Usage.aeadKey]

end Theorems

end DySlop.HPKE
