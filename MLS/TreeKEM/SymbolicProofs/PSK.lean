module

public import MLS.TreeKEM.Code.PSK
public import MLS.Common.SymbolicProofs.Crypto.Derived.ExpandWithLabel
public import DySlop.Lib.Label
public import MLS.Symbolic.SymbolicProofs.MiscLemmas

/-!
Port of `MLS.TreeKEM.Symbolic.PSK`: the labels of pre-shared keys, and the proofs of the computation of the PSK secret.

Port-specific differences:
- MLS*'s `has_mls_psk_invariants` is the class `HasMlsPskInvariants`, whose field is a scoped instance in `MLS.TreeKEM`.
- `for_allP p (List.Tot.map f l)` is `∀ x ∈ l, p (f x)`.
- MLS*'s `take` and `drop` are Lean's `List.take` and `List.drop`.
- `compute_psk_secret_step_cannot_be_zero_vector` (hence the injectivity lemmas) use the bytes invariants:
  DyLean's bytes functor is abstract, the zero vector and the result of `kdfExtract` are distinguished by their usages
  (`MLS.literalToBytes_ne_kdfExtract`).
- The labels of a list of PSKs are characterized by their corruption (`psksLabel_isCorrupt`):
  MLS*'s `psks_label_take_lemma` (an equality of labels) follows from it.
-/

namespace MLS.TreeKEM

open Comparse
open DY
open DySlop DySlop.KdfExpand
open MLS

/-! ## Invariants -/

section Invariants

variable [HasSymbolicBytes] [ExecTraceTypes]

/-- Port of `expand_usage_extractedkey_derivedpsk`. -/
@[expose]
public
def expandUsageExtractedkeyDerivedpsk: ExpandWithLabelUsage.Local ["derived psk"] :=
  .single (.secret (Usage.kdfExpandKey "MLS.DerivedPSK" BytesLike.empty))

end Invariants

section Invariants

variable [HasSymbolicInvariants]

/--
Port of `has_mls_psk_invariants`.
The field is a scoped instance in the namespace `MLS.TreeKEM`; the top-level protocol provides it
(`instance: HasMlsPskInvariants where`).
-/
public
class HasMlsPskInvariants: Prop where
  [derivedPsk: ExpandWithLabelUsage.Has "KDF.ExtractedKey" expandUsageExtractedkeyDerivedpsk]

attribute [scoped instance] HasMlsPskInvariants.derivedPsk

end Invariants

/-! ## Symbolic bytes -/

section SymbolicBytes

variable [HasSymbolicInvariants]

/-- The zero vector is publishable. -/
public
theorem zeroVector_publishable (tr: ProofTrace): (zeroVector: Bytes).Publishable tr :=
  BytesCompatiblePred.pred_fromByteArray (pred := (Bytes.Publishable · tr)) _

/-- The label of the zero vector is equivalent to `Label.pub`. -/
public
theorem zeroVector_label (tr: ProofTrace): ((zeroVector: Bytes).label tr).equivalent Label.pub tr.erase := by
  have := zeroVector_publishable tr
  grind [Bytes.Publishable]

/-- Publishable pre-shared key identifiers satisfy the bytes invariant. -/
public
theorem PreSharedKeyId.wf_invariant_of_publishable (tr: ProofTrace) (pskId: PreSharedKeyId Bytes)
  (h: PreSharedKeyId.mf.wf (Bytes.Publishable · tr) pskId):
  PreSharedKeyId.mf.wf (Bytes.Invariant · tr) pskId
:= by
  cases pskId <;> simp only [PreSharedKeyId.mf.wf_eq] at h ⊢ <;> grind

end SymbolicBytes

/-! ## Proofs -/

section Code

variable [HasSymbolicBytes]

theorem computePskSecretStep_eq_success (label: PskLabel Bytes) (psk prevPskSecret res: Bytes)
  (h: computePskSecretStep label psk prevPskSecret = .success res):
  ∃ pskInput,
    expandWithLabel (DySlop.KdfExtract.kdfExtract zeroVector psk) "derived psk" (serializeNE PskLabel.mf label) (CryptoBytes.kdfLength Bytes) =
      .success pskInput ∧
    res = DySlop.KdfExtract.kdfExtract pskInput prevPskSecret
:= by
  simp only [computePskSecretStep, Result.bind_eq_success, cryptoBytesBytes_kdfExtract] at h
  grind

end Code

section Proofs

variable [HasSymbolicInvariants] [HasMlsPskInvariants]

/-- Port of `compute_psk_secret_step_proof`. -/
public
theorem computePskSecretStep_proof (tr: ProofTrace) (label: PskLabel Bytes) (psk prevPskSecret: Bytes) (res: Bytes)
  (h: computePskSecretStep label psk prevPskSecret = .success res)
  (hlabel: PskLabel.mf.wf (Bytes.Invariant · tr) label) (hpsk: psk.Invariant tr) (hprev: prevPskSecret.Invariant tr):
  res.Invariant tr ∧ (res.label tr).equivalent ((prevPskSecret.label tr).meet (psk.label tr)) tr.erase
:= by
  obtain ⟨pskInput, hinput, rfl⟩ := computePskSecretStep_eq_success label psk prevPskSecret res h
  have hctx := (pred_serializeNE_iff PskLabel.mf (Bytes.Invariant · tr) label).2 hlabel
  have hzero := zeroVector_publishable tr
  obtain ⟨hinv, -, hlab⟩ := expandWithLabel.Invariant expandUsageExtractedkeyDerivedpsk "KDF.ExtractedKey" tr _
    DySlop.KdfExtract.extractedKeyUsage "derived psk" _ _ pskInput hinput (by simp [hzero.1, hpsk]) hctx
    (DySlop.KdfExtract.kdfExtract.HasUsage _ _ tr) rfl rfl (by simp)
  simp only [expandUsageExtractedkeyDerivedpsk, ExpandWithLabelUsage.Local.getLabel_single,
    ExpandWithLabelUsage.secret, DySlop.KdfExtract.kdfExtract.label] at hlab
  have := zeroVector_label tr
  simp only [DySlop.KdfExtract.kdfExtract.label]
  grind [Label.canFlow, DySlop.KdfExtract.kdfExtract.Invariant]

end Proofs

/-! ## Labels of the pre-shared keys -/

section PsksLabel

variable [HasSymbolicInvariants]

/-- Port of `psks_bytes_invariant`. -/
@[expose]
public
def PsksBytesInvariant (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)): Prop :=
  (∀ x ∈ l, PreSharedKeyId.mf.wf (Bytes.Publishable · tr) x.1) ∧
  ∀ x ∈ l, x.2.Invariant tr

/-- Port of `psks_bytes_invariant_later`. -/
public
theorem PsksBytesInvariant_later (tr1 tr2: ProofTrace) (psks: List (PreSharedKeyId Bytes × Bytes))
  : tr1 ≤ tr2 →
    PsksBytesInvariant tr1 psks →
    PsksBytesInvariant tr2 psks
:= by
  intro hle ⟨h1, h2⟩
  refine ⟨fun x hx => ?_, fun x hx => by grind⟩
  have := h1 x hx
  obtain ⟨pskId, psk⟩ := x
  cases pskId <;> simp only [PreSharedKeyId.mf.wf_eq] at this ⊢ <;> grind

grind_pattern PsksBytesInvariant_later => tr1 ≤ tr2, PsksBytesInvariant tr1 psks
grind_pattern [grind_later] PsksBytesInvariant_later => tr1 ≤ tr2, PsksBytesInvariant tr1 psks

/-- Port of `psks_label`. -/
@[expose]
public
def psksLabel (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)): Label :=
  (l.map (·.2.label tr)).foldr Label.meet Label.pub

/-- The label of a list of pre-shared keys is corrupt when all of them are. -/
public
theorem psksLabel_isCorrupt (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)) (tr': ExecTrace):
  (psksLabel tr l).isCorrupt tr' ↔ ∀ x ∈ l, (x.2.label tr).isCorrupt tr'
:= by
  induction l with
  | nil => simp [psksLabel]
  | cons h t ih =>
    simp only [psksLabel, List.map_cons, List.foldr_cons, Label.meetIsCorrupt, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]

/-- Port of `psks_label_later`. -/
public
theorem psksLabel_later (tr1 tr2: ProofTrace) (psks: List (PreSharedKeyId Bytes × Bytes))
  : PsksBytesInvariant tr1 psks →
    tr1 ≤ tr2 →
    psksLabel tr1 psks = psksLabel tr2 psks
:= by
  rintro ⟨-, h⟩ hle
  have: ∀ x ∈ psks, x.2.label tr1 = x.2.label tr2 :=
    fun x hx => Bytes.label_later _ _ _ hle (Bytes.Invariant_implies_WellFormed _ _ (h x hx))
  ext tr'
  simp only [psksLabel_isCorrupt]
  grind

grind_pattern psksLabel_later => psksLabel tr1 psks, tr1 ≤ tr2

/-- Port of `psks_label_nil`. -/
public
theorem psksLabel_nil (tr: ProofTrace): psksLabel tr [] = Label.pub := by
  simp [psksLabel]

/-- Port of `psks_label_take_lemma`. -/
theorem psksLabel_take_succ (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)) (i: Nat) (hi: i < l.length):
  (psksLabel tr (l.take i)).meet (l[i].2.label tr) = psksLabel tr (l.take (i+1))
:= by
  ext tr'
  simp only [Label.meetIsCorrupt, psksLabel_isCorrupt, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.mem_append, List.mem_singleton]
  grind

end PsksLabel

section ComputePskSecret

variable [HasSymbolicBytes]

theorem computePskSecretAux_lt (l: List (PreSharedKeyId Bytes × Bytes)) (ind: Nat) (pskSecretInd res: Bytes)
  (hind: ind < l.length) (h: computePskSecretAux l ind pskSecretInd = .success res):
  ∃ next,
    ind < 2^16 ∧ l.length < 2^16 ∧
    computePskSecretStep { id := l[ind].1, index := ind.toUInt16, count := l.length.toUInt16 } l[ind].2 pskSecretInd =
      .success next ∧
    computePskSecretAux l (ind+1) next = .success res
:= by
  rw [computePskSecretAux] at h
  simp only [hind, dite_true, Result.bind_eq_success, mkUInt16_eq_success] at h
  grind

theorem computePskSecretAux_ge (l: List (PreSharedKeyId Bytes × Bytes)) (ind: Nat) (pskSecretInd: Bytes)
  (hind: ¬ ind < l.length):
  computePskSecretAux l ind pskSecretInd = .success pskSecretInd
:= by
  rw [computePskSecretAux]
  simp [hind, pure]

end ComputePskSecret

section ComputePskSecretProof

variable [HasSymbolicInvariants] [HasMlsPskInvariants]

/-- Port of `compute_psk_secret_aux_proof`. -/
theorem computePskSecretAux_proof (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)) (ind: Nat)
  (pskSecretInd res: Bytes)
  (h: computePskSecretAux l ind pskSecretInd = .success res)
  (hl: PsksBytesInvariant tr l) (hs: pskSecretInd.Invariant tr)
  (hlabel: (pskSecretInd.label tr).equivalent (psksLabel tr (l.take ind)) tr.erase):
  res.Invariant tr ∧ (res.label tr).equivalent (psksLabel tr l) tr.erase
:= by
  by_cases hind: ind < l.length
  · obtain ⟨next, -, -, hstep, hrec⟩ := computePskSecretAux_lt l ind _ res hind h
    have hmem := List.getElem_mem hind
    obtain ⟨hnext, hnextLabel⟩ := computePskSecretStep_proof tr _ _ _ next hstep
      (by simpa using PreSharedKeyId.wf_invariant_of_publishable tr _ (hl.1 _ hmem)) (hl.2 _ hmem) hs
    apply computePskSecretAux_proof tr l (ind+1) next res hrec hl hnext
    rw [← psksLabel_take_succ tr l ind hind]
    grind [Label.canFlow]
  · rw [computePskSecretAux_ge l ind _ hind, Result.success.injEq] at h
    subst h
    rw [List.take_of_length_le (by omega)] at hlabel
    exact ⟨hs, hlabel⟩
termination_by l.length - ind

/-- Port of `compute_psk_secret_proof`. -/
public
theorem computePskSecret_proof (tr: ProofTrace) (l: List (PreSharedKeyId Bytes × Bytes)) (res: Bytes)
  (h: computePskSecret l = .success res) (hl: PsksBytesInvariant tr l):
  res.Invariant tr ∧ (res.label tr).equivalent (psksLabel tr l) tr.erase
:= by
  apply computePskSecretAux_proof tr l 0 _ res h hl (zeroVector_publishable tr).1
  simpa [psksLabel_nil] using zeroVector_label tr

end ComputePskSecretProof

/-! ## Injectivity -/

section Injectivity

variable [HasSymbolicBytes]

/-- Port of `compute_psk_secret_step_inj`. -/
public
theorem computePskSecretStep_inj (label1: PskLabel Bytes) (psk1 prevPskSecret1: Bytes)
  (label2: PskLabel Bytes) (psk2 prevPskSecret2: Bytes) (res: Bytes)
  (h1: computePskSecretStep label1 psk1 prevPskSecret1 = .success res)
  (h2: computePskSecretStep label2 psk2 prevPskSecret2 = .success res):
  label1 = label2 ∧ psk1 = psk2 ∧ prevPskSecret1 = prevPskSecret2
:= by
  obtain ⟨input1, hinput1, rfl⟩ := computePskSecretStep_eq_success label1 psk1 prevPskSecret1 _ h1
  obtain ⟨input2, hinput2, heq⟩ := computePskSecretStep_eq_success label2 psk2 prevPskSecret2 _ h2
  obtain ⟨rfl, rfl⟩ := kdfExtract_inj _ _ _ _ heq.symm
  obtain ⟨kdfLabel1, -, hctx1, -, rfl⟩ := expandWithLabel_eq_success _ _ _ _ _ hinput1
  obtain ⟨kdfLabel2, -, hctx2, -, heq⟩ := expandWithLabel_eq_success _ _ _ _ _ hinput2
  obtain ⟨hsecret, hinfo, -⟩ := kdfExpand_inj _ _ _ _ _ _ heq
  obtain ⟨-, rfl⟩ := kdfExtract_inj _ _ _ _ hsecret
  obtain rfl := serializeNE_injective KdfLabel.mf hinfo
  exact ⟨serializeNE_injective PskLabel.mf (hctx1.symm.trans hctx2), rfl, rfl⟩

end Injectivity

section InjectivityInvariants

variable [HasSymbolicInvariants]

/-- Port of `compute_psk_secret_step_cannot_be_zero_vector`. -/
theorem computePskSecretStep_ne_zeroVector (label: PskLabel Bytes) (psk prevPskSecret: Bytes)
  (h: computePskSecretStep label psk prevPskSecret = .success zeroVector):
  False
:= by
  obtain ⟨input, -, heq⟩ := computePskSecretStep_eq_success label psk prevPskSecret _ h
  exact literalToBytes_ne_kdfExtract _ _ _ heq

/-- Port of `compute_psk_secret_aux_inj`. MLS* requires `ind1 <= List.Tot.length l1` and `ind2 <= List.Tot.length l2`. -/
theorem computePskSecretAux_inj (l1: List (PreSharedKeyId Bytes × Bytes)) (ind1: Nat) (pskSecretInd1: Bytes)
  (l2: List (PreSharedKeyId Bytes × Bytes)) (ind2: Nat) (pskSecretInd2: Bytes) (res: Bytes)
  (h1: computePskSecretAux l1 ind1 pskSecretInd1 = .success res)
  (h2: computePskSecretAux l2 ind2 pskSecretInd2 = .success res)
  (hind1: ind1 ≤ l1.length) (hind2: ind2 ≤ l2.length)
  (hlt: l1.length - ind1 < l2.length - ind2 → ind1 = 0)
  (hgt: l1.length - ind1 > l2.length - ind2 → ind2 = 0)
  (hzero1: ind1 = 0 → pskSecretInd1 = zeroVector)
  (hzero2: ind2 = 0 → pskSecretInd2 = zeroVector):
  l1.drop ind1 = l2.drop ind2 ∧
  ((ind1 ≠ l1.length ∨ ind2 ≠ l2.length) → ind1 = ind2) ∧
  pskSecretInd1 = pskSecretInd2
:= by
  by_cases hrem: l1.length - ind1 = l2.length - ind2
  · by_cases hend: l1.length - ind1 = 0
    · -- both lists are fully processed
      rw [computePskSecretAux_ge l1 ind1 _ (by omega), Result.success.injEq] at h1
      rw [computePskSecretAux_ge l2 ind2 _ (by omega), Result.success.injEq] at h2
      refine ⟨by rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)], by omega, by grind⟩
    · -- one step on both lists
      obtain ⟨next1, hi1, hn1, hstep1, hrec1⟩ := computePskSecretAux_lt l1 ind1 _ res (by omega) h1
      obtain ⟨next2, hi2, hn2, hstep2, hrec2⟩ := computePskSecretAux_lt l2 ind2 _ res (by omega) h2
      obtain ⟨hdrop, -, rfl⟩ := computePskSecretAux_inj l1 (ind1+1) next1 l2 (ind2+1) next2 res hrec1 hrec2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨hlabel, hpsk, rfl⟩ := computePskSecretStep_inj _ _ _ _ _ _ next1 hstep1 hstep2
      simp only [PskLabel.mk.injEq] at hlabel
      obtain ⟨hid, hindex, -⟩ := hlabel
      obtain rfl: ind1 = ind2 := by grind [UInt16.toNat_ofNat_of_lt]
      refine ⟨?_, fun _ => rfl, rfl⟩
      have e1: l1.drop ind1 = l1[ind1] :: l1.drop (ind1+1) := List.drop_eq_getElem_cons (by omega)
      have e2: l2.drop ind1 = l2[ind1] :: l2.drop (ind1+1) := List.drop_eq_getElem_cons (by omega)
      rw [e1, e2, hdrop]
      grind
  · by_cases hlt': l1.length - ind1 < l2.length - ind2
    · -- one step on the longest list: its next secret is the zero vector, impossible
      obtain rfl := hlt hlt'
      obtain ⟨next2, -, -, hstep2, hrec2⟩ := computePskSecretAux_lt l2 ind2 _ res (by omega) h2
      obtain ⟨-, -, heq⟩ := computePskSecretAux_inj l1 0 pskSecretInd1 l2 (ind2+1) next2 res h1 hrec2
        (by omega) (by omega) (by omega) (by omega) hzero1 (by omega)
      rw [hzero1 rfl] at heq
      exact (computePskSecretStep_ne_zeroVector _ _ _ (heq ▸ hstep2)).elim
    · obtain rfl := hgt (by omega)
      obtain ⟨next1, -, -, hstep1, hrec1⟩ := computePskSecretAux_lt l1 ind1 _ res (by omega) h1
      obtain ⟨-, -, heq⟩ := computePskSecretAux_inj l1 (ind1+1) next1 l2 0 pskSecretInd2 res hrec1 h2
        (by omega) (by omega) (by omega) (by omega) (by omega) hzero2
      rw [hzero2 rfl] at heq
      exact (computePskSecretStep_ne_zeroVector _ _ _ (heq.symm ▸ hstep1)).elim
termination_by (l1.length - ind1) + (l2.length - ind2)

/-- Port of `compute_psk_secret_inj`. -/
public
theorem computePskSecret_inj (l1 l2: List (PreSharedKeyId Bytes × Bytes)) (res: Bytes)
  (h1: computePskSecret l1 = .success res) (h2: computePskSecret l2 = .success res):
  l1 = l2
:= by
  have := computePskSecretAux_inj l1 0 _ l2 0 _ res h1 h2 (by omega) (by omega) (by omega) (by omega)
    (fun _ => rfl) (fun _ => rfl)
  simpa using this.1

end InjectivityInvariants

end MLS.TreeKEM
