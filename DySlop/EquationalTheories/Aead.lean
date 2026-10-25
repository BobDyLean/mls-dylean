/-
  Port of the AEAD section of `DY.Core.Bytes`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.Aead

public
class CanAead (Bytes: Type u) where
  /-- Port of `aead_enc`. -/
  aeadEnc: (key: Bytes) → (nonce: Bytes) → (msg: Bytes) → (ad: Bytes) → Bytes
  /-- Port of `aead_dec`. -/
  aeadDec: (key: Bytes) → (nonce: Bytes) → (msg: Bytes) → (ad: Bytes) → Option Bytes

export CanAead (aeadEnc)
export CanAead (aeadDec)

section Constructors

namespace AeadEnc

/-- Port of `AeadEnc`. -/
public
structure SubF (Bytes: Type) where
  key: Bytes
  nonce: Bytes
  msg: Bytes
  ad: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {key, nonce, msg, ad} => sizeOf key + sizeOf nonce + sizeOf msg + sizeOf ad

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 4 }

  toRepr | {key, nonce, msg, ad} => {
    id := ()
    data := ()
    as := #v[key, nonce, msg, ad]
  }
  fromRepr
  | {id, data, as} =>
    let key := as[0]
    let nonce := as[1]
    let msg := as[2]
    let ad := as[3]
    { key, nonce, msg, ad }
  from_to | {key, nonce, msg, ad} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {key, nonce, msg, ad} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { key := _, nonce := _, msg, ad := _ } rec =>
    16 + rec msg

end AeadEnc

#combine into BytesFunctor, BytesLength from
  AeadEnc

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev AeadEnc.SubF.pack (x: AeadEnc.SubF Bytes) := BytesView.pack x

public
instance: CanAead Bytes where
  aeadEnc key nonce msg ad :=
    ({key, nonce, msg, ad}: AeadEnc.SubF Bytes).pack

  aeadDec key nonce msg ad :=
    match msg.view? AeadEnc.SubF with
    | some { key := key', nonce := nonce', msg := res, ad := ad' } =>
      if key = key' ∧ nonce = nonce' ∧ ad = ad' then
        some res
      else
        none
    | none => none

/-- Port of `aead_dec_enc`. -/
public
theorem aead_dec_enc
  (key nonce msg ad: Bytes)
  : aeadDec key nonce (aeadEnc key nonce msg ad) ad = some msg
:= by
  simp only [aeadDec, aeadEnc]
  grind

@[simp]
public
theorem length_aeadEnc
  [BytesLength] [BytesLength.Has SubF.length]
  (key nonce msg ad: Bytes)
  : Bytes.length (aeadEnc key nonce msg ad) = 16 + Bytes.length msg
:= by
  simp only [aeadEnc]
  grind [AeadEnc.SubF.length]

end Constructors

section AttackerKnowledge

public
def aeadEnc.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key nonce msg ad,
      out = aeadEnc key nonce msg ad ∧
      p key ∧
      p nonce ∧
      p msg ∧
      p ad

public
def aeadDec.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key nonce msg ad,
      some out = aeadDec key nonce msg ad ∧
      p key ∧
      p nonce ∧
      p msg ∧
      p ad

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  aeadEnc,
  aeadDec

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_aeadEnc
  (key nonce msg ad: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    ad.AttackerKnows tr →
    (aeadEnc key nonce msg ad).AttackerKnows tr
:= by
  intro h_key h_nonce h_msg h_ad
  apply Bytes.AttackerKnows.prove aeadEnc.attackerKnowledge
  simp only [aeadEnc.attackerKnowledge]
  grind

public
theorem attacker_knows_aeadDec
  (key nonce msg ad: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    ad.AttackerKnows tr →
    match aeadDec key nonce msg ad with
    | none => True
    | some res => res.AttackerKnows tr
:= by
  intro h_key h_nonce h_msg h_ad
  split
  · trivial
  apply Bytes.AttackerKnows.prove aeadDec.attackerKnowledge
  simp only [aeadDec.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  Port of `aead_crypto_predicate`.
  DY* requires `AeadKey? key_usage`; here, the predicate is defined on all usages.
-/
public
class AeadPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → (keyUsage: Usage) → (key nonce msg ad: Bytes) → ProofTrace → Prop

/-- Port of `aead_crypto_predicate.pred_later`. -/
public
class AeadPredProof [BytesInvariants] [AeadPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg key nonce msg ad tr1 tr2,
      key.WellFormed tr1 →
      nonce.WellFormed tr1 →
      msg.WellFormed tr1 →
      ad.WellFormed tr1 →
      tr1 ≤ tr2 →
      AeadPred.pred keyUsg key nonce msg ad tr1 →
      AeadPred.pred keyUsg key nonce msg ad tr2

grind_pattern AeadPredProof.pred_later => tr1 ≤ tr2, AeadPred.pred keyUsg key nonce msg ad tr1

public
theorem AeadPredProof.pred_later_fast
  [BytesInvariants] [AeadPred] [AeadPredProof] [BytesInvariantsProofs]
  (keyUsg: Usage) (key nonce msg ad: Bytes) (tr1 tr2: ProofTrace)
  : key.Invariant tr1 →
    nonce.Invariant tr1 →
    msg.Invariant tr1 →
    ad.Invariant tr1 →
    tr1 ≤ tr2 →
    AeadPred.pred keyUsg key nonce msg ad tr1 →
    AeadPred.pred keyUsg key nonce msg ad tr2
:= by grind

grind_pattern [grind_later] AeadPredProof.pred_later_fast => tr1 ≤ tr2, AeadPred.pred keyUsg key nonce msg ad tr1

public
def AeadEnc.invariants [AeadPred]: Bytes.PartialInvariants AeadEnc.SubF where
  well_formed := fun {key, nonce, msg, ad} rec tr =>
    (rec key) tr ∧
    (rec nonce) tr ∧
    (rec msg) tr ∧
    (rec ad) tr

  usage := fun {key := _, nonce := _, msg := _, ad := _} _rec _tr =>
    Usage.nothing

  label := fun {key := _, nonce := _, msg := _, ad := _} _rec _tr =>
    Label.pub

  invariant := fun {key, nonce, msg, ad} rec tr =>
    (rec key) tr ∧
    (rec nonce) tr ∧
    (rec msg) tr ∧
    (rec ad) tr ∧
    -- the nonce is a public value
    -- (e.g. it is often transmitted on the network)
    (nonce.label tr).canFlow Label.pub tr.erase ∧
    -- the standard IND-CCA assumption do not guarantee indistinguishability of additional data,
    -- hence it must flow to public
    (ad.label tr).canFlow Label.pub tr.erase ∧
    (
      (
        ∃ keyUsg,
        -- Honest case:
        -- - the key has the usage of AEAD key
        key.HasUsage keyUsg tr ∧
        keyUsg.type = "AeadKey" ∧
        -- - the custom (protocol-specific) invariant hold (authentication)
        AeadPred.pred keyUsg key nonce msg ad tr ∧
        -- - the message is less secret than the key
        --   (this is crucial so that decryption preserve publishability)
        (msg.label tr).canFlow (key.label tr) tr.erase
      ) ∨ (
        -- Attacker case:
        -- the key and message are both public
        (key.label tr).canFlow Label.pub tr.erase ∧
        (msg.label tr).canFlow Label.pub tr.erase
      )
    )

public
theorem AeadEnc.invariantsProofs [BytesInvariants] [AeadPred] [AeadPredProof]: Bytes.PartialInvariantsProofs AeadEnc.invariants where

end Definition

#combine [AeadPred] into
  BytesInvariants,
  BytesInvariantsProofs [AeadPredProof]
from
  AeadEnc

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [AeadPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_aead_enc`. -/
@[simp]
public
theorem aeadEnc.WellFormed
  (key nonce msg ad: Bytes) (tr: ProofTrace)
  : (aeadEnc key nonce msg ad).WellFormed tr = (
      key.WellFormed tr ∧
      nonce.WellFormed tr ∧
      msg.WellFormed tr ∧
      ad.WellFormed tr
    )
:= by
  simp [aeadEnc, Bytes.WellFormed.eq, AeadEnc.invariants]

/-- Port of `bytes_well_formed_aead_dec`. -/
public
theorem aeadDec.WellFormed
  (key nonce msg ad: Bytes) (tr: ProofTrace)
  : match aeadDec key nonce msg ad with
    | none => True
    | some plaintext =>
      msg.WellFormed tr = (
        key.WellFormed tr ∧
        nonce.WellFormed tr ∧
        plaintext.WellFormed tr ∧
        ad.WellFormed tr
      )
:= by
  split
  · trivial
  rename_i plaintext heq
  simp only [aeadDec] at heq
  split at heq
  · rename_i key' nonce' res ad' _
    obtain rfl: msg = ({key := key', nonce := nonce', msg := res, ad := ad'}: AeadEnc.SubF Bytes).pack := by grind
    simp_all [AeadEnc.invariants]
  · simp at heq

/-- Port of `get_label_aead_enc`. -/
@[simp]
public
theorem aeadEnc.label
  (key nonce msg ad: Bytes) (tr: ProofTrace)
  : (aeadEnc key nonce msg ad).label tr = Label.pub
:= by
  simp [aeadEnc, Bytes.label.eq, AeadEnc.invariants]

/-- Port of `bytes_invariant_aead_enc`. -/
public
theorem aeadEnc.Invariant
  (key: Bytes) (keyUsg: Usage) (nonce msg ad: Bytes) (tr: ProofTrace)
  : key.Invariant tr →
    nonce.Invariant tr →
    msg.Invariant tr →
    ad.Invariant tr →
    (nonce.label tr).canFlow Label.pub tr.erase →
    (ad.label tr).canFlow Label.pub tr.erase →
    (msg.label tr).canFlow (key.label tr) tr.erase →
    key.HasUsage keyUsg tr →
    (
      (
        keyUsg.type = "AeadKey" ∧
        AeadPred.pred keyUsg key nonce msg ad tr
      ) ∨ (
        (key.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (aeadEnc key nonce msg ad).Invariant tr
:= by
  simp [aeadEnc, Bytes.Invariant.eq, AeadEnc.invariants]
  grind [canFlowTrans]

grind_pattern aeadEnc.Invariant => (aeadEnc key nonce msg ad).Invariant tr, key.HasUsage keyUsg tr

/-- Port of `bytes_invariant_aead_dec`. -/
public
theorem aeadDec.Invariant
  (key nonce msg ad: Bytes) (tr: ProofTrace)
  : key.Invariant tr →
    nonce.Invariant tr →
    msg.Invariant tr →
    ad.Invariant tr →
    match aeadDec key nonce msg ad with
    | none => True
    | some plaintext => (
      plaintext.KnowableBy (key.label tr) tr ∧
      (
        (
          ∀ keyUsg,
            key.HasUsage keyUsg tr →
            keyUsg.type = "AeadKey" →
            AeadPred.pred keyUsg key nonce plaintext ad tr
        ) ∨ (
          key.Publishable tr
        )
      )
    )
:= by
  intro h_key h_nonce h_msg h_ad
  split
  · trivial
  rename_i plaintext heq
  simp only [aeadDec] at heq
  split at heq
  · rename_i key' nonce' res ad' _
    obtain rfl: msg = ({key := key', nonce := nonce', msg := res, ad := ad'}: AeadEnc.SubF Bytes).pack := by grind
    have := fun usg1 usg2 => Bytes.HasUsage_inj key usg1 usg2 tr
    simp_all [Bytes.KnowableBy, Bytes.Publishable, AeadEnc.invariants]
    grind [canFlowTrans]
  · simp at heq

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [AeadPred]
variable [BytesInvariants.Has invariants]

/-- Port of `aead_enc_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem aeadEnc.attackerKnowledge where
  pf := by
    simp only [aeadEnc.attackerKnowledge]
    intro out tr h_tr ⟨key, nonce, msg, ad, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [aeadEnc, Bytes.Invariant.eq, AeadEnc.invariants]
    grind

/-- Port of `aead_dec_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem aeadDec.attackerKnowledge where
  pf := by
    simp only [aeadDec.attackerKnowledge]
    intro out tr h_tr ⟨key, nonce, msg, ad, ⟨ h_out, h_inputs ⟩⟩
    simp only [aeadDec] at h_out
    split at h_out
    · rename_i key' nonce' res ad' _
      obtain rfl: msg = ({key := key', nonce := nonce', msg := res, ad := ad'}: AeadEnc.SubF Bytes).pack := by grind
      simp_all [Bytes.Publishable, AeadEnc.invariants]
      grind [canFlowTrans]
    · simp at h_out

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [AeadPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  aeadEnc,
  aeadDec

end AttackerKnowledgeTheorem

end DySlop.Aead
