/-
  Port of the `kdf_expand` part of the KDF section of `DY.Core.Bytes`.

  Compared to `DY.EquationalTheory.KdfExpand` in DyLean:
  - the usage and label of `kdfExpand prk info len` are only given by `KdfExpandUsage`
    when `prk` has a `KdfExpandKey` usage (otherwise, they are `Usage.nothing` and the label of `prk`),
  - the invariant requires `prk` to have a `KdfExpandKey` usage (or to be public),
  - the attacker can shorten the output of `kdfExpand` (`kdfExpandShorter.attackerKnowledge`).

  DY* requires `len <> 0`; here, `len` is any natural number.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.KdfExpand

public
class CanKdfExpand (Bytes: Type u) where
  /-- Port of `kdf_expand`. -/
  kdfExpand: (prk: Bytes) → (info: Bytes) → (len: Nat) → Bytes

export CanKdfExpand (kdfExpand)

section Constructors

namespace KdfExpand

/-- Port of `KdfExpand`. -/
public
structure SubF (Bytes: Type) where
  prk: Bytes
  info: Bytes
  len: Nat

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {prk, info, ..} => sizeOf prk + sizeOf info

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Nat, nRec := 2 }

  toRepr | {prk, info, len} => {
    id := ()
    data := len
    as := #v[prk, info]
  }
  fromRepr
  | {id, data, as} =>
    let prk := as[0]
    let info := as[1]
    let len := data
    { prk, info, len }
  from_to | {prk, info, len} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {prk, info, len} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { len, .. } _ =>
    len

end KdfExpand

#combine into BytesFunctor, BytesLength from
  KdfExpand

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev KdfExpand.SubF.pack (x: KdfExpand.SubF Bytes) := BytesView.pack x

public
instance: CanKdfExpand Bytes where
  kdfExpand prk info len := ({prk, info, len}: KdfExpand.SubF Bytes).pack

@[simp]
public
theorem length_kdfExpand
  [BytesLength] [BytesLength.Has SubF.length]
  (prk info: Bytes) (len: Nat)
  : Bytes.length (kdfExpand prk info len) = len
:= by
  simp only [kdfExpand]
  grind [KdfExpand.SubF.length]

end Constructors

section AttackerKnowledge

public
def kdfExpand.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ prk info len,
      out = kdfExpand prk info len ∧
      p prk ∧
      p info

public
def kdfExpandShorter.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ prk info len1 len2,
      len1 ≤ len2 ∧
      out = kdfExpand prk info len1 ∧
      p (kdfExpand prk info len2)
  pred_isMonotonic := by
    simp only [Fixpoint.IsMonotonic]
    intro set1 set2 h out ⟨prk, info, len1, len2, h_len, h_out, h_p⟩
    exact ⟨prk, info, len1, len2, h_len, h_out, h _ h_p⟩

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kdfExpand,
  kdfExpandShorter

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_kdfExpand
  (prk info: Bytes) (len: Nat) (tr: ExecTrace)
  : prk.AttackerKnows tr →
    info.AttackerKnows tr →
    (kdfExpand prk info len).AttackerKnows tr
:= by
  intro h_prk h_info
  apply Bytes.AttackerKnows.prove kdfExpand.attackerKnowledge
  simp only [kdfExpand.attackerKnowledge]
  grind

public
theorem attacker_knows_kdfExpand_shorter
  (prk info: Bytes) (len1 len2: Nat) (tr: ExecTrace)
  : len1 ≤ len2 →
    (kdfExpand prk info len2).AttackerKnows tr →
    (kdfExpand prk info len1).AttackerKnows tr
:= by
  intro h_len h_out
  apply Bytes.AttackerKnows.prove kdfExpandShorter.attackerKnowledge
  simp only [kdfExpandShorter.attackerKnowledge]
  exact ⟨prk, info, len1, len2, h_len, rfl, h_out⟩

end AttackerKnowledge

section Invariants

section Definition

/--
  Port of `kdf_expand_crypto_usage`.
  DY* requires `KdfExpandKey? prk_usage`; here, `getUsage` and `getLabel` are defined on all usages.
-/
public
class KdfExpandUsage [ExecTraceTypes] [BytesFunctor] where
  /-- HKDF.Expand is a more standard PRF to derive several keys from an initial one,
  therefore we know that `prk` must have the correct usage.
  In particular, it cannot be used to mix two secrets.
  Note that the usage and the label do not depend on the `len` argument,
  because `HKDF.Expand prk info len` is a prefix of `HKDF.Expand prk info (len+k)`.

  The usage of HKDF.Expand depends on the prk usage and the info content. -/
  getUsage (prkUsage: Usage) (info: Bytes): Usage
  /-- The label of HKDF.Expand depends on the prk usage and label and the info content. -/
  getLabel (prkUsage: Usage) (prkLabel: Label) (info: Bytes): Label
  /-- The label of HKDF.Expand cannot be too secret. -/
  getLabel_lemma (tr: ExecTrace) (prkUsage: Usage) (prkLabel: Label) (info: Bytes)
    : prkUsage.type = "KdfExpandKey" →
      (getLabel prkUsage prkLabel info).canFlow prkLabel tr

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/-- Port of `default_kdf_expand_crypto_usage`. -/
@[instance_reducible]
public
def KdfExpandUsage.default: KdfExpandUsage where
  getUsage _ _ := Usage.nothing
  getLabel _ prkLabel _ := prkLabel
  getLabel_lemma := by grind

public
def KdfExpand.invariants [KdfExpandUsage] : Bytes.PartialInvariants KdfExpand.SubF where
  well_formed := fun {prk, info, len := _} rec tr =>
    (rec prk) tr ∧ (rec info) tr

  usage := fun {prk, info, len := _} rec tr =>
    if ((rec prk) tr).type = "KdfExpandKey" then
      KdfExpandUsage.getUsage ((rec prk) tr) info
    else
      Usage.nothing

  label := fun {prk, info, len := _} rec tr =>
    if (prk.usage tr).type = "KdfExpandKey" then
      KdfExpandUsage.getLabel (prk.usage tr) ((rec prk) tr) info
    else
      (rec prk) tr

  invariant := fun {prk, info, len := _} rec tr =>
    (rec prk) tr ∧
    (rec info) tr ∧
    (
      (
        ∃ prkUsg,
        -- Honest case:
        -- the prk has correct usage
        prk.HasUsage prkUsg tr ∧
        prkUsg.type = "KdfExpandKey"
      ) ∨ (
        -- Attacker case:
        -- the attacker knows prk
        (prk.label tr).canFlow Label.pub tr.erase
      )
    )

public
theorem KdfExpand.invariantsProofs [BytesInvariants] [KdfExpandUsage]: Bytes.PartialInvariantsProofs KdfExpand.invariants where

end Definition

#combine [KdfExpandUsage] into
  BytesInvariants,
  BytesInvariantsProofs
from
  KdfExpand

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [KdfExpandUsage]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_kdf_expand`. -/
@[simp]
public
theorem kdfExpand.WellFormed
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : (kdfExpand prk info len).WellFormed tr = (prk.WellFormed tr ∧ info.WellFormed tr)
:= by
  simp [kdfExpand, Bytes.WellFormed.eq, KdfExpand.invariants]

/-- Port of `bytes_invariant_kdf_expand`. -/
public
theorem kdfExpand.Invariant
  (prk: Bytes) (prkUsage: Usage) (info: Bytes) (len: Nat) (tr: ProofTrace)
  : prk.Invariant tr →
    info.Invariant tr →
    prk.HasUsage prkUsage tr →
    prkUsage.type = "KdfExpandKey" →
    (kdfExpand prk info len).Invariant tr
:= by
  simp only [kdfExpand, Bytes.Invariant.eq, KdfExpand.invariants]
  grind

grind_pattern kdfExpand.Invariant => (kdfExpand prk info len).Invariant tr, prk.HasUsage prkUsage tr

/-- Port of `has_usage_kdf_expand`. -/
public
theorem kdfExpand.HasUsage
  (prk: Bytes) (prkUsage: Usage) (info: Bytes) (len: Nat) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    prkUsage.type = "KdfExpandKey" →
    (kdfExpand prk info len).HasUsage (KdfExpandUsage.getUsage prkUsage info) tr
:= by
  have := KdfExpandUsage.getLabel_lemma tr.erase (prk.usage tr) (prk.label tr) info
  simp [Bytes.HasUsage, kdfExpand, Bytes.label.eq, Bytes.usage.eq, KdfExpand.invariants]
  grind [canFlowTrans]

grind_pattern kdfExpand.HasUsage =>
  (kdfExpand prk info len).HasUsage (KdfExpandUsage.getUsage prkUsage info) tr,
  prk.HasUsage prkUsage tr

/-- Port of `get_label_kdf_expand`. -/
public
theorem kdfExpand.label_equivalent
  (prk: Bytes) (prkUsage: Usage) (info: Bytes) (len: Nat) (tr: ProofTrace)
  : prk.HasUsage prkUsage tr →
    prkUsage.type = "KdfExpandKey" →
    ((kdfExpand prk info len).label tr).equivalent (KdfExpandUsage.getLabel prkUsage (prk.label tr) info) tr.erase
:= by
  have := KdfExpandUsage.getLabel_lemma tr.erase (prk.usage tr) (prk.label tr) info
  have := KdfExpandUsage.getLabel_lemma tr.erase prkUsage (prk.label tr) info
  simp [Bytes.HasUsage, kdfExpand, Bytes.label.eq, KdfExpand.invariants]
  grind [canFlowTrans]

grind_pattern kdfExpand.label_equivalent =>
  (kdfExpand prk info len).label tr,
  prk.HasUsage prkUsage tr

/-- Port of `get_label_kdf_expand_can_flow`. -/
public
theorem kdfExpand.label_canFlow
  (prk info: Bytes) (len: Nat) (tr: ProofTrace)
  : ((kdfExpand prk info len).label tr).canFlow (prk.label tr) tr.erase
:= by
  have := KdfExpandUsage.getLabel_lemma tr.erase (prk.usage tr) (prk.label tr) info
  simp [kdfExpand, Bytes.label.eq, KdfExpand.invariants]
  grind

grind_pattern kdfExpand.label_canFlow => (kdfExpand prk info len).label tr

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [KdfExpandUsage]
variable [BytesInvariants.Has invariants]

/-- Port of `kdf_expand_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem kdfExpand.attackerKnowledge where
  pf := by
    simp only [kdfExpand.attackerKnowledge]
    intro out tr h_tr ⟨prk, info, len, ⟨ h_out, h_prk, h_info ⟩⟩
    subst h_out
    have := kdfExpand.label_canFlow prk info len tr
    simp only [Bytes.Publishable, kdfExpand, Bytes.Invariant.eq, KdfExpand.invariants] at *
    grind [canFlowTrans]

/-- Port of `kdf_expand_shorter_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem kdfExpandShorter.attackerKnowledge where
  pf := by
    simp only [kdfExpandShorter.attackerKnowledge]
    intro out tr h_tr ⟨prk, info, len1, len2, ⟨ _, h_out, h_pub ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable, kdfExpand, Bytes.Invariant.eq, Bytes.label.eq, KdfExpand.invariants]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [KdfExpandUsage] [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kdfExpand,
  kdfExpandShorter

end AttackerKnowledgeTheorem

end DySlop.KdfExpand
