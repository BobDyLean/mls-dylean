/-
  Port of the `kdf_extract` part of the KDF section of `DY.Core.Bytes`.

  Compared to `DY.EquationalTheory.KdfExtract` in DyLean,
  the result of `kdfExtract` has the usage `KdfExpandKey "KDF.ExtractedKey" (literal_to_bytes Seq.empty)`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.EquationalTheory.Literal
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.KdfExtract

public
class CanKdfExtract (Bytes: Type u) where
  /-- Port of `kdf_extract`. -/
  kdfExtract: (salt: Bytes) → (ikm: Bytes) → Bytes

export CanKdfExtract (kdfExtract)

section Constructors

namespace KdfExtract

/-- Port of `KdfExtract`. -/
public
structure SubF (Bytes: Type) where
  salt: Bytes
  ikm: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {salt, ikm} => sizeOf salt + sizeOf ikm

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {salt, ikm} => {
    id := ()
    data := ()
    as := #v[salt, ikm]
  }
  fromRepr
  | {id, data, as} =>
    let salt := as[0]
    let ikm := as[1]
    { salt, ikm }
  from_to | {salt, ikm} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {salt, ikm} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end KdfExtract

#combine into BytesFunctor, BytesLength from
  KdfExtract

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev KdfExtract.SubF.pack (x: KdfExtract.SubF Bytes) := BytesView.pack x

public
instance: CanKdfExtract Bytes where
  kdfExtract salt ikm := ({salt, ikm}: KdfExtract.SubF Bytes).pack

@[simp]
public
theorem length_kdfExtract
  [BytesLength] [BytesLength.Has SubF.length]
  (salt ikm: Bytes)
  : Bytes.length (kdfExtract salt ikm) = 32
:= by
  simp only [kdfExtract]
  grind [KdfExtract.SubF.length]

end Constructors

section AttackerKnowledge

public
def kdfExtract.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ salt ikm,
      out = kdfExtract salt ikm ∧
      p salt ∧
      p ikm

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kdfExtract

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_kdfExtract
  (salt ikm: Bytes) (tr: ExecTrace)
  : salt.AttackerKnows tr →
    ikm.AttackerKnows tr →
    (kdfExtract salt ikm).AttackerKnows tr
:= by
  intro h_salt h_ikm
  apply Bytes.AttackerKnows.prove kdfExtract.attackerKnowledge
  simp only [kdfExtract.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has DY.Literal.SubF]

/-- The usage of the result of `kdfExtract` (`KdfExpandKey "KDF.ExtractedKey" (literal_to_bytes Seq.empty)` in DY*). -/
@[expose]
public
def extractedKeyUsage: Usage :=
  Usage.kdfExpandKey "KDF.ExtractedKey" (DY.Literal.literalToBytes ByteArray.empty)

public
def KdfExtract.invariants: Bytes.PartialInvariants KdfExtract.SubF where
  well_formed := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

  usage := fun {salt := _, ikm := _} _rec _tr =>
    extractedKeyUsage

  label := fun {salt, ikm} rec tr =>
    Label.meet ((rec salt) tr) ((rec ikm) tr)

  invariant := fun {salt, ikm} rec tr =>
    (rec salt) tr ∧ (rec ikm) tr

public
theorem KdfExtract.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs KdfExtract.invariants where

end Definition

#combine [BytesFunctor.Has DY.Literal.SubF] into
  BytesInvariants,
  BytesInvariantsProofs
from
  KdfExtract

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has DY.Literal.SubF]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_kdf_extract`. -/
@[simp]
public
theorem kdfExtract.WellFormed
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).WellFormed tr = (salt.WellFormed tr ∧ ikm.WellFormed tr)
:= by
  simp [kdfExtract, Bytes.WellFormed.eq, KdfExtract.invariants]

/-- Port of `get_label_kdf_extract`. -/
@[simp]
public
theorem kdfExtract.label
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).label tr = Label.meet (salt.label tr) (ikm.label tr)
:= by
  simp [kdfExtract, Bytes.label.eq, KdfExtract.invariants]

/-- Port of `has_usage_kdf_extract`. -/
public
theorem kdfExtract.HasUsage
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).HasUsage extractedKeyUsage tr
:= by
  simp [kdfExtract, Bytes.HasUsage, Bytes.usage.eq, KdfExtract.invariants]

grind_pattern kdfExtract.HasUsage => (kdfExtract salt ikm).HasUsage extractedKeyUsage tr

/-- Port of `bytes_invariant_kdf_extract`. -/
@[simp]
public
theorem kdfExtract.Invariant
  (salt ikm: Bytes) (tr: ProofTrace)
  : (kdfExtract salt ikm).Invariant tr = (salt.Invariant tr ∧ ikm.Invariant tr)
:= by
  simp [kdfExtract, Bytes.Invariant.eq, KdfExtract.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF] [BytesFunctor.Has DY.Literal.SubF]
variable [BytesInvariants.Has invariants]

/-- Port of `kdf_extract_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem kdfExtract.attackerKnowledge where
  pf := by
    simp only [kdfExtract.attackerKnowledge]
    intro out tr h_tr ⟨salt, ikm, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesFunctor.Has DY.Literal.SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kdfExtract

end AttackerKnowledgeTheorem

end DySlop.KdfExtract
