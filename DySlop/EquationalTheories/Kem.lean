/-
  Port of the KEM section of `DY.Core.Bytes`.

  The KEM usages `KemKey usg` and `KemNonce usg` are `Usage.kemKey usg` and `Usage.kemNonce usg`
  (see `DySlop.EquationalTheories.Common`).
  DY*'s `has_usage_kem_decap` requires `KemKey? sk_usg` and concludes with `KemKey?.usg sk_usg`;
  here, it takes `ssUsg` with `sk.HasUsage (Usage.kemKey ssUsg) tr`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.Kem

public
class CanKem (Bytes: Type u) where
  /-- Port of `kem_pk`. -/
  kemPk: (sk: Bytes) → Bytes
  /-- Port of `kem_encap`.
  Note that `KemSecretShared` does not include `pk`,
  this is to model a KEM that does not bind the shared secret to the public key.
  See https://eprint.iacr.org/2023/1933 for more information. -/
  kemEncap: (pk: Bytes) → (nonce: Bytes) → Bytes × Bytes
  /-- Port of `kem_decap`. -/
  kemDecap: (sk: Bytes) → (encap: Bytes) → Option Bytes

export CanKem (kemPk)
export CanKem (kemEncap)
export CanKem (kemDecap)

section Constructors

namespace KemPub

/-- Port of `KemPub`. -/
public
structure SubF (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {sk} => {
    id := ()
    data := ()
    as := #v[sk]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    { sk }
  from_to | {sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end KemPub

namespace KemEncap

/-- Port of `KemEncap`. -/
public
structure SubF (Bytes: Type) where
  pk: Bytes
  nonce: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pk, nonce} => sizeOf pk + sizeOf nonce

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {pk, nonce} => {
    id := ()
    data := ()
    as := #v[pk, nonce]
  }
  fromRepr
  | {id, data, as} =>
    let pk := as[0]
    let nonce := as[1]
    { pk, nonce }
  from_to | {pk, nonce} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pk, nonce} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end KemEncap

namespace KemSecretShared

/-- Port of `KemSecretShared`. -/
public
structure SubF (Bytes: Type) where
  nonce: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {nonce} => sizeOf nonce

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {nonce} => {
    id := ()
    data := ()
    as := #v[nonce]
  }
  fromRepr
  | {id, data, as} =>
    let nonce := as[0]
    { nonce }
  from_to | {nonce} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {nonce} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end KemSecretShared

#combine into BytesFunctor, BytesLength from
  KemPub,
  KemEncap,
  KemSecretShared

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev KemPub.SubF.pack (x: KemPub.SubF Bytes) := BytesView.pack x
public abbrev KemEncap.SubF.pack (x: KemEncap.SubF Bytes) := BytesView.pack x
public abbrev KemSecretShared.SubF.pack (x: KemSecretShared.SubF Bytes) := BytesView.pack x

public
instance: CanKem Bytes where
  kemPk sk :=
    ({sk}: KemPub.SubF Bytes).pack

  kemEncap pk nonce :=
    (({pk, nonce}: KemEncap.SubF Bytes).pack, ({nonce}: KemSecretShared.SubF Bytes).pack)

  kemDecap sk encap :=
    match encap.view? KemEncap.SubF with
    | some { pk, nonce } =>
      match pk.view? KemPub.SubF with
      | some { sk := sk' } =>
        if sk = sk' then
          some ({nonce}: KemSecretShared.SubF Bytes).pack
        else
          none
      | none => none
    | none => none

/-- Port of `kem_decap_encap`. -/
public
theorem kem_decap_encap
  (sk nonce: Bytes)
  : kemDecap sk (kemEncap (kemPk sk) nonce).1 = some (kemEncap (kemPk sk) nonce).2
:= by
  simp only [kemDecap, kemEncap, kemPk]
  grind

@[simp]
public
theorem length_kemPk
  [BytesLength] [BytesLength.Has SubF.length]
  (sk: Bytes)
  : Bytes.length (kemPk sk) = 32
:= by
  simp only [kemPk]
  grind [KemPub.SubF.length]

@[simp]
public
theorem length_kemEncap
  [BytesLength] [BytesLength.Has SubF.length]
  (pk nonce: Bytes)
  : Bytes.length (kemEncap pk nonce).1 = 32 ∧
    Bytes.length (kemEncap pk nonce).2 = 32
:= by
  simp only [kemEncap]
  grind [KemEncap.SubF.length, KemSecretShared.SubF.length]

end Constructors

section AttackerKnowledge

public
def kemPk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = kemPk sk ∧
      p sk

public
def kemEncapLeft.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk nonce rhs,
      (out, rhs) = kemEncap pk nonce ∧
      p pk ∧
      p nonce

public
def kemEncapRight.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk nonce lhs,
      (lhs, out) = kemEncap pk nonce ∧
      p pk ∧
      p nonce

public
def kemDecap.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk encap,
      some out = kemDecap sk encap ∧
      p sk ∧
      p encap

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kemPk,
  kemEncapLeft,
  kemEncapRight,
  kemDecap

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_kemPk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (kemPk sk).AttackerKnows tr
:= by
  intro h_sk
  apply Bytes.AttackerKnows.prove kemPk.attackerKnowledge
  simp only [kemPk.attackerKnowledge]
  grind

public
theorem attacker_knows_kemEncap
  (pk nonce: Bytes) (tr: ExecTrace)
  : pk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    (kemEncap pk nonce).1.AttackerKnows tr ∧
    (kemEncap pk nonce).2.AttackerKnows tr
:= by
  intro h_pk h_nonce
  constructor
  · apply Bytes.AttackerKnows.prove kemEncapLeft.attackerKnowledge
    simp only [kemEncapLeft.attackerKnowledge]
    exact ⟨pk, nonce, (kemEncap pk nonce).2, rfl, h_pk, h_nonce⟩
  · apply Bytes.AttackerKnows.prove kemEncapRight.attackerKnowledge
    simp only [kemEncapRight.attackerKnowledge]
    exact ⟨pk, nonce, (kemEncap pk nonce).1, rfl, h_pk, h_nonce⟩

public
theorem attacker_knows_kemDecap
  (sk encap: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    encap.AttackerKnows tr →
    match kemDecap sk encap with
    | none => True
    | some ss => ss.AttackerKnows tr
:= by
  intro h_sk h_encap
  split
  · trivial
  apply Bytes.AttackerKnows.prove kemDecap.attackerKnowledge
  simp only [kemDecap.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def KemPub.invariants: Bytes.PartialInvariants KemPub.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := _} _rec _tr =>
    Usage.nothing

  label := fun {sk := _} _rec _tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
theorem KemPub.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs KemPub.invariants where

end Definition

section KemPkLemmas

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has Kem.SubF]
variable [BytesInvariants] [BytesInvariants.Has KemPub.invariants]

/-- Port of `bytes_well_formed_kem_pk`. -/
@[simp]
public
theorem kemPk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  : (kemPk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [kemPk, Bytes.WellFormed.eq, KemPub.invariants]

/-- Port of `get_label_kem_pk`. -/
@[simp]
public
theorem kemPk.label
  (sk: Bytes) (tr: ProofTrace)
  : (kemPk sk).label tr = Label.pub
:= by
  simp [kemPk, Bytes.label.eq, KemPub.invariants]

/-- Port of `bytes_invariant_kem_pk`. -/
@[simp]
public
theorem kemPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : (kemPk sk).Invariant tr = sk.Invariant tr
:= by
  simp [kemPk, Bytes.Invariant.eq, KemPub.invariants]

end KemPkLemmas

end Invariants

-- Temporarily close the namespace to define `Bytes.kemSkLabel` and `Bytes.KemSkHasUsage`
end DySlop.Kem

section ExtractKemSk

variable [BytesFunctor] [BytesFunctor.Has DySlop.Kem.SubF]

/-- Port of `extract_kem_sk`. -/
public
noncomputable
def DySlop.Kem.extractKemSk (pk: Bytes): Option Bytes :=
  match pk.view? DySlop.Kem.KemPub.SubF with
  | some { sk } =>
    some sk
  | none => none

public
theorem DySlop.Kem.kemPk_extractKemSk (b: Bytes):
  match extractKemSk b with
  | none => True
  | some sk => b = DySlop.Kem.kemPk sk
:= by
  simp [extractKemSk, DySlop.Kem.kemPk]
  grind

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `extract_kem_sk_preserves_well_formedness`. -/
public
theorem DySlop.Kem.extractKemSk.preserves_WellFormed
  [BytesInvariants] [BytesInvariants.Has DySlop.Kem.KemPub.invariants]
: ExtractPreservesWellFormed extractKemSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [DySlop.Kem.kemPk_extractKemSk, DySlop.Kem.kemPk.WellFormed]

/-- Port of `get_kem_sk_label`. -/
@[expose]
public
noncomputable
def DY.Bytes.kemSkLabel
  [GetLabel]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DySlop.Kem.extractKemSk pk tr

/-- Port of `get_kem_sk_label_kem_pk`. -/
public
theorem DY.Bytes.kemSkLabel_kemPk
  [GetLabel]
  (sk: Bytes) (tr: ProofTrace)
  : (DySlop.Kem.kemPk sk).kemSkLabel tr = sk.label tr
:= by
  simp [Bytes.kemSkLabel, Bytes.xxxLabel, DySlop.Kem.extractKemSk, DySlop.Kem.kemPk]
  grind

grind_pattern DY.Bytes.kemSkLabel_kemPk => (DySlop.Kem.kemPk sk).kemSkLabel tr

public
theorem DY.Bytes.kemSkLabel_later
  [BytesInvariants] [BytesInvariants.Has DySlop.Kem.KemPub.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by
  simp only [Bytes.kemSkLabel]
  apply Bytes.xxxLabel_later DySlop.Kem.extractKemSk DySlop.Kem.extractKemSk.preserves_WellFormed

grind_pattern DY.Bytes.kemSkLabel_later => tr1 ≤ tr2, b.kemSkLabel tr1

public
theorem DY.Bytes.kemSkLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.Kem.KemPub.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.kemSkLabel_later_fast => tr1 ≤ tr2, b.kemSkLabel tr1

/-- Port of `has_kem_sk_usage`. -/
@[expose]
public
def DY.Bytes.KemSkHasUsage
  [GetUsage] [GetLabel]
  (pk: Bytes) (usg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage DySlop.Kem.extractKemSk pk usg tr

/-- Port of `has_kem_sk_usage_kem_pk`. -/
public
theorem DY.Bytes.KemSkHasUsage_kemPk
  [GetUsage] [GetLabel]
  (sk: Bytes) (usg: Usage) (tr: ProofTrace)
  : (DySlop.Kem.kemPk sk).KemSkHasUsage usg tr = sk.HasUsage usg tr
:= by
  simp [Bytes.KemSkHasUsage, Bytes.XXXHasUsage, DySlop.Kem.extractKemSk, DySlop.Kem.kemPk]
  grind

grind_pattern DY.Bytes.KemSkHasUsage_kemPk => (DySlop.Kem.kemPk sk).KemSkHasUsage usg tr

public
theorem DY.Bytes.KemSkHasUsage_later
  [BytesInvariants] [BytesInvariants.Has DySlop.Kem.KemPub.invariants]
  [GetUsageLater] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by
  simp only [Bytes.KemSkHasUsage]
  apply Bytes.XXXHasUsage_later DySlop.Kem.extractKemSk DySlop.Kem.extractKemSk.preserves_WellFormed

grind_pattern DY.Bytes.KemSkHasUsage_later => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

public
theorem DY.Bytes.KemSkHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.Kem.KemPub.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.KemSkHasUsage_later_fast => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

end ExtractKemSk

namespace DySlop.Kem

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def KemEncap.invariants [BytesFunctor.Has Kem.SubF]: Bytes.PartialInvariants KemEncap.SubF where
  well_formed := fun {pk, nonce} rec tr =>
    (rec pk) tr ∧
    (rec nonce) tr

  usage := fun {pk := _, nonce := _} _rec _tr =>
    Usage.nothing

  label := fun {pk := _, nonce := _} _rec _tr =>
    Label.pub

  invariant := fun {pk, nonce} rec tr =>
    (rec pk) tr ∧
    (rec nonce) tr ∧
    (
      (
        -- Honest case:
        -- nonce is knowable by the holder of pk
        -- (because the nonce roughly corresponds to the shared secret)
        (nonce.label tr).canFlow (pk.kemSkLabel tr) tr.erase ∧
        -- nonce and pk agree on the usage of the shared secret
        -- (this is because this KEM model does not bind the public key to the shared secret)
        ∃ ssUsg,
          pk.KemSkHasUsage (Usage.kemKey ssUsg) tr ∧
          nonce.HasUsage (Usage.kemNonce ssUsg) tr
      ) ∨ (
        -- Attacker case:
        -- the attacker knows the nonce
        (nonce.label tr).canFlow Label.pub tr.erase
      )
    )

public
theorem KemEncap.invariantsProofs [BytesFunctor.Has Kem.SubF] [BytesInvariants] [BytesInvariants.Has KemPub.invariants]: Bytes.PartialInvariantsProofs KemEncap.invariants where

public
def KemSecretShared.invariants: Bytes.PartialInvariants KemSecretShared.SubF where
  well_formed := fun {nonce := nonce} rec tr =>
    (rec nonce) tr

  usage := fun {nonce := nonce} rec tr =>
    match ((rec nonce) tr).kemNonce? with
    | some usg => usg
    | none => Usage.nothing

  label := fun {nonce := nonce} rec tr =>
    (rec nonce) tr

  invariant := fun {nonce := nonce} rec tr =>
    (rec nonce) tr

public
theorem KemSecretShared.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs KemSecretShared.invariants where

end Definition

#combine [BytesFunctor.Has SubF] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has KemPub.invariants]
from
  KemPub,
  KemEncap,
  KemSecretShared

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_kem_encap`. -/
public
theorem kemEncap.WellFormed
  (pk nonce: Bytes) (tr: ProofTrace)
  : (kemEncap pk nonce).1.WellFormed tr = (pk.WellFormed tr ∧ nonce.WellFormed tr) ∧
    (kemEncap pk nonce).2.WellFormed tr = nonce.WellFormed tr
:= by
  simp [kemEncap, Bytes.WellFormed.eq, KemEncap.invariants, KemSecretShared.invariants]

/-- Port of `bytes_well_formed_kem_decap`. -/
public
theorem kemDecap.WellFormed
  (sk encap: Bytes) (tr: ProofTrace)
  : match kemDecap sk encap with
    | none => True
    | some ss => encap.WellFormed tr = (sk.WellFormed tr ∧ ss.WellFormed tr)
:= by
  split
  · trivial
  rename_i ss heq
  simp only [kemDecap] at heq
  split at heq
  · rename_i pk nonce _
    obtain rfl: encap = ({pk, nonce}: KemEncap.SubF Bytes).pack := by grind
    split at heq
    · rename_i sk' _
      obtain rfl: pk = ({sk := sk'}: KemPub.SubF Bytes).pack := by grind
      split at heq
      · rename_i h_sk'
        subst h_sk'
        cases heq
        simp [KemEncap.invariants, KemSecretShared.invariants, KemPub.invariants]
      · simp at heq
    · simp at heq
  · simp at heq

/-- Port of `bytes_invariant_kem_encap`. -/
public
theorem kemEncap.Invariant
  (pk nonce: Bytes) (usg: Usage) (tr: ProofTrace)
  : pk.Invariant tr →
    nonce.Invariant tr →
    nonce.HasUsage (Usage.kemNonce usg) tr →
    (
      (
        pk.KemSkHasUsage (Usage.kemKey usg) tr ∧
        (nonce.label tr).canFlow (pk.kemSkLabel tr) tr.erase
      ) ∨ (
        (nonce.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (kemEncap pk nonce).1.Publishable tr ∧
    (kemEncap pk nonce).2.Invariant tr ∧
    (kemEncap pk nonce).2.label tr = nonce.label tr ∧
    (kemEncap pk nonce).2.HasUsage usg tr
:= by
  simp [kemEncap, Bytes.Publishable, Bytes.HasUsage, KemEncap.invariants, KemSecretShared.invariants]
  grind

grind_pattern kemEncap.Invariant => kemEncap pk nonce, nonce.HasUsage (Usage.kemNonce usg) tr

/-- Port of `has_usage_kem_decap`. -/
public
theorem kemDecap.HasUsage
  (sk: Bytes) (ssUsg: Usage) (encap: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    encap.Invariant tr →
    sk.HasUsage (Usage.kemKey ssUsg) tr →
    match kemDecap sk encap with
    | none => True
    | some ss => ss.HasUsage ssUsg tr
:= by
  intro h_sk h_encap h_usg
  split
  · trivial
  rename_i ss heq
  simp only [kemDecap] at heq
  split at heq
  · rename_i pk nonce _
    obtain rfl: encap = ({pk, nonce}: KemEncap.SubF Bytes).pack := by grind
    split at heq
    · rename_i sk' _
      obtain rfl: pk = ({sk := sk'}: KemPub.SubF Bytes).pack := by grind
      split at heq
      · rename_i h_sk'
        subst h_sk'
        cases heq
        have := Bytes.HasUsage_inj sk (Usage.kemKey ssUsg)
        simp_all [Bytes.HasUsage, KemEncap.invariants, KemSecretShared.invariants, KemPub.invariants, Bytes.kemSkLabel, Bytes.KemSkHasUsage, Bytes.xxxLabel, Bytes.XXXHasUsage, extractKemSk]
        grind [canFlowTrans]
      · simp at heq
    · simp at heq
  · simp at heq

grind_pattern kemDecap.HasUsage => kemDecap sk encap, sk.HasUsage (Usage.kemKey ssUsg) tr

/-- Port of `bytes_invariant_kem_decap`. -/
public
theorem kemDecap.Invariant
  (sk encap: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    encap.Invariant tr →
    match kemDecap sk encap with
    | none => True
    | some ss => ss.KnowableBy (sk.label tr) tr
:= by
  intro h_sk h_encap
  split
  · trivial
  rename_i ss heq
  simp only [kemDecap] at heq
  split at heq
  · rename_i pk nonce _
    obtain rfl: encap = ({pk, nonce}: KemEncap.SubF Bytes).pack := by grind
    split at heq
    · rename_i sk' _
      obtain rfl: pk = ({sk := sk'}: KemPub.SubF Bytes).pack := by grind
      split at heq
      · rename_i h_sk'
        subst h_sk'
        cases heq
        simp_all [Bytes.KnowableBy, KemEncap.invariants, KemSecretShared.invariants, KemPub.invariants, Bytes.kemSkLabel, Bytes.KemSkHasUsage, Bytes.xxxLabel, Bytes.XXXHasUsage, extractKemSk]
        grind [canFlowTrans]
      · simp at heq
    · simp at heq
  · simp at heq

grind_pattern kemDecap.Invariant => kemDecap sk encap, encap.Invariant tr

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

/-- Port of `kem_pk_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem kemPk.attackerKnowledge where
  pf := by
    simp only [kemPk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

/-- Port of `kem_encap_preserves_publishability` (encapsulation). -/
public
instance: SubAttackerKnowledgeTheorem kemEncapLeft.attackerKnowledge where
  pf := by
    simp only [kemEncapLeft.attackerKnowledge]
    intro out tr h_tr ⟨pk, nonce, rhs, ⟨ h_out, h_pk, h_nonce ⟩⟩
    simp only [kemEncap, Prod.mk.injEq] at h_out
    obtain ⟨rfl, -⟩ := h_out
    simp_all [Bytes.Publishable, KemEncap.invariants]
    grind

/-- Port of `kem_encap_preserves_publishability` (shared secret). -/
public
instance: SubAttackerKnowledgeTheorem kemEncapRight.attackerKnowledge where
  pf := by
    simp only [kemEncapRight.attackerKnowledge]
    intro out tr h_tr ⟨pk, nonce, lhs, ⟨ h_out, h_pk, h_nonce ⟩⟩
    simp only [kemEncap, Prod.mk.injEq] at h_out
    obtain ⟨-, rfl⟩ := h_out
    simp_all [Bytes.Publishable, KemSecretShared.invariants]

/-- Port of `kem_decap_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem kemDecap.attackerKnowledge where
  pf := by
    simp only [kemDecap.attackerKnowledge]
    intro out tr h_tr ⟨sk, encap, ⟨ h_out, h_sk, h_encap ⟩⟩
    simp only [kemDecap] at h_out
    split at h_out
    · rename_i pk nonce _
      obtain rfl: encap = ({pk, nonce}: KemEncap.SubF Bytes).pack := by grind
      split at h_out
      · rename_i sk' _
        obtain rfl: pk = ({sk := sk'}: KemPub.SubF Bytes).pack := by grind
        split at h_out
        · rename_i h_sk'
          subst h_sk'
          cases h_out
          simp_all [Bytes.Publishable, KemEncap.invariants, KemSecretShared.invariants, KemPub.invariants, Bytes.kemSkLabel, Bytes.KemSkHasUsage, Bytes.xxxLabel, Bytes.XXXHasUsage, extractKemSk]
          grind [canFlowTrans]
        · simp at h_out
      · simp at h_out
    · simp at h_out

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kemPk,
  kemEncapLeft,
  kemEncapRight,
  kemDecap

end AttackerKnowledgeTheorem

end DySlop.Kem
