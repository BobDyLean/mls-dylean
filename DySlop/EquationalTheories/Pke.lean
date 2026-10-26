/-
  Port of the public-key encryption section of `DY.Core.Bytes`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.Pke

public
class CanPke (Bytes: Type u) where
  /-- Port of `pk`. -/
  pk: (sk: Bytes) → Bytes
  /-- Port of `pke_enc`. -/
  pkeEnc: (pk: Bytes) → (nonce: Bytes) → (msg: Bytes) → Bytes
  /-- Port of `pke_dec`. -/
  pkeDec: (sk: Bytes) → (msg: Bytes) → Option Bytes

export CanPke (pk)
export CanPke (pkeEnc)
export CanPke (pkeDec)

section Constructors

namespace Pk

/-- Port of `Pk`. -/
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

end Pk

namespace PkeEnc

/-- Port of `PkeEnc`. -/
public
structure SubF (Bytes: Type) where
  pk: Bytes
  nonce: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pk, nonce, msg} => sizeOf pk + sizeOf nonce + sizeOf msg

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }

  toRepr | {pk, nonce, msg} => {
    id := ()
    data := ()
    as := #v[pk, nonce, msg]
  }
  fromRepr
  | {id, data, as} =>
    let pk := as[0]
    let nonce := as[1]
    let msg := as[2]
    { pk, nonce, msg }
  from_to | {pk, nonce, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pk, nonce, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { pk := _, nonce := _, msg } rec =>
    64 + rec msg

end PkeEnc

#combine into BytesFunctor, BytesLength from
  Pk,
  PkeEnc

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Pk.SubF.pack (x: Pk.SubF Bytes) := BytesView.pack x
public abbrev PkeEnc.SubF.pack (x: PkeEnc.SubF Bytes) := BytesView.pack x

public
instance: CanPke Bytes where
  pk sk :=
    ({sk}: Pk.SubF Bytes).pack

  pkeEnc pk nonce msg :=
    ({pk, nonce, msg}: PkeEnc.SubF Bytes).pack

  pkeDec sk msg :=
    match msg.view? PkeEnc.SubF with
    | some { pk, nonce := _, msg := res } =>
      match pk.view? Pk.SubF with
      | some { sk := sk' } =>
        if sk = sk' then
          some res
        else
          none
      | none => none
    | none => none

/-- Port of `pke_dec_enc`. -/
public
theorem pke_dec_enc
  (sk nonce msg: Bytes)
  : pkeDec sk (pkeEnc (pk sk) nonce msg) = some msg
:= by
  simp only [pkeDec, pkeEnc, pk]
  grind

@[simp]
public
theorem length_pk
  [BytesLength] [BytesLength.Has SubF.length]
  (sk: Bytes)
  : Bytes.length (pk sk) = 32
:= by
  simp only [pk]
  grind [Pk.SubF.length]

@[simp]
public
theorem length_pkeEnc
  [BytesLength] [BytesLength.Has SubF.length]
  (pk nonce msg: Bytes)
  : Bytes.length (pkeEnc pk nonce msg) = 64 + Bytes.length msg
:= by
  simp only [pkeEnc]
  grind [PkeEnc.SubF.length]

end Constructors

section AttackerKnowledge

public
def pk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = pk sk ∧
      p sk

public
def pkeEnc.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pk nonce msg,
      out = pkeEnc pk nonce msg ∧
      p pk ∧
      p nonce ∧
      p msg

public
def pkeDec.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk msg,
      some out = pkeDec sk msg ∧
      p sk ∧
      p msg

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  pk,
  pkeEnc,
  pkeDec

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_pk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (pk sk).AttackerKnows tr
:= by
  intro h_sk
  apply Bytes.AttackerKnows.prove pk.attackerKnowledge
  simp only [pk.attackerKnowledge]
  grind

public
theorem attacker_knows_pkeEnc
  (pk nonce msg: Bytes) (tr: ExecTrace)
  : pk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (pkeEnc pk nonce msg).AttackerKnows tr
:= by
  intro h_pk h_nonce h_msg
  apply Bytes.AttackerKnows.prove pkeEnc.attackerKnowledge
  simp only [pkeEnc.attackerKnowledge]
  grind

public
theorem attacker_knows_pkeDec
  (sk msg: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    msg.AttackerKnows tr →
    match pkeDec sk msg with
    | none => True
    | some res => res.AttackerKnows tr
:= by
  intro h_sk h_msg
  split
  · trivial
  apply Bytes.AttackerKnows.prove pkeDec.attackerKnowledge
  simp only [pkeDec.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def Pk.invariants: Bytes.PartialInvariants Pk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := _} _rec _tr =>
    Usage.nothing

  label := fun {sk := _} _rec _tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
theorem Pk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Pk.invariants where

end Definition

section PkLemmas

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has Pke.SubF]
variable [BytesInvariants] [BytesInvariants.Has Pk.invariants]

/-- Port of `bytes_well_formed_pk`. -/
@[simp]
public
theorem pk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  : (pk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [pk, Bytes.WellFormed.eq, Pk.invariants]

/-- Port of `get_label_pk`. -/
@[simp]
public
theorem pk.label
  (sk: Bytes) (tr: ProofTrace)
  : (pk sk).label tr = Label.pub
:= by
  simp [pk, Bytes.label.eq, Pk.invariants]

/-- Port of `bytes_invariant_pk`. -/
@[simp]
public
theorem pk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : (pk sk).Invariant tr = sk.Invariant tr
:= by
  simp [pk, Bytes.Invariant.eq, Pk.invariants]

end PkLemmas

end Invariants

-- Temporarily close the namespace to define `Bytes.skLabel` and `Bytes.SkHasUsage`
end DySlop.Pke

section ExtractSk

variable [BytesFunctor] [BytesFunctor.Has DySlop.Pke.SubF]

/-- Port of `extract_sk`. -/
public
noncomputable
def DySlop.Pke.extractSk (pk: Bytes): Option Bytes :=
  match pk.view? DySlop.Pke.Pk.SubF with
  | some { sk } =>
    some sk
  | none => none

theorem DySlop.Pke.pk_extractSk (b: Bytes):
  match extractSk b with
  | none => True
  | some sk => b = DySlop.Pke.pk sk
:= by
  simp [extractSk, DySlop.Pke.pk]
  grind

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `extract_sk_preserves_well_formedness`. -/
theorem DySlop.Pke.extractSk.preserves_WellFormed
  [BytesInvariants] [BytesInvariants.Has DySlop.Pke.Pk.invariants]
: ExtractPreservesWellFormed extractSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [DySlop.Pke.pk_extractSk, DySlop.Pke.pk.WellFormed]

/-- Port of `get_sk_label`. -/
@[expose]
public
noncomputable
def DY.Bytes.skLabel
  [GetLabel]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DySlop.Pke.extractSk pk tr

/-- Port of `get_sk_label_pk`. -/
public
theorem DY.Bytes.skLabel_pk
  [GetLabel]
  (sk: Bytes) (tr: ProofTrace)
  : (DySlop.Pke.pk sk).skLabel tr = sk.label tr
:= by
  simp [Bytes.skLabel, Bytes.xxxLabel, DySlop.Pke.extractSk, DySlop.Pke.pk]
  grind

grind_pattern DY.Bytes.skLabel_pk => (DySlop.Pke.pk sk).skLabel tr

public
theorem DY.Bytes.skLabel_later
  [BytesInvariants] [BytesInvariants.Has DySlop.Pke.Pk.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.skLabel tr1 = b.skLabel tr2
:= by
  simp only [Bytes.skLabel]
  apply Bytes.xxxLabel_later DySlop.Pke.extractSk DySlop.Pke.extractSk.preserves_WellFormed

grind_pattern DY.Bytes.skLabel_later => tr1 ≤ tr2, b.skLabel tr1

public
theorem DY.Bytes.skLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.Pke.Pk.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.skLabel tr1 = b.skLabel tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.skLabel_later_fast => tr1 ≤ tr2, b.skLabel tr1

/-- Port of `has_sk_usage`. -/
@[expose]
public
def DY.Bytes.SkHasUsage
  [GetUsage] [GetLabel]
  (pk: Bytes) (usg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage DySlop.Pke.extractSk pk usg tr

/-- Port of `has_sk_usage_pk`. -/
public
theorem DY.Bytes.SkHasUsage_pk
  [GetUsage] [GetLabel]
  (sk: Bytes) (usg: Usage) (tr: ProofTrace)
  : (DySlop.Pke.pk sk).SkHasUsage usg tr = sk.HasUsage usg tr
:= by
  simp [Bytes.SkHasUsage, Bytes.XXXHasUsage, DySlop.Pke.extractSk, DySlop.Pke.pk]
  grind

grind_pattern DY.Bytes.SkHasUsage_pk => (DySlop.Pke.pk sk).SkHasUsage usg tr

public
theorem DY.Bytes.SkHasUsage_later
  [BytesInvariants] [BytesInvariants.Has DySlop.Pke.Pk.invariants]
  [GetUsageLater] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.SkHasUsage usg tr1 →
    b.SkHasUsage usg tr2
:= by
  simp only [Bytes.SkHasUsage]
  apply Bytes.XXXHasUsage_later DySlop.Pke.extractSk DySlop.Pke.extractSk.preserves_WellFormed

grind_pattern DY.Bytes.SkHasUsage_later => tr1 ≤ tr2, b.SkHasUsage usg tr1

public
theorem DY.Bytes.SkHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.Pke.Pk.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.SkHasUsage usg tr1 →
    b.SkHasUsage usg tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.SkHasUsage_later_fast => tr1 ≤ tr2, b.SkHasUsage usg tr1

end ExtractSk

namespace DySlop.Pke

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  Port of `pke_crypto_predicate`.
  DY* requires `PkeKey? sk_usage`; here, the predicate is defined on all usages.
-/
public
class PkePred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → (skUsage: Usage) → (pk msg: Bytes) → ProofTrace → Prop

/-- Port of `pke_crypto_predicate.pred_later`. -/
public
class PkePredProof [BytesInvariants] [PkePred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ skUsg pk msg tr1 tr2,
      pk.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      PkePred.pred skUsg pk msg tr1 →
      PkePred.pred skUsg pk msg tr2

grind_pattern PkePredProof.pred_later => tr1 ≤ tr2, PkePred.pred skUsg pk msg tr1

public
theorem PkePredProof.pred_later_fast
  [BytesInvariants] [PkePred] [PkePredProof] [BytesInvariantsProofs]
  (skUsg: Usage) (pk msg: Bytes) (tr1 tr2: ProofTrace)
  : pk.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    PkePred.pred skUsg pk msg tr1 →
    PkePred.pred skUsg pk msg tr2
:= by grind

grind_pattern [grind_later] PkePredProof.pred_later_fast => tr1 ≤ tr2, PkePred.pred skUsg pk msg tr1

public
def PkeEnc.invariants [BytesFunctor.Has Pke.SubF] [PkePred]: Bytes.PartialInvariants PkeEnc.SubF where
  well_formed := fun {pk, nonce, msg} rec tr =>
    (rec pk) tr ∧
    (rec nonce) tr ∧
    (rec msg) tr

  usage := fun {pk := _, nonce := _, msg := _} _rec _tr =>
    Usage.nothing

  label := fun {pk := _, nonce := _, msg := _} _rec _tr =>
    Label.pub

  invariant := fun {pk, nonce, msg} rec tr =>
    (rec pk) tr ∧
    (rec nonce) tr ∧
    (rec msg) tr ∧
    (
      (
        ∃ skUsg,
        -- Honest case:
        -- - the key has the usage of asymetric encryption key
        pk.SkHasUsage skUsg tr ∧
        skUsg.type = "PkeKey" ∧
        -- - the custom (protocol-specific) invariant hold (authentication)
        PkePred.pred skUsg pk msg tr ∧
        -- - the message is less secret than the decryption key
        --   (this is crucial so that decryption preserve publishability)
        (msg.label tr).canFlow (pk.skLabel tr) tr.erase ∧
        -- - the message is less secret than the nonce
        --   (this is because the standard IND-CCA security assumption
        --   do not give guarantees on the indistinguishability of the message
        --   when the attacker knows the nonce)
        (msg.label tr).canFlow (nonce.label tr) tr.erase ∧
        -- - the nonce has the correct usage (for the same reason as above)
        nonce.HasUsage Usage.pkeNonce tr
      ) ∨ (
        -- Attacker case:
        -- the attacker knows the message
        (msg.label tr).canFlow Label.pub tr.erase
      )
    )

public
theorem PkeEnc.invariantsProofs [BytesFunctor.Has Pke.SubF] [BytesInvariants] [BytesInvariants.Has Pk.invariants] [PkePred] [PkePredProof]: Bytes.PartialInvariantsProofs PkeEnc.invariants where

end Definition

#combine [BytesFunctor.Has SubF] [PkePred] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Pk.invariants] [PkePredProof]
from
  Pk,
  PkeEnc

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [PkePred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_pke_enc`. -/
@[simp]
public
theorem pkeEnc.WellFormed
  (pk nonce msg: Bytes) (tr: ProofTrace)
  : (pkeEnc pk nonce msg).WellFormed tr = (
      pk.WellFormed tr ∧
      nonce.WellFormed tr ∧
      msg.WellFormed tr
    )
:= by
  simp [pkeEnc, Bytes.WellFormed.eq, PkeEnc.invariants]

/-- Port of `bytes_well_formed_pke_dec`. -/
public
theorem pkeDec.WellFormed
  (sk msg: Bytes) (tr: ProofTrace)
  : match pkeDec sk msg with
    | none => True
    | some plaintext =>
      msg.WellFormed tr → (
        sk.WellFormed tr ∧
        plaintext.WellFormed tr
      )
:= by
  split
  · trivial
  rename_i plaintext heq
  simp only [pkeDec] at heq
  split at heq
  · rename_i pk' nonce res _
    obtain rfl: msg = ({pk := pk', nonce, msg := res}: PkeEnc.SubF Bytes).pack := by grind
    split at heq
    · rename_i sk' _
      obtain rfl: pk' = ({sk := sk'}: Pk.SubF Bytes).pack := by grind
      simp_all [PkeEnc.invariants, Pk.invariants]
    · simp at heq
  · simp at heq

/-- Port of `get_label_pke_enc`. -/
@[simp]
public
theorem pkeEnc.label
  (pk nonce msg: Bytes) (tr: ProofTrace)
  : (pkeEnc pk nonce msg).label tr = Label.pub
:= by
  simp [pkeEnc, Bytes.label.eq, PkeEnc.invariants]

/-- Port of `bytes_invariant_pke_enc`. -/
public
theorem pkeEnc.Invariant
  (pk: Bytes) (skUsg: Usage) (nonce msg: Bytes) (tr: ProofTrace)
  : pk.Invariant tr →
    nonce.Invariant tr →
    msg.Invariant tr →
    (msg.label tr).canFlow (pk.skLabel tr) tr.erase →
    (msg.label tr).canFlow (nonce.label tr) tr.erase →
    pk.SkHasUsage skUsg tr →
    nonce.HasUsage Usage.pkeNonce tr →
    (
      (
        skUsg.type = "PkeKey" ∧
        PkePred.pred skUsg pk msg tr
      ) ∨ (
        (msg.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (pkeEnc pk nonce msg).Invariant tr
:= by
  simp [pkeEnc, Bytes.Invariant.eq, PkeEnc.invariants]
  grind

grind_pattern pkeEnc.Invariant => (pkeEnc pk nonce msg).Invariant tr, pk.SkHasUsage skUsg tr

/-- Port of `bytes_invariant_pke_dec`. -/
public
theorem pkeDec.Invariant
  (sk: Bytes) (skUsg: Usage) (msg: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    msg.Invariant tr →
    sk.HasUsage skUsg tr →
    match pkeDec sk msg with
    | none => True
    | some plaintext =>
      plaintext.KnowableBy (sk.label tr) tr ∧
      (
        (
          skUsg.type = "PkeKey" ∧
          PkePred.pred skUsg (pk sk) plaintext tr
        ) ∨ (
          (plaintext.label tr).canFlow Label.pub tr.erase
        )
      )
:= by
  intro h_sk h_msg h_usg
  split
  · trivial
  rename_i plaintext heq
  simp only [pkeDec] at heq
  split at heq
  · rename_i pk' nonce res _
    obtain rfl: msg = ({pk := pk', nonce, msg := res}: PkeEnc.SubF Bytes).pack := by grind
    split at heq
    · rename_i sk' _
      obtain rfl: pk' = ({sk := sk'}: Pk.SubF Bytes).pack := by grind
      have := Bytes.HasUsage_inj sk skUsg
      simp_all [Bytes.KnowableBy, pk, PkeEnc.invariants, Pk.invariants, Bytes.skLabel, Bytes.SkHasUsage, Bytes.xxxLabel, Bytes.XXXHasUsage, extractSk]
      grind [canFlowTrans]
    · simp at heq
  · simp at heq

grind_pattern pkeDec.Invariant => pkeDec sk msg, msg.Invariant tr, sk.HasUsage skUsg tr

end Invariants

section KeyPredicates

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants]

/--
  Port of `is_encryption_key`.
  DY* requires `PkeKey? usg`.
-/
@[expose]
public
def IsEncryptionKey (usg: Usage) (l: Label) (b: Bytes) (tr: ProofTrace): Prop :=
  b.Publishable tr ∧
  b.skLabel tr = l ∧
  b.SkHasUsage usg tr

/--
  Port of `is_decryption_key`.
  DY* requires `PkeKey? usg`.
-/
@[expose]
public
def IsDecryptionKey (usg: Usage) (l: Label) (b: Bytes) (tr: ProofTrace): Prop :=
  b.IsSecret l tr ∧
  b.HasUsage usg tr

end KeyPredicates

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [PkePred]
variable [BytesInvariants.Has invariants]

/-- Port of `pk_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem pk.attackerKnowledge where
  pf := by
    simp only [pk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

/-- Port of `pke_enc_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem pkeEnc.attackerKnowledge where
  pf := by
    simp only [pkeEnc.attackerKnowledge]
    intro out tr h_tr ⟨pk, nonce, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [pkeEnc, Bytes.Invariant.eq, PkeEnc.invariants]
    grind

/-- Port of `pke_dec_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem pkeDec.attackerKnowledge where
  pf := by
    simp only [pkeDec.attackerKnowledge]
    intro out tr h_tr ⟨sk, msg, ⟨ h_out, h_sk, h_msg ⟩⟩
    simp only [pkeDec] at h_out
    split at h_out
    · rename_i pk' nonce res _
      obtain rfl: msg = ({pk := pk', nonce, msg := res}: PkeEnc.SubF Bytes).pack := by grind
      split at h_out
      · rename_i sk' _
        obtain rfl: pk' = ({sk := sk'}: Pk.SubF Bytes).pack := by grind
        simp_all [Bytes.Publishable, PkeEnc.invariants, Pk.invariants, Bytes.skLabel, Bytes.xxxLabel, extractSk]
        grind [canFlowTrans]
      · simp at h_out
    · simp at h_out

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [PkePred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  pk,
  pkeEnc,
  pkeDec

end AttackerKnowledgeTheorem

end DySlop.Pke
