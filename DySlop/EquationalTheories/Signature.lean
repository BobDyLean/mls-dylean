/-
  Port of the signature section of `DY.Core.Bytes`.

  Compared to `DY.EquationalTheory.Sign` in DyLean,
  the signature invariant also requires the nonce to have the usage `SigNonce`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.Signature

public
class CanSign (Bytes: Type u) where
  /-- Port of `vk`. -/
  vk: (sk: Bytes) → Bytes
  /-- Port of `sign`. -/
  sign: (sk: Bytes) → (nonce: Bytes) → (msg: Bytes) → Bytes
  /-- Port of `verify`. -/
  verify: (vk: Bytes) → (msg: Bytes) → (sig: Bytes) → Bool

export CanSign (vk)
export CanSign (sign)
export CanSign (verify)

section Constructors

namespace Vk

/-- Port of `Vk`. -/
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

end Vk

namespace Sign

/-- Port of `Sign`. -/
public
structure SubF (Bytes: Type) where
  sk: Bytes
  nonce: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk, nonce, msg} => sizeOf sk + sizeOf nonce + sizeOf msg

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }

  toRepr | {sk, nonce, msg} => {
    id := ()
    data := ()
    as := #v[sk, nonce, msg]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    let nonce := as[1]
    let msg := as[2]
    { sk, nonce, msg }
  from_to | {sk, nonce, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk, nonce, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    64

end Sign

#combine into BytesFunctor, BytesLength from
  Vk,
  Sign

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Vk.SubF.pack (x: Vk.SubF Bytes) := BytesView.pack x
public abbrev Sign.SubF.pack (x: Sign.SubF Bytes) := BytesView.pack x

public
instance: CanSign Bytes where
  vk sk :=
    ({sk}: Vk.SubF Bytes).pack

  sign sk nonce msg :=
    ({sk, nonce, msg}: Sign.SubF Bytes).pack

  verify vk msg sig :=
    match sig.view? Sign.SubF with
    | some { sk, nonce := _, msg := msg' } =>
      vk = ({sk} : Vk.SubF Bytes).pack &&
      msg = msg'
    | none => false

/-- Port of `verify_sign`. -/
public
theorem verify_sign
  (sk nonce msg: Bytes)
  : verify (vk sk) msg (sign sk nonce msg) = true
:= by
  simp only [verify, vk, sign]
  grind

@[simp]
public
theorem length_vk
  [BytesLength] [BytesLength.Has SubF.length]
  (sk: Bytes)
  : Bytes.length (vk sk) = 32
:= by
  simp only [vk]
  grind [Vk.SubF.length]

@[simp]
public
theorem length_sign
  [BytesLength] [BytesLength.Has SubF.length]
  (sk nonce msg: Bytes)
  : Bytes.length (sign sk nonce msg) = 64
:= by
  simp only [sign]
  grind [Sign.SubF.length]

end Constructors

section AttackerKnowledge

public
def vk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = vk sk ∧
      p sk

public
def sign.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk nonce msg,
      out = sign sk nonce msg ∧
      p sk ∧
      p nonce ∧
      p msg

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  vk,
  sign

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_vk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (vk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove vk.attackerKnowledge
  simp only [vk.attackerKnowledge]
  grind

public
theorem attacker_knows_sign
  (sk nonce msg: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (sign sk nonce msg).AttackerKnows tr
:= by
  intro h_inp h_nonce h_msg
  apply Bytes.AttackerKnows.prove sign.attackerKnowledge
  simp only [sign.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def Vk.invariants: Bytes.PartialInvariants Vk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := _} _rec _tr =>
    Usage.nothing

  label := fun {sk := _} _rec _tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
theorem Vk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Vk.invariants where

end Definition

section VkLemmas

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has Signature.SubF]
variable [BytesInvariants] [BytesInvariants.Has Vk.invariants]

/-- Port of `bytes_well_formed_vk`. -/
@[simp]
public
theorem vk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  : (vk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [vk, Bytes.WellFormed.eq, Vk.invariants]

/-- Port of `get_label_vk`. -/
@[simp]
public
theorem vk.label
  (sk: Bytes) (tr: ProofTrace)
  : (vk sk).label tr = Label.pub
:= by
  simp [vk, Bytes.label.eq, Vk.invariants]

/-- Port of `bytes_invariant_vk`. -/
@[simp]
public
theorem vk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : (vk sk).Invariant tr = sk.Invariant tr
:= by
  simp [vk, Bytes.Invariant.eq, Vk.invariants]

end VkLemmas

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  Port of `sign_crypto_predicate`.
  DY* requires `SigKey? sk_usage`; here, the predicate is defined on all usages.
-/
public
class SignPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → Usage → Bytes → Bytes → ProofTrace → Prop

/-- Port of `sign_crypto_predicate.pred_later`. -/
public
class SignPredProof [BytesInvariants] [SignPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ skUsg vk msg tr1 tr2,
      vk.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      SignPred.pred skUsg vk msg tr1 →
      SignPred.pred skUsg vk msg tr2

grind_pattern SignPredProof.pred_later => tr1 ≤ tr2, SignPred.pred skUsg vk msg tr1

public
theorem SignPredProof.pred_later_fast
  [BytesInvariants] [SignPred] [SignPredProof] [BytesInvariantsProofs]
  (skUsg: Usage) (vk msg: Bytes) (tr1 tr2: ProofTrace)
  : vk.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    SignPred.pred skUsg vk msg tr1 →
    SignPred.pred skUsg vk msg tr2
:= by grind

grind_pattern [grind_later] SignPredProof.pred_later_fast => tr1 ≤ tr2, SignPred.pred skUsg vk msg tr1

public
def Sign.invariants [BytesFunctor.Has Signature.SubF] [SignPred]: Bytes.PartialInvariants Sign.SubF where
  well_formed := fun {sk, nonce, msg} rec tr =>
      (rec sk) tr ∧
      (rec nonce) tr ∧
      (rec msg) tr

  usage := fun {sk := _, nonce := _, msg := _} _rec _tr =>
    Usage.nothing

  label := fun {sk := _, nonce := _, msg} rec tr =>
    (rec msg) tr

  invariant := fun {sk, nonce, msg} rec tr =>
      (rec sk) tr ∧
      (rec nonce) tr ∧
      (rec msg) tr ∧
      (
        (
          ∃ skUsg,
          -- Honest case:
          -- - the key has the usage of signature key
          sk.HasUsage skUsg tr ∧
          skUsg.type = "SigKey" ∧
          -- - the custom (protocol-specific) invariant hold (authentication)
          SignPred.pred skUsg (vk sk) msg tr ∧
          -- - the nonce is more secret than the signature key
          --   (this is because the standard EUF-CMA security assumption on signatures
          --   do not have any guarantees when the nonce is leaked to the attacker,
          --   in practice knowing the nonce used to sign a message
          --   can be used to obtain the private key,
          --   hence this restriction)
          (sk.label tr).canFlow (nonce.label tr) tr.erase ∧
          -- - the nonce has the correct usage (for the same reason as above)
          nonce.HasUsage Usage.sigNonce tr
        ) ∨ (
          -- Attacker case:
          -- the attacker knows the signature key.
          -- The message is not required to be known by the attacker:
          -- the EUF-CMA security assumption on signatures doesn't guarantee
          -- that in case of signature forgeries.
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )

public
theorem Sign.invariantsProofs [BytesFunctor.Has Signature.SubF] [BytesInvariants] [BytesInvariants.Has Vk.invariants] [SignPred] [SignPredProof]: Bytes.PartialInvariantsProofs Sign.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind [vk.WellFormed]

end Definition

#combine [BytesFunctor.Has SubF] [SignPred] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Vk.invariants] [SignPredProof]
from
  Vk,
  Sign

end Invariants

-- Temporarily close the namespace to define `Bytes.SignkeyHasUsage` and `Bytes.signkeyLabel`
end DySlop.Signature

section ExtractSignKey

variable [BytesFunctor] [BytesFunctor.Has DySlop.Signature.SubF]

/-- Port of `extract_signkey`. -/
public
noncomputable
def DySlop.Signature.extractSignkey (vk: Bytes): Option Bytes :=
  match vk.view? DySlop.Signature.Vk.SubF with
  | some { sk } =>
    some sk
  | none => none

theorem DySlop.Signature.vk_extractSignkey (b: Bytes):
  match extractSignkey b with
  | none => True
  | some sk => b = DySlop.Signature.vk sk
:= by
  simp [extractSignkey, DySlop.Signature.vk]
  grind

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `extract_signkey_preserves_well_formedness`. -/
theorem DySlop.Signature.extractSignkey.preserves_WellFormed
  [BytesInvariants] [DySlop.Signature.SignPred] [BytesInvariants.Has DySlop.Signature.invariants]
: ExtractPreservesWellFormed extractSignkey
:= by
  simp [ExtractPreservesWellFormed]
  grind [DySlop.Signature.vk_extractSignkey, DySlop.Signature.vk.WellFormed]

/-- Port of `has_signkey_usage`. -/
public
def DY.Bytes.SignkeyHasUsage
  [BytesInvariants]
  (vk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage DySlop.Signature.extractSignkey vk skUsg tr

/-- Port of `has_signkey_usage_vk`. -/
public
theorem DY.Bytes.SignkeyHasUsage_vk
  [BytesInvariants]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (DySlop.Signature.vk sk).SignkeyHasUsage skUsg tr = sk.HasUsage skUsg tr
:= by
  simp [Bytes.SignkeyHasUsage, Bytes.XXXHasUsage, DySlop.Signature.extractSignkey, DySlop.Signature.vk]
  grind

grind_pattern DY.Bytes.SignkeyHasUsage_vk => (DySlop.Signature.vk sk).SignkeyHasUsage skUsg tr

public
theorem DY.Bytes.SignkeyHasUsage_later
  [BytesInvariants] [BytesInvariantsProofs]
  [DySlop.Signature.SignPred] [BytesInvariants.Has DySlop.Signature.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.SignkeyHasUsage usg tr1 →
    b.SignkeyHasUsage usg tr2
:= by
  simp only [Bytes.SignkeyHasUsage]
  apply Bytes.XXXHasUsage_later DySlop.Signature.extractSignkey DySlop.Signature.extractSignkey.preserves_WellFormed

grind_pattern DY.Bytes.SignkeyHasUsage_later => tr1 ≤ tr2, b.SignkeyHasUsage usg tr1

public
theorem DY.Bytes.SignkeyHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [DySlop.Signature.SignPred] [BytesInvariants.Has DySlop.Signature.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.SignkeyHasUsage usg tr1 →
    b.SignkeyHasUsage usg tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.SignkeyHasUsage_later_fast => tr1 ≤ tr2, b.SignkeyHasUsage usg tr1

/-- Port of `get_signkey_label`. -/
public
noncomputable
def DY.Bytes.signkeyLabel
  [BytesInvariants]
  (vk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DySlop.Signature.extractSignkey vk tr

/-- Port of `get_signkey_label_vk`. -/
public
theorem DY.Bytes.signkeyLabel_vk
  [BytesInvariants]
  (sk: Bytes) (tr: ProofTrace)
  : (DySlop.Signature.vk sk).signkeyLabel tr = sk.label tr
:= by
  simp [Bytes.signkeyLabel, Bytes.xxxLabel, DySlop.Signature.extractSignkey, DySlop.Signature.vk]
  grind

grind_pattern DY.Bytes.signkeyLabel_vk => (DySlop.Signature.vk sk).signkeyLabel tr

public
theorem DY.Bytes.signkeyLabel_later
  [BytesInvariants] [BytesInvariantsProofs]
  [DySlop.Signature.SignPred] [BytesInvariants.Has DySlop.Signature.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.signkeyLabel tr1 = b.signkeyLabel tr2
:= by
  simp only [Bytes.signkeyLabel]
  apply Bytes.xxxLabel_later DySlop.Signature.extractSignkey DySlop.Signature.extractSignkey.preserves_WellFormed

grind_pattern DY.Bytes.signkeyLabel_later => tr1 ≤ tr2, b.signkeyLabel tr1

public
theorem DY.Bytes.signkeyLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [DySlop.Signature.SignPred] [BytesInvariants.Has DySlop.Signature.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.signkeyLabel tr1 = b.signkeyLabel tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.signkeyLabel_later_fast => tr1 ≤ tr2, b.signkeyLabel tr1

end ExtractSignKey

namespace DySlop.Signature

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

variable [SignPred]
variable [BytesInvariants]
variable [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_sign`. -/
@[simp]
public
theorem sign.WellFormed
  (sk nonce msg: Bytes) (tr: ProofTrace)
  : (sign sk nonce msg).WellFormed tr = (
      sk.WellFormed tr ∧
      nonce.WellFormed tr ∧
      msg.WellFormed tr
    )
:= by
  simp [sign, Bytes.WellFormed.eq, Sign.invariants]

/-- Port of `get_label_sign`. -/
@[simp]
public
theorem sign.label
  (sk nonce msg: Bytes) (tr: ProofTrace)
  : (sign sk nonce msg).label tr = msg.label tr
:= by
  simp [sign, Bytes.label.eq, Sign.invariants]

/-- Port of `bytes_invariant_sign`. -/
public
theorem sign.Invariant
  (sk nonce msg: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : sk.Invariant tr →
    nonce.Invariant tr →
    msg.Invariant tr →
    sk.HasUsage skUsg tr →
    nonce.HasUsage Usage.sigNonce tr →
    (sk.label tr).canFlow (nonce.label tr) tr.erase →
    (
      (
        skUsg.type = "SigKey" ∧
        SignPred.pred skUsg (vk sk) msg tr
      ) ∨ (
        (sk.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (sign sk nonce msg).Invariant tr
:= by
  simp only [sign, Bytes.Invariant.eq, Sign.invariants]
  grind

grind_pattern sign.Invariant => (sign sk nonce msg).Invariant tr, sk.HasUsage skUsg tr

/-- Port of `bytes_invariant_verify`. -/
public
theorem verify.Invariant
  (vk msg sig: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : vk.Invariant tr →
    msg.Invariant tr →
    sig.Invariant tr →
    vk.SignkeyHasUsage skUsg tr →
    verify vk msg sig → (
      (
        skUsg.type = "SigKey" →
        SignPred.pred skUsg vk msg tr
      ) ∨ (
        (vk.signkeyLabel tr).canFlow Label.pub tr.erase
      )
    )
:= by
  simp only [verify]
  split
  · rename_i sk nonce msg heq
    have := Bytes.pack_view? Sign.SubF sig
    simp only [heq] at this
    subst this
    have: ({sk}: Vk.SubF Bytes).pack = CanSign.vk sk := rfl
    have := Bytes.HasUsage_inj sk skUsg
    simp_all [Bytes.Invariant.eq, Sign.invariants]
    grind
  · simp

end Invariants

section KeyPredicates

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesInvariants]

/--
  Port of `is_verification_key`.
  DY* requires `SigKey? usg`.
-/
public
def IsVerificationKey (usg: Usage) (l: Label) (b: Bytes) (tr: ProofTrace): Prop :=
  b.Publishable tr ∧
  b.signkeyLabel tr = l ∧
  b.SignkeyHasUsage usg tr

/--
  Port of `is_signature_key`.
  DY* requires `SigKey? usg`.
-/
public
def IsSignatureKey (usg: Usage) (l: Label) (b: Bytes) (tr: ProofTrace): Prop :=
  b.IsSecret l tr ∧
  b.HasUsage usg tr

end KeyPredicates

section HoareTriples

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [SignPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Hoare triple of `vk` (as DyLean's). -/
public
instance
  (sk: Bytes)
  : HoareTriplePure
    (vk sk)
    (fun tr => sk.Invariant tr)
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
    )
where
  pf := by
    grind [vk.Invariant, vk.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [SignPred]
variable [BytesInvariants.Has invariants]

/-- Port of `vk_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem vk.attackerKnowledge where
  pf := by
    simp only [vk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

/-- Port of `sign_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem sign.attackerKnowledge where
  pf := by
    simp only [sign.attackerKnowledge]
    intro out tr h_tr ⟨sk, nonce, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [sign, Bytes.Invariant.eq, Sign.invariants]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [SignPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  vk,
  sign

end AttackerKnowledgeTheorem

end DySlop.Signature
