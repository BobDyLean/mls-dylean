/-
  Port of the MAC section of `DY.Core.Bytes`.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.Mac

public
class CanMac (Bytes: Type u) where
  /-- Port of `mac_compute`. -/
  macCompute: (key: Bytes) → (msg: Bytes) → Bytes
  /-- Port of `mac_verify`. -/
  macVerify: (key: Bytes) → (msg: Bytes) → (tag: Bytes) → Bool

export CanMac (macCompute)
export CanMac (macVerify)

section Constructors

namespace Mac

/-- Port of `Mac`. -/
public
structure SubF (Bytes: Type) where
  key: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {key, msg} => sizeOf key + sizeOf msg

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {key, msg} => {
    id := ()
    data := ()
    as := #v[key, msg]
  }
  fromRepr
  | {id, data, as} =>
    let key := as[0]
    let msg := as[1]
    { key, msg }
  from_to | {key, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {key, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end Mac

#combine into BytesFunctor, BytesLength from
  Mac

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev Mac.SubF.pack (x: Mac.SubF Bytes) := BytesView.pack x

public
instance: CanMac Bytes where
  macCompute key msg :=
    ({key, msg}: Mac.SubF Bytes).pack

  macVerify key msg tag :=
    match tag.view? Mac.SubF with
    | some { key := key', msg := msg' } =>
      key = key' && msg = msg'
    | none => false

/-- Port of `mac_verify_auth`. -/
public
theorem mac_verify_auth
  (key msg: Bytes)
  : macVerify key msg (macCompute key msg) = true
:= by
  simp only [macVerify, macCompute]
  grind

@[simp]
public
theorem length_macCompute
  [BytesLength] [BytesLength.Has SubF.length]
  (key msg: Bytes)
  : Bytes.length (macCompute key msg) = 32
:= by
  simp only [macCompute]
  grind [Mac.SubF.length]

end Constructors

section AttackerKnowledge

public
def macCompute.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key msg,
      out = macCompute key msg ∧
      p key ∧
      p msg

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  macCompute

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_macCompute
  (key msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    msg.AttackerKnows tr →
    (macCompute key msg).AttackerKnows tr
:= by
  intro h_key h_msg
  apply Bytes.AttackerKnows.prove macCompute.attackerKnowledge
  simp only [macCompute.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  Port of `mac_crypto_predicate`.
  DY* requires `MacKey? key_usage`; here, the predicate is defined on all usages.
-/
public
class MacPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] → (keyUsage: Usage) → (key msg: Bytes) → ProofTrace → Prop

/-- Port of `mac_crypto_predicate.pred_later`. -/
public
class MacPredProof [BytesInvariants] [MacPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ keyUsg key msg tr1 tr2,
      key.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      MacPred.pred keyUsg key msg tr1 →
      MacPred.pred keyUsg key msg tr2

grind_pattern MacPredProof.pred_later => tr1 ≤ tr2, MacPred.pred keyUsg key msg tr1

public
theorem MacPredProof.pred_later_fast
  [BytesInvariants] [MacPred] [MacPredProof] [BytesInvariantsProofs]
  (keyUsg: Usage) (key msg: Bytes) (tr1 tr2: ProofTrace)
  : key.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    MacPred.pred keyUsg key msg tr1 →
    MacPred.pred keyUsg key msg tr2
:= by grind

grind_pattern [grind_later] MacPredProof.pred_later_fast => tr1 ≤ tr2, MacPred.pred keyUsg key msg tr1

public
def Mac.invariants [MacPred]: Bytes.PartialInvariants Mac.SubF where
  well_formed := fun {key, msg} rec tr =>
    (rec key) tr ∧
    (rec msg) tr

  usage := fun {key := _, msg := _} _rec _tr =>
    Usage.nothing

  label := fun {key := _, msg} rec tr =>
    (rec msg) tr

  invariant := fun {key, msg} rec tr =>
    (rec key) tr ∧
    (rec msg) tr ∧
    (
      (
        -- Honest case:
        ∃ keyUsg,
        -- - the key has the usage of mac key
        key.HasUsage keyUsg tr ∧
        keyUsg.type = "MacKey" ∧
        -- - the custom (protocol-specific) invariant hold (authentication)
        MacPred.pred keyUsg key msg tr
      ) ∨ (
        -- Attacker case:
        -- the attacker knows the key
        (key.label tr).canFlow Label.pub tr.erase
      )
    )

public
theorem Mac.invariantsProofs [BytesInvariants] [MacPred] [MacPredProof]: Bytes.PartialInvariantsProofs Mac.invariants where

end Definition

#combine [MacPred] into
  BytesInvariants,
  BytesInvariantsProofs [MacPredProof]
from
  Mac

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [MacPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_mac_compute`. -/
@[simp]
public
theorem macCompute.WellFormed
  (key msg: Bytes) (tr: ProofTrace)
  : (macCompute key msg).WellFormed tr = (key.WellFormed tr ∧ msg.WellFormed tr)
:= by
  simp [macCompute, Bytes.WellFormed.eq, Mac.invariants]

/-- Port of `get_label_mac_compute`. -/
@[simp]
public
theorem macCompute.label
  (key msg: Bytes) (tr: ProofTrace)
  : (macCompute key msg).label tr = msg.label tr
:= by
  simp [macCompute, Bytes.label.eq, Mac.invariants]

/-- Port of `bytes_invariant_mac_compute`. -/
public
theorem macCompute.Invariant
  (key: Bytes) (keyUsg: Usage) (msg: Bytes) (tr: ProofTrace)
  : key.Invariant tr →
    msg.Invariant tr →
    key.HasUsage keyUsg tr →
    (
      (
        keyUsg.type = "MacKey" ∧
        MacPred.pred keyUsg key msg tr
      ) ∨ (
        (key.label tr).canFlow Label.pub tr.erase
      )
    ) →
    (macCompute key msg).Invariant tr
:= by
  simp [macCompute, Bytes.Invariant.eq, Mac.invariants]
  grind

grind_pattern macCompute.Invariant => (macCompute key msg).Invariant tr, key.HasUsage keyUsg tr

/-- Port of `bytes_invariant_mac_verify`. -/
public
theorem macVerify.Invariant
  (key: Bytes) (keyUsg: Usage) (msg tag: Bytes) (tr: ProofTrace)
  : key.Invariant tr →
    msg.Invariant tr →
    tag.Invariant tr →
    key.HasUsage keyUsg tr →
    macVerify key msg tag →
    (
      (
        keyUsg.type = "MacKey" →
        MacPred.pred keyUsg key msg tr
      ) ∨ (
        (key.label tr).canFlow Label.pub tr.erase
      )
    )
:= by
  intro h_key h_msg h_tag h_usg h_verify
  simp only [macVerify] at h_verify
  split at h_verify
  · rename_i key' msg' _
    obtain rfl: tag = ({key := key', msg := msg'}: Mac.SubF Bytes).pack := by grind
    have := Bytes.HasUsage_inj key keyUsg
    simp_all [Bytes.Invariant.eq, Mac.invariants]
    grind
  · simp at h_verify

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [MacPred]
variable [BytesInvariants.Has invariants]

/-- Port of `mac_compute_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem macCompute.attackerKnowledge where
  pf := by
    simp only [macCompute.attackerKnowledge]
    intro out tr h_tr ⟨key, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [macCompute, Bytes.Invariant.eq, Mac.invariants]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [MacPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  macCompute

end AttackerKnowledgeTheorem

end DySlop.Mac
