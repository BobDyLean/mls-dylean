/-
  Port of the Diffie-Hellman section of `DY.Core.Bytes`.

  Compared to `DY.EquationalTheory.DiffieHellman` in DyLean:
  - `dh` takes its arguments in the order of DY* (`dh sk pk`),
  - the usage of a DH shared secret is given by `DhUsage` (DY*'s `dh_crypto_usage`),
  - the invariant requires one of the secret keys to have the usage `DhKey` (or to be public),
  - when `pk` is not a DH public key, the shared secret is public, and its invariant requires `pk` to be public.
-/

module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DySlop.EquationalTheories.Common

open DY

namespace DySlop.DiffieHellman

public
class CanDH (Bytes: Type u) where
  /-- Port of `dh_pk`. -/
  dhPk: (sk: Bytes) → Bytes
  /-- Port of `dh`. -/
  dh: (sk: Bytes) → (pk: Bytes) → Bytes

export CanDH (dhPk)
export CanDH (dh)

section Constructors

namespace DhPk

/-- Port of `DhPub`. -/
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

-- workaround for lean4#11708
theorem SubF.sizeOf_eq
  [BytesFunctor]
  (x: BytesView SubF)
  : DY.ALaCarte.FunctorSizeOf.sizeOf x = sizeOf x.sk
:= by
  cases x
  simp [DY.ALaCarte.FunctorSizeOf.sizeOf]

grind_pattern SubF.sizeOf_eq => DY.ALaCarte.FunctorSizeOf.sizeOf x

end DhPk

namespace Dh

/-- Port of `Dh`. -/
public
structure SubF (Bytes: Type) where
  sk: Bytes
  pk: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk, pk} => sizeOf sk + sizeOf pk

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {sk, pk} => {
    id := ()
    data := ()
    as := #v[sk, pk]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    let pk := as[1]
    { sk, pk }
  from_to | {sk, pk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk, pk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end Dh

#combine into BytesFunctor, BytesLength from
  DhPk,
  Dh

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev DhPk.SubF.pack (x: DhPk.SubF Bytes) := BytesView.pack x
public abbrev Dh.SubF.pack (x: Dh.SubF Bytes) := BytesView.pack x

public
instance: CanDH Bytes where
  dhPk sk :=
    ({sk}: DhPk.SubF Bytes).pack

  dh sk pk :=
    match pk.view? DhPk.SubF with
    | some { sk := sk2 } =>
      if sk ≤ sk2 then
        ({sk := sk, pk := ({sk := sk2}: DhPk.SubF Bytes).pack}: Dh.SubF Bytes).pack
      else
        ({sk := sk2, pk := ({sk := sk}: DhPk.SubF Bytes).pack}: Dh.SubF Bytes).pack
    | none =>
      ({sk, pk}: Dh.SubF Bytes).pack

/-- Port of `dh_shared_secret_lemma`. -/
public
theorem dh_shared_secret_lemma
  (x y: Bytes)
  : dh x (dhPk y) = dh y (dhPk x)
:= by
  simp only [dhPk, dh, BytesView.view_pack]
  grind

grind_pattern dh_shared_secret_lemma => dh x (dhPk y), dh y (dhPk x)

@[simp]
public
theorem length_dhPk
  [BytesLength] [BytesLength.Has SubF.length]
  (sk: Bytes)
  : Bytes.length (dhPk sk) = 32
:= by
  simp only [dhPk]
  grind [DhPk.SubF.length]

end Constructors

section AttackerKnowledge

public
def dhPk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = dhPk sk ∧
      p sk

public
def dh.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk pk,
      out = dh sk pk ∧
      p sk ∧
      p pk

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  dhPk,
  dh

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_dhPk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (dhPk sk).AttackerKnows tr
:= by
  intro h_sk
  apply Bytes.AttackerKnows.prove dhPk.attackerKnowledge
  simp only [dhPk.attackerKnowledge]
  grind

public
theorem attacker_knows_dh
  (sk pk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    pk.AttackerKnows tr →
    (dh sk pk).AttackerKnows tr
:= by
  intro h_sk h_pk
  apply Bytes.AttackerKnows.prove dh.attackerKnowledge
  simp only [dh.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def DhPk.invariants: Bytes.PartialInvariants DhPk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := _} _rec _tr =>
    Usage.nothing

  label := fun {sk := _} _rec _tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
theorem DhPk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs DhPk.invariants where

end Definition

section DhPkLemmas

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has DiffieHellman.SubF]
variable [BytesInvariants] [BytesInvariants.Has DhPk.invariants]

/-- Port of `bytes_well_formed_dh_pk`. -/
@[simp]
public
theorem dhPk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  : (dhPk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [dhPk, Bytes.WellFormed.eq, DhPk.invariants]

/-- Port of `get_label_dh_pk`. -/
@[simp]
public
theorem dhPk.label
  (sk: Bytes) (tr: ProofTrace)
  : (dhPk sk).label tr = Label.pub
:= by
  simp [dhPk, Bytes.label.eq, DhPk.invariants]

/-- Port of `bytes_invariant_dh_pk`. -/
@[simp]
public
theorem dhPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : (dhPk sk).Invariant tr = sk.Invariant tr
:= by
  simp [dhPk, Bytes.Invariant.eq, DhPk.invariants]

end DhPkLemmas

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

/--
  Port of `dh_crypto_usage`.
  DY* requires the arguments of `known_peer_usage` and `unknown_peer_usage` to be `DhKey` usages;
  here, these functions are defined on all usages.
-/
public
class DhUsage where
  knownPeerUsage: Usage → Usage → Usage
  unknownPeerUsage: Usage → Usage
  knownPeerUsage_commutes:
    ∀ usg1 usg2,
      usg1.type = "DhKey" →
      usg2.type = "DhKey" →
      knownPeerUsage usg1 usg2 = knownPeerUsage usg2 usg1
  unknownPeerUsage_implies:
    ∀ usg1 usg2,
      usg1.type = "DhKey" →
      usg2.type = "DhKey" →
      unknownPeerUsage usg1 ≠ Usage.nothing →
      knownPeerUsage usg1 usg2 = unknownPeerUsage usg1

/-- Port of `default_dh_crypto_usage`. -/
@[instance_reducible]
public
def DhUsage.default: DhUsage where
  knownPeerUsage _ _ := Usage.nothing
  unknownPeerUsage _ := Usage.nothing
  knownPeerUsage_commutes := by grind
  unknownPeerUsage_implies := by grind

/--
  The usage of `Dh sk1 (DhPub sk2)`,
  given the usages `usg1` of `sk1` and `usg2` of `sk2` (a case of DY*'s `get_usage`).
-/
@[expose]
public
def sharedSecretUsage [DhUsage] (usg1 usg2: Usage): Usage :=
  if usg1.type = "DhKey" then
    if usg2.type = "DhKey" then
      DhUsage.knownPeerUsage usg1 usg2
    else
      DhUsage.unknownPeerUsage usg1
  else if usg2.type = "DhKey" then
    DhUsage.unknownPeerUsage usg2
  else
    Usage.nothing

omit [ExecTraceTypes] [ProofTraceTypes] in
public
theorem sharedSecretUsage_comm [DhUsage] (usg1 usg2: Usage)
  : sharedSecretUsage usg1 usg2 = sharedSecretUsage usg2 usg1
:= by
  have := DhUsage.knownPeerUsage_commutes usg1 usg2
  grind [sharedSecretUsage]

public
def Dh.invariants [BytesFunctor.Has DiffieHellman.SubF] [DhUsage]: Bytes.PartialInvariants Dh.SubF where
  well_formed := fun {sk, pk} rec tr =>
      (rec sk) tr ∧
      (rec pk) tr

  usage := fun {sk, pk} rec tr =>
    match _: pk.view? DhPk.SubF with
    | some {sk := sk2} =>
      sharedSecretUsage ((rec sk) tr) ((rec sk2) tr)
    | none =>
      if ((rec sk) tr).type = "DhKey" then
        DhUsage.unknownPeerUsage ((rec sk) tr)
      else
        Usage.nothing

  label := fun {sk, pk} rec tr =>
    match _: pk.view? DhPk.SubF with
    | some {sk := sk2} =>
      Label.join ((rec sk) tr) ((rec sk2) tr)
    | none => Label.pub

  invariant := fun {sk, pk} rec tr =>
    match _: pk.view? DhPk.SubF with
    | some {sk := sk2} =>
      (rec sk) tr ∧
      (rec sk2) tr ∧
      (
        (
          -- Honest case:
          -- - one of the keys have the correct usage
          (∃ usg1, sk.HasUsage usg1 tr ∧ usg1.type = "DhKey") ∨
          (∃ usg2, sk2.HasUsage usg2 tr ∧ usg2.type = "DhKey")
        ) ∨ (
          -- Attacker case:
          -- the attacker knows one of the secret keys
          (sk.label tr).canFlow Label.pub tr.erase ∨
          (sk2.label tr).canFlow Label.pub tr.erase
        )
      )
    | none =>
      (rec pk) tr ∧
      (rec sk) tr ∧
      (pk.label tr).canFlow Label.pub tr.erase ∧
      (
        (
          ∃ usg, sk.HasUsage usg tr ∧ usg.type = "DhKey"
        ) ∨ (
          (sk.label tr).canFlow Label.pub tr.erase
        )
      )

public
theorem Dh.invariantsProofs [BytesFunctor.Has DiffieHellman.SubF] [DhUsage] [BytesInvariants] [BytesInvariants.Has DhPk.invariants]: Bytes.PartialInvariantsProofs Dh.invariants where
  usage_later := by
    intro x rec tr1 tr2
    cases x
    simp_all [DhPk.invariants, invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetUsageLaterT]
    split <;> grind
  label_later := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [DhPk.invariants, invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, GetLabelLaterT]
    split <;> grind
  invariant_implies_wellformed := by
    intro x rec tr
    cases x
    simp_all [DhPk.invariants, invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantImpliesBytesWellFormedT]
    split <;> grind
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [DhPk.invariants, invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    split <;> grind

end Definition

#combine [BytesFunctor.Has SubF] [DhUsage] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has DhPk.invariants]
from
  DhPk,
  Dh

end Invariants

-- Temporarily close the namespace to define `Bytes.dhLabel` and `Bytes.DhHasUsage`
end DySlop.DiffieHellman

section ExtractDhSk

variable [BytesFunctor] [BytesFunctor.Has DySlop.DiffieHellman.SubF]

/-- Port of `extract_dh_sk`. -/
public
noncomputable
def DySlop.DiffieHellman.extractDhSk (pk: Bytes): Option Bytes :=
  match pk.view? DySlop.DiffieHellman.DhPk.SubF with
  | some { sk } =>
    some sk
  | none => none

theorem DySlop.DiffieHellman.dhPk_extractDhSk (b: Bytes):
  match extractDhSk b with
  | none => True
  | some sk => b = DySlop.DiffieHellman.dhPk sk
:= by
  simp [extractDhSk, DySlop.DiffieHellman.dhPk]
  grind

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `extract_dh_sk_preserves_well_formedness`. -/
theorem DySlop.DiffieHellman.extractDhSk.preserves_WellFormed
  [DySlop.DiffieHellman.DhUsage]
  [BytesInvariants] [BytesInvariants.Has DySlop.DiffieHellman.invariants]
: ExtractPreservesWellFormed extractDhSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [DySlop.DiffieHellman.dhPk_extractDhSk, DySlop.DiffieHellman.dhPk.WellFormed]

/-- Port of `get_dh_label`. -/
@[expose]
public
noncomputable
def DY.Bytes.dhLabel
  [BytesInvariants]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DySlop.DiffieHellman.extractDhSk pk tr

/-- Port of `get_dh_label_dh_pk`. -/
public
theorem DY.Bytes.dhLabel_dhPk
  [BytesInvariants]
  (sk: Bytes) (tr: ProofTrace)
  : (DySlop.DiffieHellman.dhPk sk).dhLabel tr = sk.label tr
:= by
  simp [Bytes.dhLabel, Bytes.xxxLabel, DySlop.DiffieHellman.extractDhSk, DySlop.DiffieHellman.dhPk]
  grind

grind_pattern DY.Bytes.dhLabel_dhPk => (DySlop.DiffieHellman.dhPk sk).dhLabel tr

public
theorem DY.Bytes.dhLabel_later
  [DySlop.DiffieHellman.DhUsage]
  [BytesInvariants] [BytesInvariants.Has DySlop.DiffieHellman.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.dhLabel tr1 = b.dhLabel tr2
:= by
  simp only [Bytes.dhLabel]
  apply Bytes.xxxLabel_later DySlop.DiffieHellman.extractDhSk DySlop.DiffieHellman.extractDhSk.preserves_WellFormed

grind_pattern DY.Bytes.dhLabel_later => tr1 ≤ tr2, b.dhLabel tr1

public
theorem DY.Bytes.dhLabel_later_fast
  [DySlop.DiffieHellman.DhUsage]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.DiffieHellman.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.dhLabel tr1 = b.dhLabel tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.dhLabel_later_fast => tr1 ≤ tr2, b.dhLabel tr1

/-- Port of `has_dh_usage`. -/
@[expose]
public
def DY.Bytes.DhHasUsage
  [BytesInvariants]
  (pk: Bytes) (usg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage DySlop.DiffieHellman.extractDhSk pk usg tr

/-- Port of `has_dh_usage_dh_pk`. -/
public
theorem DY.Bytes.DhHasUsage_dhPk
  [BytesInvariants]
  (sk: Bytes) (usg: Usage) (tr: ProofTrace)
  : (DySlop.DiffieHellman.dhPk sk).DhHasUsage usg tr = sk.HasUsage usg tr
:= by
  simp [Bytes.DhHasUsage, Bytes.XXXHasUsage, DySlop.DiffieHellman.extractDhSk, DySlop.DiffieHellman.dhPk]
  grind

grind_pattern DY.Bytes.DhHasUsage_dhPk => (DySlop.DiffieHellman.dhPk sk).DhHasUsage usg tr

public
theorem DY.Bytes.DhHasUsage_later
  [DySlop.DiffieHellman.DhUsage]
  [BytesInvariants] [BytesInvariants.Has DySlop.DiffieHellman.invariants]
  [GetUsageLater] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.DhHasUsage usg tr1 →
    b.DhHasUsage usg tr2
:= by
  simp only [Bytes.DhHasUsage]
  apply Bytes.XXXHasUsage_later DySlop.DiffieHellman.extractDhSk DySlop.DiffieHellman.extractDhSk.preserves_WellFormed

grind_pattern DY.Bytes.DhHasUsage_later => tr1 ≤ tr2, b.DhHasUsage usg tr1

public
theorem DY.Bytes.DhHasUsage_later_fast
  [DySlop.DiffieHellman.DhUsage]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has DySlop.DiffieHellman.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.DhHasUsage usg tr1 →
    b.DhHasUsage usg tr2
:= by grind

grind_pattern [grind_later] DY.Bytes.DhHasUsage_later_fast => tr1 ≤ tr2, b.DhHasUsage usg tr1

end ExtractDhSk

namespace DySlop.DiffieHellman

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [DhUsage]
variable [BytesInvariants] [BytesInvariants.Has invariants]

/-- Port of `bytes_well_formed_dh`. -/
@[simp]
public
theorem dh.WellFormed
  (sk pk: Bytes) (tr: ProofTrace)
  : (dh sk pk).WellFormed tr = (sk.WellFormed tr ∧ pk.WellFormed tr)
:= by
  simp only [dh]
  split
  · rename_i sk2 _
    obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
    split <;> simp [Dh.invariants, DhPk.invariants] <;> grind
  · simp [Dh.invariants]

/-- Port of `get_label_dh`. -/
@[simp]
public
theorem dh.label
  (sk pk: Bytes) (tr: ProofTrace)
  : (dh sk pk).label tr = Label.join (sk.label tr) (pk.dhLabel tr)
:= by
  simp only [dh, Bytes.dhLabel, Bytes.xxxLabel, extractDhSk]
  split
  · rename_i sk2 _
    obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
    split <;> simp [Dh.invariants] <;> grind [Label.join_commutes]
  · simp only [Bytes.label.eq, Dh.invariants]
    split <;> grind

/-- Port of `bytes_invariant_dh`. -/
public
theorem dh.Invariant
  (sk: Bytes) (skUsg: Usage) (pk: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    sk.HasUsage skUsg tr →
    skUsg.type = "DhKey" →
    pk.Publishable tr →
    (dh sk pk).Invariant tr
:= by
  simp only [dh]
  split
  · rename_i sk2 _
    obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
    split <;> simp [Bytes.Publishable, Dh.invariants, DhPk.invariants] <;> grind
  · simp only [Bytes.Invariant.eq, Dh.invariants]
    split <;> grind

grind_pattern dh.Invariant => (dh sk pk).Invariant tr, sk.HasUsage skUsg tr

/-- Port of `has_usage_dh_known_peer`. -/
public
theorem dh.HasUsage_knownPeer
  (sk: Bytes) (skUsg: Usage) (pk: Bytes) (pkUsg: Usage) (tr: ProofTrace)
  : sk.HasUsage skUsg tr →
    skUsg.type = "DhKey" →
    pk.DhHasUsage pkUsg tr →
    pkUsg.type = "DhKey" →
    (dh sk pk).HasUsage (DhUsage.knownPeerUsage skUsg pkUsg) tr
:= by
  have := DhUsage.knownPeerUsage_commutes skUsg pkUsg
  simp only [dh, Bytes.HasUsage]
  split
  · rename_i sk2 _
    obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
    simp only [Bytes.DhHasUsage, Bytes.XXXHasUsage, Bytes.HasUsage, extractDhSk, BytesView.view_pack] at *
    split <;> simp [Dh.invariants] <;> grind [sharedSecretUsage]
  · simp only [Bytes.label.eq, Dh.invariants]
    split <;> grind

grind_pattern dh.HasUsage_knownPeer =>
  (dh sk pk).HasUsage (DhUsage.knownPeerUsage skUsg pkUsg) tr,
  sk.HasUsage skUsg tr,
  pk.DhHasUsage pkUsg tr

/-- Port of `has_usage_dh_unknown_peer`. -/
public
theorem dh.HasUsage_unknownPeer
  (sk: Bytes) (skUsg: Usage) (pk: Bytes) (tr: ProofTrace)
  : sk.HasUsage skUsg tr →
    skUsg.type = "DhKey" →
    DhUsage.unknownPeerUsage skUsg ≠ Usage.nothing →
    (dh sk pk).HasUsage (DhUsage.unknownPeerUsage skUsg) tr
:= by
  have := DhUsage.unknownPeerUsage_implies skUsg
  have := DhUsage.knownPeerUsage_commutes skUsg
  simp only [dh, Bytes.HasUsage]
  split
  · rename_i sk2 _
    obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
    split <;> simp [Dh.invariants] <;> grind [sharedSecretUsage]
  · simp only [Bytes.usage.eq, Bytes.label.eq, Dh.invariants]
    split <;> grind

grind_pattern dh.HasUsage_unknownPeer =>
  (dh sk pk).HasUsage (DhUsage.unknownPeerUsage skUsg) tr,
  sk.HasUsage skUsg tr

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [DhUsage]
variable [BytesInvariants.Has invariants]

/-- Port of `dh_pk_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem dhPk.attackerKnowledge where
  pf := by
    simp only [dhPk.attackerKnowledge]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind

/-- Port of `dh_preserves_publishability`. -/
public
instance: SubAttackerKnowledgeTheorem dh.attackerKnowledge where
  pf := by
    simp only [dh.attackerKnowledge]
    intro out tr h_tr ⟨sk, pk, ⟨ h_out, h_sk, h_pk ⟩⟩
    subst h_out
    simp only [Bytes.Publishable, dh] at *
    split
    · rename_i sk2 _
      obtain rfl: pk = ({sk := sk2}: DhPk.SubF Bytes).pack := by grind
      split <;> simp [Dh.invariants, DhPk.invariants] at * <;> grind
    · simp only [Bytes.Invariant.eq, Bytes.label.eq, Dh.invariants]
      split <;> grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [DhUsage] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  dhPk,
  dh

end AttackerKnowledgeTheorem

end DySlop.DiffieHellman
