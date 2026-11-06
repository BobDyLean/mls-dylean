module

public import MLS.Bootstrap.SymbolicSpec.State.InitKey
public import MLS.Common.Code.Crypto.Derived
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.Bootstrap.SymbolicSpec.State.InitKey
import DY.Meta.Step

/-!
Port of the labels, usages, predicates and proofs of `MLS.Bootstrap.Symbolic.State.InitKey`:
the label and usage of init keys, the properties of init keys, the invariant of init key states,
and the proofs of the traceful functions.

Port-specific differences:
- DY*'s `typed_state_pred_label (init_key_label_pred prin init_pk)` is a DyLean label
  whose corruption is the compromise of an init key state of `prin` whose init key has the public key `init_pk`
  (as `MLS.TreeSync.signatureKeyLabel`); `init_key_label_pred` is inlined in `initKeyLabel`.
- The state predicate (`bootstrap_init_key_state_pred`) is the DyLean state invariant `bootstrapInitKeyStateInv`
  (an instance, as in DyLean's examples): MLS*'s `has_bootstrap_init_key_state_invariant` is not needed.
- `InitKeyUsageT` (MLS*'s `init_key_usage_t`) has no `ParseableSerializeable` instance:
  its usage data is serialized with `serializeNE InitKeyUsageT.mf`.
- The proofs of the traceful functions (`mk_init_key_invariant`, …) are DyLean Hoare triples (instances).
  They assume the proof trace entries of the state, and the trace entries and bytes invariants of randomness
  for `mkInitKey`. The `tr_out == tr` part of their postconditions is not ported
  (DyLean's Hoare triples do not state that the trace is unchanged).
-/

namespace MLS.Bootstrap

open Comparse
open DY
open DySlop.HPKE
open MLS

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/--
Port of `init_key_label` (with `init_key_label_pred`):
the init key of `prin` with public key `initPk` is corrupt
when an init key state of `prin`, whose init key has the public key `initPk`, is compromised.
-/
@[expose]
public
def initKeyLabel (prin: Participant) (initPk: Bytes): Label where
  isCorrupt tr :=
    ∃ leafPk initSk,
      hpkePk initSk = initPk ∧
      PersistentLocalState.LocalStateCompromised prin ({ leafPk, initSk }: BootstrapInitKeyState) tr

/-- Port of `init_key_label_can_flow_public`. -/
public
theorem initKeyLabel_canFlow_pub (tr: ExecTrace) (prin: Participant) (initPk: Bytes)
  : (initKeyLabel prin initPk).canFlow Label.pub tr →
    ∃ leafPk initSk,
      PersistentLocalState.LocalStateCompromised prin ({ leafPk, initSk }: BootstrapInitKeyState) tr ∧
      hpkePk initSk = initPk
:= by
  rw [← canFlowPubEqIsCorrupt]
  grind [initKeyLabel]

/-- Port of `init_sk_to_init_key_label`. -/
public
def initSkToInitKeyLabel (prin: Participant) (initSk: Bytes): Label :=
  initKeyLabel prin (hpkePk initSk)

end Labels

section Usages

variable [HasSymbolicBytes]

/-- Port of `init_key_usage_t`. -/
public
structure InitKeyUsageT [BytesFunctor] where
  me: Participant
  leafPublicKey: Bytes

namespace InitKeyUsageT

public
def f: Participant × Bytes → InitKeyUsageT :=
  fun (me, leafPublicKey) => { me, leafPublicKey }

public
def g: InitKeyUsageT → Participant × Bytes :=
  fun { me, leafPublicKey } => (me, leafPublicKey)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end InitKeyUsageT

/-- Port of `ps_init_key_usage_t`. -/
public
def InitKeyUsageT.mf: NonExtensibleMessageFormat Bytes InitKeyUsageT :=
  .isomorphic (.prod .unboundedString .unboundedBytes) InitKeyUsageT.f InitKeyUsageT.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_init_key_usage_t_is_well_formed`. -/
@[simp]
public
theorem InitKeyUsageT.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: InitKeyUsageT):
  InitKeyUsageT.mf.wf pred x = pred x.leafPublicKey
:= by
  simp [InitKeyUsageT.mf, InitKeyUsageT.g]

/-- Port of `init_key_usage_data`. -/
@[expose]
public
def initKeyUsageData (me: Participant) (leafPublicKey: Bytes): Bytes :=
  serializeNE InitKeyUsageT.mf { me, leafPublicKey }

/-- Port of `init_key_usage`. -/
@[expose]
public
def initKeyUsage (me: Participant) (leafPublicKey: Bytes): Usage :=
  mkHpkeSkUsage ("MLS.InitHpkeKey", initKeyUsageData me leafPublicKey)

/-- Port of `entropy_usage_for_init_key`. -/
@[expose]
public
def entropyUsageForInitKey (me: Participant) (leafPublicKey: Bytes): Usage :=
  mkHpkeEntropyUsage ("MLS.InitHpkeKey", initKeyUsageData me leafPublicKey)

end Usages

section Predicates

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]

/-- Port of `is_init_key_sk`. -/
@[expose]
public
def IsInitKeySk (tr: ProofTrace) (prin: Participant) (leafPk initSk: Bytes): Prop :=
  initSk.Invariant tr ∧
  initSk.label tr = initKeyLabel prin (hpkePk initSk) ∧
  initSk.HasUsage (initKeyUsage prin leafPk) tr

/-- Port of `is_init_key_pk`. -/
@[expose]
public
def IsInitKeyPk (tr: ProofTrace) (prin: Participant) (leafPk initPk: Bytes): Prop :=
  initPk.Invariant tr ∧
  initPk.hpkeSkLabel tr = initKeyLabel prin initPk ∧
  initPk.HpkeSkHasUsage (initKeyUsage prin leafPk) tr

/-- Init keys stay init keys when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IsInitKeySk_later (tr1 tr2: ProofTrace) (prin: Participant) (leafPk initSk: Bytes)
  : tr1 ≤ tr2 →
    IsInitKeySk tr1 prin leafPk initSk →
    IsInitKeySk tr2 prin leafPk initSk
:= by
  grind [IsInitKeySk]

grind_pattern IsInitKeySk_later => tr1 ≤ tr2, IsInitKeySk tr1 prin leafPk initSk
grind_pattern [grind_later] IsInitKeySk_later => tr1 ≤ tr2, IsInitKeySk tr1 prin leafPk initSk

/-- Init public keys stay init public keys when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IsInitKeyPk_later (tr1 tr2: ProofTrace) (prin: Participant) (leafPk initPk: Bytes)
  : tr1 ≤ tr2 →
    IsInitKeyPk tr1 prin leafPk initPk →
    IsInitKeyPk tr2 prin leafPk initPk
:= by
  grind [IsInitKeyPk]

grind_pattern IsInitKeyPk_later => tr1 ≤ tr2, IsInitKeyPk tr1 prin leafPk initPk
grind_pattern [grind_later] IsInitKeyPk_later => tr1 ≤ tr2, IsInitKeyPk tr1 prin leafPk initPk

/-- Init keys satisfy the bytes invariant (for the preconditions found by `step`, as in DyLean's examples). -/
public
theorem IsInitKeySk_imp_Invariant (tr: ProofTrace) (prin: Participant) (leafPk initSk: Bytes)
  : IsInitKeySk tr prin leafPk initSk → initSk.Invariant tr
:= by
  grind [IsInitKeySk]

grind_pattern IsInitKeySk_imp_Invariant => IsInitKeySk tr prin leafPk initSk
grind_pattern [grind_later] IsInitKeySk_imp_Invariant => IsInitKeySk tr prin leafPk initSk

end Predicates

section StateInvariant

open PersistentLocalState

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT BootstrapInitKeyState)]

/--
Port of `bootstrap_init_key_state_pred`: the invariant of init key states
(MLS*'s `has_bootstrap_init_key_state_invariant` is this instance).
-/
public
instance bootstrapInitKeyStateInv: CompromisableLocalStateInv BootstrapInitKeyState where
  invariant prin st tr :=
    st.leafPk.Publishable tr ∧
    IsInitKeySk tr prin st.leafPk st.initSk
  invariant_later prin st tr1 tr2 := by
    grind [Bytes.Publishable]
  invariant_implies_KnowableBy prin st tr h := by
    obtain ⟨leafPk, initSk⟩ := st
    have hflow: (initKeyLabel prin (hpkePk initSk)).canFlow (label prin ({ leafPk, initSk }: BootstrapInitKeyState)) tr.erase := by
      simp only [Label.canFlow, initKeyLabel]
      grind
    simp only [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf,
      _root_.Comparse.NonExtensibleMessageFormat.toExtensible.wf_eq, BootstrapInitKeyState.mf.wf_eq]
    grind [IsInitKeySk, Bytes.KnowableBy, Bytes.Publishable, canFlowTrans]

end StateInvariant

section Proofs

open PersistentLocalState

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT BootstrapInitKeyState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT BootstrapInitKeyState)]

/-- Port of `mk_init_key_invariant`. -/
@[instance]
public
theorem mkInitKey.proof
  [ExecTraceTypes.Has Random.ExecEntryT] [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
  [BytesInvariants.Has DY.Random.invariants]
  (prin: Participant) (leafPk: Bytes):
  HoareTriple
    (mkInitKey prin leafPk)
    (fun tr => leafPk.Publishable tr)
    (fun _ _ => True)
:= by
  unfold mkInitKey
  step with ⟨ initSkToInitKeyLabel prin, initKeyUsage prin leafPk ⟩
  step by
    simp only [LocalStateInv.invariant]
    grind [IsInitKeySk, initSkToInitKeyLabel]
  trivial

/-- Port of `get_init_key_sk_invariant`. -/
@[instance]
public
theorem getInitKeySk.proof (prin: Participant) (sid: Nat) (leafPk: Bytes):
  HoareTriple
    (getInitKeySk prin sid leafPk)
    (fun _ => True)
    (fun initSk tr => IsInitKeySk tr prin leafPk initSk)
:= by
  unfold getInitKeySk
  step
  step
  step
  simp_all only [LocalStateInv.invariant]

/--
Port of `get_init_key_pk_invariant`.
It also states that the init public key is publishable
(in DY*, this follows from `bytes_invariant` and the label of public keys).
-/
@[instance]
public
theorem getInitKeyPk.proof (prin: Participant) (sid: Nat) (leafPk: Bytes):
  HoareTriple
    (getInitKeyPk prin sid leafPk)
    (fun _ => True)
    (fun initPk tr => IsInitKeyPk tr prin leafPk initPk ∧ initPk.Publishable tr)
:= by
  unfold getInitKeyPk
  step
  step
  grind [IsInitKeySk, IsInitKeyPk, hpkePk.Invariant, hpkeSkLabel_hpkePk, HpkeSkHasUsage_hpkePk, hpkePk.label,
    Bytes.Publishable]

end Proofs

end MLS.Bootstrap
