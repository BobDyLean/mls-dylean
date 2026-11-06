module

public import MLS.TreeSync.SymbolicSpec.State.SignatureKey
public import MLS.Symbolic.SymbolicProofs.MiscLemmas
import all MLS.TreeSync.SymbolicSpec.State.SignatureKey
import DY.Meta.Step

/-!
Port of the predicates and proofs of `MLS.TreeSync.Symbolic.State.SignatureKey`:
the label of signature keys, the properties of signature keys, the invariant of signature key states,
and the proofs of the traceful functions.

Port-specific differences:
- DY*'s `typed_state_pred_label (signature_key_label_pred prin signature_vk)` is a DyLean label
  whose corruption is the compromise of a signature key state of `prin`
  whose signature key has the verification key `signature_vk` (as DyLean's `LongTermKeys.label`).
  Since states are identified by their content (and not their tag, session identifier),
  `signature_key_label_pred` is inlined in `signatureKeyLabel`.
- The state predicate (`treesync_signature_key_state_pred`) is the DyLean state invariant
  `treeSyncSignatureKeyStateInv` (an instance, as in DyLean's examples): MLS*'s `has_treesync_signature_key_state_invariant`
  is not needed.
- The proofs of the traceful functions (`mk_signature_key_invariant`, …) are DyLean Hoare triples (instances).
  They assume the proof trace entries of the state, and the trace entries and bytes invariants of randomness
  for `mkSignatureKey`.
- `get_signature_key_sk_invariant` and `get_signature_key_vk_invariant` also state that the trace is unchanged;
  DyLean's Hoare triples do not.
-/

namespace MLS.TreeSync

open DY
open MLS

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/--
Port of `signature_key_label` (with `signature_key_label_pred`):
the signature key of `prin` with verification key `signatureVk` is corrupt
when a signature key state of `prin`, whose signature key has the verification key `signatureVk`, is compromised.
-/
@[expose]
public
def signatureKeyLabel (prin: Participant) (signatureVk: Bytes): Label where
  isCorrupt tr :=
    ∃ signatureSk,
      DySlop.Signature.vk signatureSk = signatureVk ∧
      PersistentLocalState.LocalStateCompromised prin ({ signatureSk }: TreeSyncSignatureKeyState) tr

/-- Port of `signature_key_label_can_flow_public`. -/
public
theorem signatureKeyLabel_canFlow_pub (tr: ExecTrace) (prin: Participant) (signatureVk: Bytes)
  : (signatureKeyLabel prin signatureVk).canFlow Label.pub tr →
    ∃ signatureSk,
      PersistentLocalState.LocalStateCompromised prin ({ signatureSk }: TreeSyncSignatureKeyState) tr ∧
      DySlop.Signature.vk signatureSk = signatureVk
:= by
  rw [← canFlowPubEqIsCorrupt]
  grind [signatureKeyLabel]

/-- Port of `signature_sk_to_signature_key_label`. -/
public
def signatureSkToSignatureKeyLabel (prin: Participant) (signatureSk: Bytes): Label :=
  signatureKeyLabel prin (DySlop.Signature.vk signatureSk)

end Labels

section Predicates

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/-- Port of `is_signature_key_sk`. -/
@[expose]
public
def IsSignatureKeySk (tr: ProofTrace) (prin: Participant) (signatureSk: Bytes): Prop :=
  signatureSk.Invariant tr ∧
  signatureSk.label tr = signatureKeyLabel prin (DySlop.Signature.vk signatureSk) ∧
  signatureSk.HasUsage (mkMlsSigkeyUsage prin) tr

/-- Port of `is_signature_key_vk`. -/
@[expose]
public
def IsSignatureKeyVk (tr: ProofTrace) (prin: Participant) (signatureVk: Bytes): Prop :=
  signatureVk.Publishable tr ∧
  signatureVk.signkeyLabel tr = signatureKeyLabel prin signatureVk ∧
  signatureVk.SignkeyHasUsage (mkMlsSigkeyUsage prin) tr

/-- Signature keys stay signature keys when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IsSignatureKeySk_later (tr1 tr2: ProofTrace) (prin: Participant) (signatureSk: Bytes)
  : tr1 ≤ tr2 →
    IsSignatureKeySk tr1 prin signatureSk →
    IsSignatureKeySk tr2 prin signatureSk
:= by
  grind [IsSignatureKeySk]

grind_pattern IsSignatureKeySk_later => tr1 ≤ tr2, IsSignatureKeySk tr1 prin signatureSk
grind_pattern [grind_later] IsSignatureKeySk_later => tr1 ≤ tr2, IsSignatureKeySk tr1 prin signatureSk

/-- Signature keys satisfy the bytes invariant (for the preconditions found by `step`, as in DyLean's examples). -/
public
theorem IsSignatureKeySk_imp_Invariant (tr: ProofTrace) (prin: Participant) (signatureSk: Bytes)
  : IsSignatureKeySk tr prin signatureSk → signatureSk.Invariant tr
:= by
  grind [IsSignatureKeySk]

grind_pattern IsSignatureKeySk_imp_Invariant => IsSignatureKeySk tr prin signatureSk
grind_pattern [grind_later] IsSignatureKeySk_imp_Invariant => IsSignatureKeySk tr prin signatureSk

/-- Verification keys stay verification keys when the trace grows (MLS* uses an SMT pattern). -/
public
theorem IsSignatureKeyVk_later (tr1 tr2: ProofTrace) (prin: Participant) (signatureVk: Bytes)
  : tr1 ≤ tr2 →
    IsSignatureKeyVk tr1 prin signatureVk →
    IsSignatureKeyVk tr2 prin signatureVk
:= by
  grind [IsSignatureKeyVk]

grind_pattern IsSignatureKeyVk_later => tr1 ≤ tr2, IsSignatureKeyVk tr1 prin signatureVk
grind_pattern [grind_later] IsSignatureKeyVk_later => tr1 ≤ tr2, IsSignatureKeyVk tr1 prin signatureVk

end Predicates

section StateInvariant

open PersistentLocalState

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]

/--
Port of `treesync_signature_key_state_pred`: the invariant of signature key states
(MLS*'s `has_treesync_signature_key_state_invariant` is this instance).
-/
public
instance treeSyncSignatureKeyStateInv: CompromisableLocalStateInv TreeSyncSignatureKeyState where
  invariant prin st tr := IsSignatureKeySk tr prin st.signatureSk
  invariant_later prin st tr1 tr2 := by
    grind [IsSignatureKeySk]
  invariant_implies_KnowableBy prin st tr h := by
    obtain ⟨sk⟩ := st
    have hflow: (signatureKeyLabel prin (DySlop.Signature.vk sk)).canFlow (label prin ({ signatureSk := sk }: TreeSyncSignatureKeyState)) tr.erase := by
      simp only [Label.canFlow, signatureKeyLabel]
      grind
    simp only [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf, Comparse.ParseableSerializeableNE.mf,
      _root_.Comparse.NonExtensibleMessageFormat.toExtensible.wf_eq, TreeSyncSignatureKeyState.mf.wf_eq]
    grind [IsSignatureKeySk, Bytes.KnowableBy]

end StateInvariant

section Proofs

open PersistentLocalState

variable [HasSymbolicInvariants] [TraceInvariant]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT TreeSyncSignatureKeyState)]

/-- Port of `mk_signature_key_invariant`. -/
@[instance]
public
theorem mkSignatureKey.proof
  [ExecTraceTypes.Has Random.ExecEntryT] [ProofTraceTypes.Has Random.ProofEntryT] [TraceInvariant.Has Random.ProofEntryT]
  [BytesInvariants.Has DY.Random.invariants]
  (prin: Participant):
  HoareTriple
    (mkSignatureKey prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold mkSignatureKey
  step with ⟨ signatureSkToSignatureKeyLabel prin, mkMlsSigkeyUsage prin ⟩
  step by
    simp only [LocalStateInv.invariant]
    grind [IsSignatureKeySk, signatureSkToSignatureKeyLabel]
  trivial

/-- Port of `get_signature_key_sk_invariant`. -/
@[instance]
public
theorem getSignatureKeySk.proof (prin: Participant) (sid: Nat):
  HoareTriple
    (getSignatureKeySk prin sid)
    (fun _ => True)
    (fun signatureSk tr => IsSignatureKeySk tr prin signatureSk)
:= by
  unfold getSignatureKeySk
  step
  step
  simp_all only [LocalStateInv.invariant]

/-- Port of `get_signature_key_vk_invariant`. -/
@[instance]
public
theorem getSignatureKeyVk.proof (prin: Participant) (sid: Nat):
  HoareTriple
    (getSignatureKeyVk prin sid)
    (fun _ => True)
    (fun signatureVk tr => IsSignatureKeyVk tr prin signatureVk)
:= by
  unfold getSignatureKeyVk
  step
  hoist
  step
  step
  grind [IsSignatureKeySk, IsSignatureKeyVk]

end Proofs

end MLS.TreeSync
