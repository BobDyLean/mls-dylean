module

public import MLS.TreeSync.SymbolicSpec.State.SignatureKey

/-!
Port of the predicates of `MLS.TreeSync.Symbolic.State.SignatureKey`:
the label of signature keys, and the properties of signature keys.

Port-specific differences:
- DY*'s `typed_state_pred_label (signature_key_label_pred prin signature_vk)` is a DyLean label
  whose corruption is the compromise of a signature key state of `prin`
  whose signature key has the verification key `signature_vk` (as DyLean's `LongTermKeys.label`).
  Since states are identified by their content (and not their tag, session identifier),
  `signature_key_label_pred` is inlined in `signatureKeyLabel`.
- The state invariant (`treesync_signature_key_state_pred`) and the invariant proofs of the traceful functions
  (`mk_signature_key_invariant`, …) are not ported yet.
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
@[expose]
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

end MLS.TreeSync
