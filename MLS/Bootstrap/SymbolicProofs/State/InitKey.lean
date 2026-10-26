module

public import MLS.Bootstrap.SymbolicSpec.State.InitKey

/-!
Port of the labels of `MLS.Bootstrap.Symbolic.State.InitKey`: the label of init keys.

Port-specific differences:
- DY*'s `typed_state_pred_label (init_key_label_pred prin init_pk)` is a DyLean label
  whose corruption is the compromise of an init key state of `prin` whose init key has the public key `init_pk`
  (as `MLS.TreeSync.signatureKeyLabel`); `init_key_label_pred` is inlined in `initKeyLabel`.
- The usages (`init_key_usage`, …), the state invariant and the invariant proofs of the traceful functions
  are not ported yet.
-/

namespace MLS.Bootstrap

open DY
open DySlop.HPKE
open MLS

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

end MLS.Bootstrap
