module

public import MLS.Bootstrap.SymbolicSpec.State.InitKey
public import MLS.Common.Code.Crypto.Derived

/-!
Port of the labels, usages and predicates of `MLS.Bootstrap.Symbolic.State.InitKey`:
the label and usage of init keys, and the properties of init keys.

Port-specific differences:
- DY*'s `typed_state_pred_label (init_key_label_pred prin init_pk)` is a DyLean label
  whose corruption is the compromise of an init key state of `prin` whose init key has the public key `init_pk`
  (as `MLS.TreeSync.signatureKeyLabel`); `init_key_label_pred` is inlined in `initKeyLabel`.
- The state invariant (`bootstrap_init_key_state_pred`) and the invariant proofs of the traceful functions
  (`mk_init_key_invariant`, …) are not ported yet.
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
@[expose]
public
def initSkToInitKeyLabel (prin: Participant) (initSk: Bytes): Label :=
  initKeyLabel prin (hpkePk initSk)

end Labels

section Usages

variable [HasSymbolicBytes]

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

end Predicates

end MLS.Bootstrap
