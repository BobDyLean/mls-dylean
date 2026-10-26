module

public import MLS.Symbolic.Code.Symbolic

/-!
Port of `MLS.Bootstrap.Symbolic.State.InitKey`: the state storing an init key (HPKE private key of a key package).

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState`): it has no tag.
- States are identified by handles instead of session identifiers.
- The usage and label of the init key (the arguments of MLS*'s `my_mk_rand`)
  are ghost arguments of the proofs in DyLean (`Random.genRand`).
- The labels, usages, invariants and proofs are not ported yet.
-/

namespace MLS.Bootstrap

open Comparse
open DY DY.Comparse
open MLS

/-- Port of `bootstrap_init_key_state`. -/
public
structure BootstrapInitKeyState [BytesFunctor] where
  leafPk: Bytes
  initSk: Bytes

variable [HasSymbolicBytes]

namespace BootstrapInitKeyState

public
def f: Bytes × Bytes → BootstrapInitKeyState :=
  fun (leafPk, initSk) => { leafPk, initSk }

public
def g: BootstrapInitKeyState → Bytes × Bytes :=
  fun { leafPk, initSk } => (leafPk, initSk)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end BootstrapInitKeyState

/-- Port of `ps_bootstrap_init_key_state`. -/
public
def BootstrapInitKeyState.mf: NonExtensibleMessageFormat Bytes BootstrapInitKeyState :=
  .isomorphic (.prod .slowBytes .slowBytes) BootstrapInitKeyState.f BootstrapInitKeyState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_bootstrap_init_key_state_is_well_formed`. -/
@[simp]
public
theorem BootstrapInitKeyState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: BootstrapInitKeyState):
  BootstrapInitKeyState.mf.wf pred x = (pred x.leafPk ∧ pred x.initSk)
:= by
  simp [BootstrapInitKeyState.mf, BootstrapInitKeyState.g]

/-- Port of `local_state_bootstrap_init_key_state` (for its format). -/
public
instance BootstrapInitKeyState.ps: ParseableSerializeableNE BootstrapInitKeyState :=
  .make BootstrapInitKeyState.mf

variable [ExecTraceTypes] [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT BootstrapInitKeyState)]

/-- Port of `mk_init_key`. Returns the handle of the new state. -/
public
def mkInitKey (prin: Participant) (leafPk: Bytes): Traceful Nat := do
  let initSk ← Random.genRand 32
  PersistentLocalState.storeLocalState prin ({ leafPk, initSk }: BootstrapInitKeyState)

/-- Port of `get_init_key_sk`. -/
public
def getInitKeySk (prin: Participant) (sid: Nat) (leafPk: Bytes): Traceful Bytes := do
  let st: BootstrapInitKeyState ← PersistentLocalState.getLocalState prin sid
  guard (leafPk = st.leafPk)
  pure st.initSk

/-- Port of `get_init_key_pk`. -/
public
def getInitKeyPk (prin: Participant) (sid: Nat) (leafPk: Bytes): Traceful Bytes := do
  let initSk ← getInitKeySk prin sid leafPk
  pure (DySlop.HPKE.hpkePk initSk)

end MLS.Bootstrap
