module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeSync.Code.API.Types
public import MLS.TreeSync.Code.Parsers
public import MLS.TreeSync.SymbolicSpec.AuthService

/-!
Port of `MLS.TreeSync.Symbolic.State.Tree`: the public state of TreeSync.

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT (TreeSyncPublicState tkt)`):
  it has no tag (MLS*'s `local_state` instance).
- The state contains the `TreeSyncState` itself (with its group id, on which its type depends),
  instead of MLS*'s `bare_treesync_state` (which flattens it).
  Therefore MLS*'s helpers `treesync_state_to_bare_treesync_state`, `new_public_treesync_state`,
  `set_public_treesync_state` and `get_public_treesync_state` are not needed:
  the state is stored and retrieved with `PersistentLocalState.storeLocalState` and `getLocalState`.
  In particular, unlike `get_public_treesync_state`, retrieving the state does not check the TreeSync invariants
  at runtime: MLS* needs it for the refinements of `treesync_state`, which are not part of the Lean type
  (see `MLS.TreeSync.API.Types`).
- `tokens_type` and `ps_tokens_type` (which work around an F* bug) are not ported,
  and neither is `ps_dy_as_tokens` (it is `ASTokens.mf DyAsToken.mf`).
- The invariants (`treesync_public_state_pred`, …) and the proofs are in `MLS.TreeSync.SymbolicProofs.State.Tree`.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS

variable [HasSymbolicBytes]

/-- Port of `bare_treesync_state`. -/
public
structure TreeSyncPublicState (tkt: TreeKEMTypes Bytes) where
  groupId: MlsBytes Bytes
  st: TreeSyncState Bytes tkt DyAsToken groupId

namespace TreeSyncPublicState

variable {tkt: TreeKEMTypes Bytes}

public
abbrev Raw (tkt: TreeKEMTypes Bytes) :=
  MlsBytes Bytes × ((levels: Nat) × (TreeSync Bytes tkt levels × ASTokens DyAsToken levels))

public
def f: Raw tkt → TreeSyncPublicState tkt :=
  fun (groupId, ⟨levels, tree, tokens⟩) => { groupId, st := { levels, tree, tokens } }

public
def g: TreeSyncPublicState tkt → Raw tkt :=
  fun ⟨groupId, ⟨levels, tree, tokens⟩⟩ => (groupId, ⟨levels, tree, tokens⟩)

public
instance: LeftInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩
public
instance: RightInverse (g (tkt := tkt)) f := ⟨by intro _; rfl⟩

end TreeSyncPublicState

/-- Port of `ps_bare_treesync_state`. -/
public
def TreeSyncPublicState.mf (tkt: TreeKEMTypes Bytes): NonExtensibleMessageFormat Bytes (TreeSyncPublicState tkt) :=
  .isomorphic
    (.prod MlsBytes.mf (.sigma .slowNat (fun levels => .prod (TreeSync.mf tkt levels) (ASTokens.mf DyAsToken.mf levels))))
    TreeSyncPublicState.f TreeSyncPublicState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_bare_treesync_state_is_well_formed`. -/
@[simp]
public
theorem TreeSyncPublicState.mf.wf_eq (tkt: TreeKEMTypes Bytes) (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (x: TreeSyncPublicState tkt):
  (TreeSyncPublicState.mf tkt).wf pred x = (
    pred x.groupId.val ∧ (TreeSync.mf tkt x.st.levels).wf pred x.st.tree ∧
    (ASTokens.mf DyAsToken.mf x.st.levels).wf pred x.st.tokens
  )
:= by
  simp [TreeSyncPublicState.mf, TreeSyncPublicState.g]

/-- Port of `local_state_bare_treesync_state` (for its format). -/
public
instance TreeSyncPublicState.ps (tkt: TreeKEMTypes Bytes): ParseableSerializeableNE (TreeSyncPublicState tkt) :=
  .make (TreeSyncPublicState.mf tkt)

end MLS.TreeSync
