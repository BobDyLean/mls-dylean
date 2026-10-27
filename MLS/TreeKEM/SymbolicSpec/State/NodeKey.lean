module

public import MLS.Symbolic.Code.Symbolic
public import MLS.TreeKEM.Code.Parsers

/-!
Port of `MLS.TreeKEM.Symbolic.State.NodeKey`: the state storing the private keys of a path (TreeKEM node keys).

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT TreeKEMNodeKeysState`): it has no tag.
- States are identified by handles instead of session identifiers.
- Paths are not indexed by the position of the tree and the leaf index (see `MLS.TreeKEM.Types`):
  the state only stores the height `l` (MLS* also stores `i` and `li`), and `getNodeKeys` only checks it.
- The usage and label of the leaf key (the arguments of MLS*'s `my_mk_rand`)
  are ghost arguments of the proofs in DyLean (`Random.genRand`).
- The labels, usages and predicates are in `MLS.TreeKEM.SymbolicProofs.State.NodeKey`;
  so are the state invariant and the proofs.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS

/-- Port of `treekem_node_keys_state`. -/
public
structure TreeKEMNodeKeysState [BytesFunctor] where
  l: Nat
  path: TreeKEMPriv Bytes l

variable [HasSymbolicBytes]

namespace TreeKEMNodeKeysState

public
def f: (l: Nat) × TreeKEMPriv Bytes l → TreeKEMNodeKeysState :=
  fun ⟨l, path⟩ => { l, path }

public
def g: TreeKEMNodeKeysState → (l: Nat) × TreeKEMPriv Bytes l :=
  fun { l, path } => ⟨l, path⟩

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end TreeKEMNodeKeysState

/-- Port of `ps_treekem_node_keys_state`. -/
public
def TreeKEMNodeKeysState.mf: NonExtensibleMessageFormat Bytes TreeKEMNodeKeysState :=
  .isomorphic (.sigma .slowNat TreeKEMPriv.mf) TreeKEMNodeKeysState.f TreeKEMNodeKeysState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_treekem_node_keys_state_is_well_formed`. -/
@[simp]
public
theorem TreeKEMNodeKeysState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: TreeKEMNodeKeysState):
  TreeKEMNodeKeysState.mf.wf pred x = (TreeKEMPriv.mf x.l).wf pred x.path
:= by
  simp [TreeKEMNodeKeysState.mf, TreeKEMNodeKeysState.g]

/-- Port of `local_state_treekem_node_keys_state` (for its format). -/
public
instance TreeKEMNodeKeysState.ps: ParseableSerializeableNE TreeKEMNodeKeysState :=
  .make TreeKEMNodeKeysState.mf

variable [ExecTraceTypes] [ExecTraceTypes.Has Random.ExecEntryT]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeKEMNodeKeysState)]

/--
Port of `mk_leaf_node_key`.
Returns the handle of the new state, and the public key.
-/
public
def mkLeafNodeKey (me: Participant): Traceful (Nat × Bytes) := do
  let leafSk ← Random.genRand (CryptoBytes.hpkePrivateKeyLength Bytes)
  let path: TreeKEMPriv Bytes 0 := .leaf leafSk
  let sid ← PersistentLocalState.storeLocalState me ({ l := 0, path }: TreeKEMNodeKeysState)
  pure (sid, DySlop.HPKE.hpkePk leafSk)

/--
Port of `get_node_keys`.
MLS* also checks the position of the tree and the leaf index (`i` and `li`), which are not part of the Lean types.
-/
public
def getNodeKeys {l: Nat} (me: Participant) (sid: Nat): Traceful (TreeKEMPriv Bytes l) := do
  let st: TreeKEMNodeKeysState ← PersistentLocalState.getLocalState me sid
  if h: st.l = l then
    pure (h ▸ st.path)
  else
    failure

/-- Port of `get_leaf_node_key`. -/
public
def getLeafNodeKey (me: Participant) (sid: Nat): Traceful Bytes := do
  let priv: TreeKEMPriv Bytes 0 ← getNodeKeys me sid
  match priv with
  | .leaf leafNodeKey => pure leafNodeKey

/-- Port of `store_node_keys`. Returns the handle of the new state. -/
public
def storeNodeKeys {l: Nat} (me: Participant) (path: TreeKEMPriv Bytes l): Traceful Nat :=
  PersistentLocalState.storeLocalState me ({ l, path }: TreeKEMNodeKeysState)

end MLS.TreeKEM
