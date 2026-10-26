module

public import MLS.TreeKEM.Code.API.Types
public import MLS.TreeSync.SymbolicSpec.State.Tree
public import MLS.TreeKEM.SymbolicSpec.State.NodeKey
public import MLS.TreeKEM.SymbolicSpec.State.EpochSecrets

/-!
Port of `MLS.TreeKEM.Symbolic.State.API`: the state of a principal in a group.
The TreeSync and TreeKEM trees are stored in one state,
while the secrets are stored in their own states (`MLS.TreeKEM.SymbolicSpec.State.NodeKey`,
`MLS.TreeKEM.SymbolicSpec.State.EpochSecrets`), whose handles are stored.

Port-specific differences:
- The state is a DyLean local state, with its own trace entry type
  (`PersistentLocalState.CompromisableState.ExecEntryT BareTreeSyncTreeKEMState`): it has no tag.
- States are identified by handles instead of session identifiers.
- The TreeSync part is a `TreeSyncPublicState` (MLS*'s `bare_treesync_state`), which contains the `TreeSyncState`.
- `getTreesyncTreekemState` only checks what the Lean types need (the group identifier of the TreeSync state),
  and not the TreeSync and TreeKEM invariants, nor the relation between the TreeSync and TreeKEM trees
  (MLS* checks them for its refinement types, see `MLS.TreeSync.SymbolicSpec.State.Tree`):
  they follow from the state invariant.
- The invariants (`treesync_treekem_state_pred`, `treesync_treekem_state_invariant`, …) and the proofs are not ported yet.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync

variable [HasSymbolicBytes]

/-- Port of `bare_treekem_state`. -/
public
structure BareTreeKEMState where
  -- tree state
  levels: Nat
  tree: TreeKEM Bytes levels
  privSid: Nat
  -- key schedule state
  senderDataSecretSid: Nat
  exporterSecretSid: Nat
  externalSecretSid: Nat
  membershipKeySid: Nat
  resumptionPskSid: Nat
  epochAuthenticatorSid: Nat
  confirmationTag: Bytes
  initSecretSid: Nat

namespace BareTreeKEMState

public
abbrev Raw :=
  (levels: Nat) × (TreeKEM Bytes levels × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bytes × Nat)

public
def f: Raw → BareTreeKEMState :=
  fun ⟨levels, tree, privSid, senderDataSecretSid, exporterSecretSid, externalSecretSid, membershipKeySid,
      resumptionPskSid, epochAuthenticatorSid, confirmationTag, initSecretSid⟩ =>
    { levels, tree, privSid, senderDataSecretSid, exporterSecretSid, externalSecretSid, membershipKeySid,
      resumptionPskSid, epochAuthenticatorSid, confirmationTag, initSecretSid }

public
def g: BareTreeKEMState → Raw :=
  fun x =>
    ⟨x.levels, x.tree, x.privSid, x.senderDataSecretSid, x.exporterSecretSid, x.externalSecretSid, x.membershipKeySid,
      x.resumptionPskSid, x.epochAuthenticatorSid, x.confirmationTag, x.initSecretSid⟩

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end BareTreeKEMState

/-- Port of `ps_bare_treekem_state`. -/
public
def BareTreeKEMState.mf: NonExtensibleMessageFormat Bytes BareTreeKEMState :=
  .isomorphic
    (.sigma .slowNat (fun levels =>
      .prod (TreeKEM.mf levels) (.prod .slowNat (.prod .slowNat (.prod .slowNat (.prod .slowNat (.prod .slowNat
        (.prod .slowNat (.prod .slowNat (.prod .slowBytes .slowNat))))))))))
    BareTreeKEMState.f BareTreeKEMState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_bare_treekem_state_is_well_formed`. -/
@[simp]
public
theorem BareTreeKEMState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: BareTreeKEMState):
  BareTreeKEMState.mf.wf pred x = ((TreeKEM.mf x.levels).wf pred x.tree ∧ pred x.confirmationTag)
:= by
  simp only [BareTreeKEMState.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, BareTreeKEMState.g,
    NonExtensibleMessageFormat.sigma.wf_eq, NonExtensibleMessageFormat.prod.wf_eq,
    NonExtensibleMessageFormat.slowNat.wf_eq, NonExtensibleMessageFormat.slowBytes.wf_eq, true_and, and_true]

/-- Port of `bare_treesync_treekem_state`. -/
public
structure BareTreeSyncTreeKEMState where
  leafIndex: Nat
  groupContext: GroupContext Bytes
  mySignatureKeySid: Nat
  treesync: TreeSyncPublicState tkt
  treekem: BareTreeKEMState

namespace BareTreeSyncTreeKEMState

public
abbrev Raw :=
  Nat × GroupContext Bytes × Nat × TreeSyncPublicState tkt × BareTreeKEMState

public
def f: Raw → BareTreeSyncTreeKEMState :=
  fun (leafIndex, groupContext, mySignatureKeySid, treesync, treekem) =>
    { leafIndex, groupContext, mySignatureKeySid, treesync, treekem }

public
def g: BareTreeSyncTreeKEMState → Raw :=
  fun { leafIndex, groupContext, mySignatureKeySid, treesync, treekem } =>
    (leafIndex, groupContext, mySignatureKeySid, treesync, treekem)

public
instance: LeftInverse g f := ⟨by intro _; rfl⟩
public
instance: RightInverse g f := ⟨by intro _; rfl⟩

end BareTreeSyncTreeKEMState

/-- Port of `ps_bare_treesync_treekem_state`. -/
public
def BareTreeSyncTreeKEMState.mf: NonExtensibleMessageFormat Bytes BareTreeSyncTreeKEMState :=
  .isomorphic
    (.prod .slowNat (.prod GroupContext.mf (.prod .slowNat (.prod (TreeSyncPublicState.mf tkt) BareTreeKEMState.mf))))
    BareTreeSyncTreeKEMState.f BareTreeSyncTreeKEMState.g
deriving NonExtensibleMessageFormat.IsNonAmbiguous, NonExtensibleMessageFormat.HasUniqueRepresentation, NonExtensibleMessageFormat.ParseConsumes

/-- Port of `ps_bare_treesync_treekem_state_is_well_formed`. -/
@[simp]
public
theorem BareTreeSyncTreeKEMState.mf.wf_eq (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: BareTreeSyncTreeKEMState):
  BareTreeSyncTreeKEMState.mf.wf pred x = (
    GroupContext.mf.wf pred x.groupContext ∧ (TreeSyncPublicState.mf tkt).wf pred x.treesync ∧
    BareTreeKEMState.mf.wf pred x.treekem
  )
:= by
  simp only [BareTreeSyncTreeKEMState.mf, NonExtensibleMessageFormat.isomorphic.wf_eq, BareTreeSyncTreeKEMState.g,
    NonExtensibleMessageFormat.prod.wf_eq, NonExtensibleMessageFormat.slowNat.wf_eq, true_and]

/-- Port of `local_state_treesync_treekem_state` (for its format). -/
public
instance BareTreeSyncTreeKEMState.ps: ParseableSerializeableNE BareTreeSyncTreeKEMState :=
  .make BareTreeSyncTreeKEMState.mf

/-- Port of `treesync_treekem_state`. -/
public
structure TreeSyncTreeKEMState where
  leafIndex: Nat
  groupContext: GroupContext Bytes
  mySignatureKeySid: Nat
  treesync: TreeSyncState Bytes tkt DyAsToken groupContext.groupId
  treekem: TreeKEMState Bytes leafIndex

variable [ExecTraceTypes]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeKEMNodeKeysState)]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT TreeKEMEpochSecret)]
variable [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT BareTreeSyncTreeKEMState)]

/-- Port of `store_treesync_treekem_state`. Returns the handle of the new state. -/
public
def storeTreesyncTreekemState (me: Participant) (st: TreeSyncTreeKEMState): Traceful Nat := do
  let epochKeys := st.treekem.keyscheduleState.epochKeys
  let confirmationTag := epochKeys.confirmationTag
  let senderDataSecretSid ← storeEpochSecret me .senderDataSecret st.groupContext confirmationTag epochKeys.senderDataSecret
  let exporterSecretSid ← storeEpochSecret me .exporterSecret st.groupContext confirmationTag epochKeys.exporterSecret
  let externalSecretSid ← storeEpochSecret me .externalSecret st.groupContext confirmationTag epochKeys.externalSecret
  let membershipKeySid ← storeEpochSecret me .membershipKey st.groupContext confirmationTag epochKeys.membershipKey
  let resumptionPskSid ← storeEpochSecret me .resumptionPsk st.groupContext confirmationTag epochKeys.resumptionPsk
  let epochAuthenticatorSid ← storeEpochSecret me .epochAuthenticator st.groupContext confirmationTag epochKeys.epochAuthenticator
  let initSecretSid ← storeEpochSecret me .initSecret st.groupContext confirmationTag st.treekem.keyscheduleState.initSecret
  let privSid ← storeNodeKeys me st.treekem.treeState.priv
  let bareSt: BareTreeSyncTreeKEMState := {
    leafIndex := st.leafIndex
    groupContext := st.groupContext
    mySignatureKeySid := st.mySignatureKeySid
    treesync := {
      groupId := st.groupContext.groupId
      st := st.treesync
    }
    treekem := {
      levels := st.treekem.treeState.levels
      tree := st.treekem.treeState.tree
      privSid
      senderDataSecretSid
      exporterSecretSid
      externalSecretSid
      membershipKeySid
      resumptionPskSid
      epochAuthenticatorSid
      confirmationTag
      initSecretSid
    }
  }
  PersistentLocalState.storeLocalState me bareSt

/--
Port of `get_treesync_treekem_state`.
Unlike MLS*, this function does not check the TreeSync and TreeKEM invariants
(`leaf_index < pow2 levels`, `unmerged_leaves_ok`, `parent_hash_invariant`, `valid_leaves_invariant`,
`Some? (leaf_at tree leaf_index)`), nor that the heights of the trees are equal
and that the TreeKEM tree is `treesync_to_treekem` of the TreeSync tree:
MLS* checks them for its refinement types, and they follow from the state invariant.
-/
public
def getTreesyncTreekemState (me: Participant) (sid: Nat): Traceful TreeSyncTreeKEMState := do
  let bareSt: BareTreeSyncTreeKEMState ← PersistentLocalState.getLocalState me sid
  let confirmationTag := bareSt.treekem.confirmationTag
  let senderDataSecret ← getEpochSecret me bareSt.treekem.senderDataSecretSid .senderDataSecret bareSt.groupContext confirmationTag
  let exporterSecret ← getEpochSecret me bareSt.treekem.exporterSecretSid .exporterSecret bareSt.groupContext confirmationTag
  let externalSecret ← getEpochSecret me bareSt.treekem.externalSecretSid .externalSecret bareSt.groupContext confirmationTag
  let membershipKey ← getEpochSecret me bareSt.treekem.membershipKeySid .membershipKey bareSt.groupContext confirmationTag
  let resumptionPsk ← getEpochSecret me bareSt.treekem.resumptionPskSid .resumptionPsk bareSt.groupContext confirmationTag
  let epochAuthenticator ← getEpochSecret me bareSt.treekem.epochAuthenticatorSid .epochAuthenticator bareSt.groupContext confirmationTag
  let initSecret ← getEpochSecret me bareSt.treekem.initSecretSid .initSecret bareSt.groupContext confirmationTag
  if h: bareSt.treesync.groupId = bareSt.groupContext.groupId then
    let priv ← getNodeKeys me bareSt.treekem.privSid
    pure {
      leafIndex := bareSt.leafIndex
      groupContext := bareSt.groupContext
      mySignatureKeySid := bareSt.mySignatureKeySid
      treesync := h ▸ bareSt.treesync.st
      treekem := {
        treeState := {
          levels := bareSt.treekem.levels
          tree := bareSt.treekem.tree
          priv
        }
        keyscheduleState := {
          epochKeys := {
            senderDataSecret
            exporterSecret
            externalSecret
            membershipKey
            resumptionPsk
            epochAuthenticator
            confirmationTag
          }
          initSecret
        }
      }
    }
  else
    failure

end MLS.TreeKEM
