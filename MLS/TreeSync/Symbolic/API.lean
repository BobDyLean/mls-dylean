module

public import MLS.TreeSync.Code.API
public import MLS.TreeSync.Proofs.ParentHashGuarantees
public import MLS.TreeSync.Symbolic.State.SignatureKey
public import MLS.TreeSync.Symbolic.State.Tree
public import MLS.TreeSync.Symbolic.State.AuthServiceCache
public import MLS.TreeSync.Symbolic.State.GroupManager
public import MLS.TreeSync.Symbolic.State.KeyPackageManager
public import MLS.TreeSync.Symbolic.LeafNodeSignature

/-!
Port of `MLS.TreeSync.Symbolic.API`: the traceful API of TreeSync.

Port-specific differences:
- The namespace is `MLS.TreeSync.Symbolic.API` (MLS*'s module name), since `MLS.TreeSync.API` is the code API.
- Functions returning `traceful (option a)` return `Traceful a`, which already supports failure.
  MLS*'s `guard` is Lean's `guard` (`Traceful` is an `Alternative`).
- States are identified by handles instead of session identifiers, and DyLean's states are immutable:
  a function updating the public state of a group stores a new version of it (instead of MLS*'s `set_public_treesync_state`),
  and stores a new version of the group manager pointing to it.
  Such functions (`create`, `welcome`, `add`, `update`, `remove`, `commit`) return the new handle of the group manager
  (after their MLS* result, if any).
- The public state is retrieved with `PersistentLocalState.getLocalState` (instead of MLS*'s `get_public_treesync_state`),
  without checking the TreeSync invariants (see `MLS.TreeSync.Symbolic.State.Tree`).
- Only the specification is ported for now: the invariants (`has_treesync_invariants`, `tree_event_pre`,
  `external_path_has_event_pre`, …) and the proofs (`*_proof`) are not ported yet.
-/

namespace MLS.TreeSync

open Comparse
open DY DY.Comparse
open MLS
open DySlop.Map (Map)
open MLS.Bootstrap (KeyPackage)

/-!
## Configuration

The trace entries used by the symbolic API of TreeSync are bundled in a typeclass,
whose fields are scoped instances in the namespace `MLS.TreeSync`.
The top-level protocol provides it after combining the corresponding trace entries
(`instance: HasTreeSyncExecTrace tkt where`).
The TreeKEM types `tkt` are an `outParam`, so that the entries which do not depend on it are found.
-/

public
class HasTreeSyncExecTrace [HasSymbolicBytes] [ExecTraceTypes] (tkt: outParam (TreeKEMTypes Bytes)) where
  [traceExec0: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
  [traceExec2: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (TreeSyncPublicState tkt))]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map AsCacheKey AsCacheValue))]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map GroupManagerKey GroupManagerValue))]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map (KeyPackage Bytes tkt) KeyPackageManagerValue))]
  [traceExec6: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
  [traceExec7: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]

attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec0
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec1
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec2
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec3
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec4
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec5
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec6
attribute [reducible, scoped instance] HasTreeSyncExecTrace.traceExec7

end MLS.TreeSync

namespace MLS.TreeSync.Symbolic.API

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeSync.API
open MLS.Bootstrap (KeyPackage)

variable [HasSymbolicBytes] [ExecTraceTypes] {tkt: TreeKEMTypes Bytes} [HasTreeSyncExecTrace tkt]

/-! ## Utility functions -/

/-- Port of `get_token_for`. -/
public
def getTokenFor (p: Participant) (asSession: Nat) (inp: ASInput Bytes): Traceful DyAsToken := do
  let (verificationKey, credential) := inp
  let value ← findVerifiedCredential p asSession { verificationKey, credential }
  pure value.token

/-- Port of `get_tokens_for`. -/
public
def getTokensFor (p: Participant) (asSession: Nat): List (Option (ASInput Bytes)) → Traceful (List (Option DyAsToken))
  | [] => pure []
  | inpHead :: inpsTail => do
    let tokenHead ←
      match inpHead with
      | some inp => do
        let token ← getTokenFor p asSession inp
        pure (some token)
      | none => pure none
    let tokensTail ← getTokensFor p asSession inpsTail
    pure (tokenHead :: tokensTail)

/-! ## Process proposals -/

/--
Port of `create`.
Returns the new handle of the group manager.
-/
public
def create (p: Participant) (asSession gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt) (secretSession: Nat): Traceful Nat
:= do
  let createPend ← extractResult (prepareCreate groupId ln)
  let token ← getTokenFor p asSession createPend.asInput
  let st := finalizeCreate createPend token
  let siPublic ← PersistentLocalState.storeLocalState p ({ groupId, st }: TreeSyncPublicState tkt)
  let groupSessions: GroupManagerValue := { siPublic, siPrivate := secretSession }
  addNewGroupSessions p gmgrSession { groupId } groupSessions

/--
Port of `welcome`.
Returns the new handle of the group manager.
-/
public
def welcome (p: Participant) (asSession gmgrSession kpmgrSession: Nat)
  (myKeyPackage: KeyPackage Bytes tkt)
  (groupId: MlsBytes Bytes) (l: Nat) (t: TreeSync Bytes tkt l): Traceful Nat
:= do
  let welcomePend ← extractResult (prepareWelcome groupId t)
  let tokens ← getTokensFor p asSession welcomePend.asInputs
  let st := finalizeWelcome welcomePend tokens
  let siPublic ← PersistentLocalState.storeLocalState p ({ groupId, st }: TreeSyncPublicState tkt)
  let kpValue ← findKeyPackageSecretSession tkt p kpmgrSession myKeyPackage
  let groupSessions: GroupManagerValue := { siPublic, siPrivate := kpValue.siPrivate }
  addNewGroupSessions p gmgrSession { groupId } groupSessions

/--
Port of `add`.
Returns the leaf index of the new member, and the new handle of the group manager.
-/
public
def add (p: Participant) (asSession gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt): Traceful (Nat × Nat)
:= do
  let groupSession ← findGroupSessions p gmgrSession { groupId }
  let ⟨stGroupId, st⟩: TreeSyncPublicState tkt ← PersistentLocalState.getLocalState p groupSession.siPublic
  let addPend ← extractResult (prepareAdd st ln)
  let token ← getTokenFor p asSession addPend.asInput
  let (newSt, newLeafIndex) ← extractResult (finalizeAdd addPend token)
  let siPublic ← PersistentLocalState.storeLocalState p ({ groupId := stGroupId, st := newSt }: TreeSyncPublicState tkt)
  let gmgrSession ← addNewGroupSessions p gmgrSession { groupId } { groupSession with siPublic }
  pure (newLeafIndex, gmgrSession)

/--
Port of `update`.
Returns the new handle of the group manager.
-/
public
def update (p: Participant) (asSession gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt) (li: Nat): Traceful Nat
:= do
  let groupSession ← findGroupSessions p gmgrSession { groupId }
  let ⟨stGroupId, st⟩: TreeSyncPublicState tkt ← PersistentLocalState.getLocalState p groupSession.siPublic
  guard (li < 2^st.levels)
  let updatePend ← extractResult (prepareUpdate st ln li)
  let token ← getTokenFor p asSession updatePend.asInput
  let newSt := finalizeUpdate updatePend token
  let siPublic ← PersistentLocalState.storeLocalState p ({ groupId := stGroupId, st := newSt }: TreeSyncPublicState tkt)
  addNewGroupSessions p gmgrSession { groupId } { groupSession with siPublic }

/--
Port of `remove`.
Returns the new handle of the group manager.
-/
public
def remove (p: Participant) (_asSession gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (li: Nat): Traceful Nat
:= do
  let groupSession ← findGroupSessions p gmgrSession { groupId }
  let ⟨stGroupId, st⟩: TreeSyncPublicState tkt ← PersistentLocalState.getLocalState p groupSession.siPublic
  guard (li < 2^st.levels)
  let removePend ← extractResult (prepareRemove st li)
  let newSt := finalizeRemove removePend
  let siPublic ← PersistentLocalState.storeLocalState p ({ groupId := stGroupId, st := newSt }: TreeSyncPublicState tkt)
  addNewGroupSessions p gmgrSession { groupId } { groupSession with siPublic }

/--
Port of `commit`.
Returns the new handle of the group manager.
-/
public
def commit {l: Nat} (p: Participant) (asSession gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (li: Nat) (path: PathSync Bytes tkt l): Traceful Nat
:= do
  let groupSession ← findGroupSessions p gmgrSession { groupId }
  let ⟨stGroupId, st⟩: TreeSyncPublicState tkt ← PersistentLocalState.getLocalState p groupSession.siPublic
  if h: l = st.levels then
    let commitPend ← extractResult (prepareCommit st li (h ▸ path))
    let token ← getTokenFor p asSession commitPend.asInput
    let newSt ← extractResult (finalizeCommit commitPend token)
    let siPublic ← PersistentLocalState.storeLocalState p ({ groupId := stGroupId, st := newSt }: TreeSyncPublicState tkt)
    addNewGroupSessions p gmgrSession { groupId } { groupSession with siPublic }
  else
    failure

/-! ## Create signature keypair -/

/--
Port of `create_signature_keypair`.
Returns the handle of the private state (containing the signature key), and the verification key.
-/
public
def createSignatureKeypair (p: Participant): Traceful (Nat × SignaturePublicKey Bytes) := do
  let privateSi ← mkSignatureKey p
  let verificationKey ← getSignatureKeyVk p privateSi
  if h: mlsNatPred (BytesLike.length verificationKey) then
    pure (privateSi, ⟨verificationKey, h⟩)
  else
    failure

/-! ## Sign stuff -/

/--
Port of `authenticate_path`.
MLS* requires `(get_path_leaf path).source == LNS_update`; otherwise, see `externalPathToPath`.
MLS* compares the trees `tree` and `st.tree`; as trees have no decidable equality, their serializations are compared.
-/
public
def authenticatePath {l: Nat} (p: Participant) (gmgrSession: Nat)
  (groupId: MlsBytes Bytes) (tree: TreeSync Bytes tkt l) (li: Nat) (path: ExternalPathSync Bytes tkt l):
  Traceful (PathSync Bytes tkt l)
:= do
  let signatureNonce ← Random.genRand 32
  let groupSession ← findGroupSessions p gmgrSession { groupId }
  let ⟨groupId', st⟩: TreeSyncPublicState tkt ← PersistentLocalState.getLocalState p groupSession.siPublic
  let signatureKey ← getSignatureKeySk p groupSession.siPrivate
  guard (groupId = groupId')
  guard (l = st.levels)
  guard (serializeNE (TreeSync.mf tkt l) tree = serializeNE (TreeSync.mf tkt st.levels) st.tree)
  guard (BytesLike.length signatureNonce ≥ CryptoBytes.signSignMinEntropyLength Bytes)
  guard (pathIsFilterValid tree li path)
  extractResult (externalPathToPath tree li path groupId signatureKey signatureNonce)

/--
Port of `authenticate_leaf_node_data_from_key_package`.
MLS* requires `ln_data.source == LNS_key_package`; otherwise, this function fails.
-/
public
def authenticateLeafNodeDataFromKeyPackage (p: Participant) (siPrivate: Nat) (lnData: LeafNodeData Bytes tkt):
  Traceful (LeafNode Bytes tkt)
:= do
  let signatureNonce ← Random.genRand 32
  let signatureKey ← getSignatureKeySk p siPrivate
  guard (BytesLike.length signatureNonce = CryptoBytes.signSignMinEntropyLength Bytes)
  extractResult (signLeafNodeDataKeyPackage lnData signatureKey signatureNonce)

/--
Port of `authenticate_leaf_node_data_from_update`.
MLS* requires `ln_data.source == LNS_update`; otherwise, this function fails.
-/
public
def authenticateLeafNodeDataFromUpdate (p: Participant) (siPrivate: Nat)
  (lnData: LeafNodeData Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: UInt32):
  Traceful (LeafNode Bytes tkt)
:= do
  let signatureNonce ← Random.genRand 32
  let signatureKey ← getSignatureKeySk p siPrivate
  guard (BytesLike.length signatureNonce ≥ CryptoBytes.signSignMinEntropyLength Bytes)
  extractResult (signLeafNodeDataUpdate lnData groupId leafIndex signatureKey signatureNonce)

/-! ## Trigger events -/

/-- Port of `trigger_tree_event`. -/
public
def triggerTreeEvent (p: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat) (t: OneTree Bytes tkt):
  Traceful Unit
:=
  ProtocolEvent.logEvent (mkGroupHasTreeEvent p groupId authentifierLeafIndex t)

/-- Port of `trigger_tree_list_event`. -/
public
def triggerTreeListEvent (p: Participant) (groupId: MlsBytes Bytes) (authentifierLeafIndex: Nat):
  TreeList Bytes tkt → Traceful Unit
  | [] => pure ()
  | h :: t => do
    triggerTreeEvent p groupId authentifierLeafIndex h
    triggerTreeListEvent p groupId authentifierLeafIndex t

/-- Port of `trigger_leaf_node_event`. -/
public
def triggerLeafNodeEvent (p: Participant) (lnTbs: LeafNodeTBS Bytes tkt): Traceful Unit :=
  ProtocolEvent.logEvent ({ prin := p, lnTbs }: LeafNodeSignedEvent tkt)

/--
Port of `trigger_external_path_events`.
The tree list is computed before triggering the leaf node event:
in MLS*, its computation cannot fail (its success follows from the one of `externalPathToPathNosig`).
-/
public
def triggerExternalPathEvents {l: Nat} (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes): Traceful Unit
:= do
  guard (p.getPathLeaf.source = .update)
  guard (li < 2^32)
  let authP ← extractResult (externalPathToPathNosig t li p)
  let authLn := authP.getPathLeaf
  let tl ← extractResult (pathToTreeList t li authP)
  triggerLeafNodeEvent prin { data := authLn.data, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 }
  triggerTreeListEvent prin groupId li tl

end MLS.TreeSync.Symbolic.API
