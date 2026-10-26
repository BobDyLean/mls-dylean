module

public import MLS.TreeKEM.Symbolic.Traceful.ExecTrace
public import MLS.TreeKEM.Code.API
public import MLS.Bootstrap.Code.Welcome
public import MLS.Glue.Code.NetworkBinder
public import MLS.Glue.Code.TreeSyncTreeKEMBinder

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome`.

The function `processWelcome` processes
a Welcome message
and a ratchet tree,
which are both obtained from the network (the attacker).
It follows the steps of section 12.4.3.1 or the MLS RFC:
- decrypt the Welcome message
- verify the ratchet tree integrity in `processWelcomeTreesync'`, in particular:
  * verify parent hash
  * verify leaf node signatures
  * check validity of signature keys wrt the authentication service
  * etc
- verify GroupInfo in `processWelcomeVerifyGroupInfo'`, in particular:
  * verify the GroupInfo signature
  * check that the GroupContext tree hash matches our ratchet tree
- initialize TreeKEM's state in `processWelcomeTreekem'`:
  * find our position in the ratchet tree
  * initialize TreeKEM using the joiner secret and (optional) path secret
  * check that our confirmation tag matches the one in GroupInfo
- finally, log an event saying that we are in the group

Port-specific differences:
- MLS*'s functions with a leading underscore (`_process_welcome`, …) end with a prime.
- `my_leaf_index_t` (a leaf index whose leaf is a given leaf node) is not ported: `findMyIndex'` returns a `Nat`.
- Leaf nodes have no decidable equality: `findMyIndex'` compares their serializations.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.Bootstrap

/-! ## Process a welcome -/

/-- Port of `_find_my_index`. -/
public
def findMyIndex' {Bytes: Type} [BytesLike Bytes] [DecidableEq Bytes] {l: Nat} (t: TreeSync Bytes tkt l) (ln: LeafNode Bytes tkt): Option Nat :=
  match t.intoLeftRightView with
  | .leaf none _ => none
  | .leaf (some ln') i =>
    if serializeNE (LeafNode.mf tkt) ln = serializeNE (LeafNode.mf tkt) ln' then some i
    else none
  | .node _ left right =>
    match findMyIndex' left ln with
    | some i => some i
    | none =>
      match findMyIndex' right ln with
      | some i => some i
      | none => none
termination_by l

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-- Port of `_process_welcome_treesync`. -/
public
def processWelcomeTreesync' (me: Participant) (authServiceSid: Nat)
  (ratchetTree: RatchetTree Bytes tkt) (groupId: MlsBytes Bytes): Traceful (TreeSyncState Bytes tkt DyAsToken groupId)
:= do
  let ⟨_, treesync⟩ ← extractResult (ratchetTreeToTreesync ratchetTree)
  let treesyncWelcomePend ← extractResult (TreeSync.API.prepareWelcome groupId treesync)
  let tokens ← Symbolic.API.getTokensFor me authServiceSid treesyncWelcomePend.asInputs
  logLeafNodeVerificationEvents me treesync groupId
  pure (TreeSync.API.finalizeWelcome treesyncWelcomePend tokens)

/-- Port of `_process_welcome_verify_group_info`. -/
public
def processWelcomeVerifyGroupInfo' {groupId: MlsBytes Bytes} (_me: Participant)
  (treesyncSt: TreeSyncState Bytes tkt DyAsToken groupId) (groupInfo: GroupInfo Bytes): Traceful Unit
:= do
  -- check group info signature
  let signerVerificationKey ← extractResult (getSignerVerificationKey treesyncSt.tree groupInfo)
  guard (verifyWelcomeGroupInfo signerVerificationKey groupInfo)

  -- check tree hash
  let computedTreeHash ← extractResult (TreeSync.API.computeTreeHash treesyncSt)
  guard (computedTreeHash = groupInfo.tbs.groupContext.treeHash.val)

/--
Port of `_process_welcome_treekem`.
Returns our leaf index, and the TreeKEM state.
-/
public
def processWelcomeTreekem' {groupId: MlsBytes Bytes} (me: Participant)
  (treesyncSt: TreeSyncState Bytes tkt DyAsToken groupId) (kpStoreValue: KeyPackageStoreValuePost)
  (groupSecrets: GroupSecrets Bytes) (groupInfo: GroupInfo Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)):
  Traceful ((leafInd: Nat) × TreeKEMState Bytes leafInd)
:= do
  let some myLeafIndex := findMyIndex' treesyncSt.tree kpStoreValue.keyPackage.tbs.leafNode | failure
  let treekem := treesyncToTreekem treesyncSt.tree
  let optPathSecretAndInviterInd: Option (Bytes × Nat) :=
    match groupSecrets.pathSecret with
    | none => none
    | some { pathSecret } => some (pathSecret.val, groupInfo.tbs.signer.toNat)
  let leafDecryptionKey ← getLeafNodeKey me kpStoreValue.leafNodeKeySid
  guard (DySlop.HPKE.hpkePk leafDecryptionKey = kpStoreValue.keyPackage.tbs.leafNode.data.content.val)
  let (treekemSt, _encryptionSecret) ← extractResult
    (API.welcome treekem leafDecryptionKey optPathSecretAndInviterInd myLeafIndex groupSecrets.joinerSecret.val psks
      groupInfo.tbs.groupContext)
  guard ((API.getEpochKeys treekemSt).confirmationTag = groupInfo.tbs.confirmationTag.val)
  pure ⟨myLeafIndex, treekemSt⟩

/-- Port of `_process_welcome`. Returns the handle of the group state. -/
public
def processWelcome' (me: Participant) (keyPackageStoreSid authServiceSid pskStoreSid: Nat)
  (welcome: Welcome Bytes) (ratchetTree: RatchetTree Bytes tkt): Traceful Nat
:= do
  let keyPackageRefToKpSecrets ← getStoreLookupFunction me keyPackageStoreSid
  let (groupSecrets, (_keyPackageRef, keyPackageStoreValue)) ← extractResult
    (decryptGroupSecrets welcome keyPackageRefToKpSecrets keyPackageStoreValueToHpkeSk)
  let psks ← retrievePsks me pskStoreSid groupSecrets.psks.val
  let groupInfo ← extractResult (decryptGroupInfo groupSecrets.joinerSecret.val psks welcome.encryptedGroupInfo.val)

  let treesyncSt ← processWelcomeTreesync' me authServiceSid ratchetTree groupInfo.tbs.groupContext.groupId
  processWelcomeVerifyGroupInfo' me treesyncSt groupInfo

  let ⟨myLeafIndex, treekemSt⟩ ← processWelcomeTreekem' me treesyncSt keyPackageStoreValue groupSecrets groupInfo psks

  ProtocolEvent.logEvent ({
    prin := me
    how := .justJoined { inviter := groupInfo.tbs.signer.toNat }
    groupContext := groupInfo.tbs.groupContext
    treeHeight := treesyncSt.levels
    tree := treesyncSt.tree
    psks
    epochKeys := treekemSt.keyscheduleState
  }: IAmInGroup)

  storeTreesyncTreekemState me {
    leafIndex := myLeafIndex
    groupContext := groupInfo.tbs.groupContext
    mySignatureKeySid := keyPackageStoreValue.signatureKeySid
    treesync := treesyncSt
    treekem := treekemSt
  }

/-- Port of `process_welcome`. Returns the handle of the group state. -/
public
def processWelcome (me: Participant) (keyPackageStoreSid authServiceSid pskStoreSid: Nat)
  (welcomeTs ratchetTreeTs: Nat): Traceful Nat
:= do
  let welcomeBytes ← Network.receiveMessage welcomeTs
  let ratchetTreeBytes ← Network.receiveMessage ratchetTreeTs
  let some welcome := (Welcome.mf (Bytes := Bytes)).toExtensible.parse welcomeBytes | failure
  let some ratchetTree := (RatchetTree.mf tkt).toExtensible.parse ratchetTreeBytes | failure
  processWelcome' me keyPackageStoreSid authServiceSid pskStoreSid welcome ratchetTree

end MLS.TreeKEM
