module

public import MLS.TreeKEM.Symbolic.Traceful.ProcessCommit
public import MLS.TreeKEM.Symbolic.API.Tree
public import MLS.Symbolic.Code.Randomness
public import MLS.Bootstrap.Code.Welcome
public import MLS.Glue.Code.TreeSyncTreeKEMBinder
public import MLS.Common.Code.Extensions

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome`.

The function `createCommitAndWelcome`
creates a Commit and a Welcome message to the joiners,
as specified by the MLS RFC:
- process proposals
- if doing a full commit, create an UpdatePath:
  * generate new public keys in TreeKEM
  * authenticate these new public keys in TreeSync
  * apply these keys in TreeSync's tree
  * compute the provisional GroupContext using the new tree hash
  * encrypt the secrets keys in TreeKEM, using the provisional GroupContext
- compute the new GroupContext
- update the Key Schedule
- create and sign the GroupInfo, containing a confirmation tag for this epoch
- encrypt joiner secret and path secrets to joiners
- combine the GroupInfo and the encrypted group secrets in a Welcome message

Port-specific differences:
- MLS*'s functions and types with a leading underscore (`_create_commit`, …) end with a prime.
- The randomness is generated with its lengths (see `MLS.Symbolic.Randomness`):
  MLS*'s ghost data (e.g. `encrypt_group_secrets_entropy_ghost_data`) are ghost arguments of the proofs.
- The refinements of the transcript hash inputs (`tx_hash_input.content.content.content_type == CT_commit`)
  are dropped: the functions fail when they are not satisfied.
- DyLean's states are immutable: `createCommit'`, `createCommitAndWelcome'` and `createCommitAndWelcome`
  also return the new handle of the PSK store.
- Unlike MLS*, `createCommitAndWelcome` returns the handle of the new group state
  (field `newGroupStateSid` of `CreateCommitAndWelcomeResult`): MLS* stores it but forgets to return it.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Welcome and Commit generation -/

/-- Port of `create_group_info_parameters`. -/
public
structure CreateGroupInfoParameters where
  groupInfoExtensions: MlsList (Extension.mf (Bytes := Bytes))

/-- Port of `_create_group_info`. -/
public
def createGroupInfo' (me: Participant) (st: TreeSyncTreeKEMState) (params: CreateGroupInfoParameters):
  Traceful (GroupInfo Bytes)
:= do
  let confirmationTag ← extractResult
    (mkMlsBytes st.treekem.keyscheduleState.epochKeys.confirmationTag "_create_group_info" "confirmation_tag")
  guard (st.leafIndex < 2^32)
  let groupInfoTbs: GroupInfoTBS Bytes := {
    groupContext := st.groupContext
    extensions := params.groupInfoExtensions
    confirmationTag
    signer := st.leafIndex.toUInt32
  }
  let signatureKey ← getSignatureKeySk me st.mySignatureKeySid
  let signatureNonce ← Random.genRand (CryptoBytes.signSignMinEntropyLength Bytes)
  guard (BytesLike.length signatureNonce = CryptoBytes.signSignMinEntropyLength Bytes)
  extractResult (signWelcomeGroupInfo signatureKey groupInfoTbs signatureNonce)

/-- Port of `create_welcome_parameters`. -/
public
structure CreateWelcomeParameters where
  joinerSecret: Bytes
  joinersAndPathSecrets: List (KeyPackage Bytes tkt × Option Bytes)
  psks: List (PreSharedKeyId Bytes × Bytes)

/-- Port of `_create_welcome`. -/
public
def createWelcome' (_st: TreeSyncTreeKEMState) (groupInfo: GroupInfo Bytes) (params: CreateWelcomeParameters):
  Traceful (Option (Welcome Bytes))
:= do
  if params.joinersAndPathSecrets.isEmpty then
    pure none
  else
    let _joinerSecret ← extractResult (mkMlsBytes params.joinerSecret "_create_welcome" "joiner_secret")
    let encryptWelcomeRand ← generateRandomness (encryptWelcomeEntropyLength params.joinersAndPathSecrets)
    let welcomeMsg ← extractResult (encryptWelcome groupInfo params.joinerSecret params.psks params.joinersAndPathSecrets encryptWelcomeRand)
    pure (some welcomeMsg)

/--
Port of `_update_path_external_pathsync_to_pathsync`.
MLS*'s leaf index `li` (implicit in the path) is explicit.
-/
public
def updatePathExternalPathsyncToPathsync' {l: Nat} (me: Participant)
  (st: TreeSyncTreeKEMState) (li: Nat) (externalPath: ExternalPathSync Bytes tkt l): Traceful (PathSync Bytes tkt l)
:= do
  if h: st.treesync.levels = l then
    guard (st.leafIndex < 2^st.treesync.levels)
    guard (st.leafIndex = li)
    let externalPath: ExternalPathSync Bytes tkt st.treesync.levels := h ▸ externalPath
    Symbolic.API.triggerExternalPathEvents me st.treesync.tree li externalPath st.groupContext.groupId
    let signatureKey ← getSignatureKeySk me st.mySignatureKeySid
    let signatureNonce ← Random.genRand (CryptoBytes.signSignMinEntropyLength Bytes)
    guard (BytesLike.length signatureNonce = CryptoBytes.signSignMinEntropyLength Bytes)
    guard (externalPath.getPathLeaf.source = .update)
    let updatePathSync ← extractResult (TreeSync.API.authenticateExternalPath st.treesync li externalPath signatureKey signatureNonce)
    pure (h ▸ updatePathSync)
  else
    failure

/-- Port of `_generate_update_path_path`. -/
public
def generateUpdatePathPath' (me: Participant) (st: TreeSyncTreeKEMState):
  Traceful (PathSync Bytes tkt st.treekem.treeState.levels × API.PendingCreateCommit st.treekem)
:= do
  guard (st.treesync.levels = st.treekem.treeState.levels)

  let some myOldLeafNode := leafAt st.treesync.tree st.leafIndex | failure
  let myNewLeafPackageData: LeafNodeData Bytes tkt := {
    myOldLeafNode.data with
    content := (MlsBytes.empty: HpkePublicKey Bytes)
    source := .update
    lifetime := ()
    parentHash := ()
  }

  let prepareCreateCommitRand ← generatePrepareCreateCommitRand me
  let (pendingCreateCommit, preUpdatePath) ← extractResult (API.prepareCreateCommit st.treekem prepareCreateCommitRand)
  let externalPath ← extractResult (treekemToTreesync myNewLeafPackageData preUpdatePath)

  let updatePathsync ← updatePathExternalPathsyncToPathsync' me st st.leafIndex externalPath
  pure (updatePathsync, pendingCreateCommit)

/-- Port of `_generate_update_path_tree_result`. -/
public
structure GenerateUpdatePathTreeResult' (leafInd: Nat) (treekem: TreeKEMState Bytes leafInd) where
  provisionalGroupContext: GroupContext Bytes
  newTreesync: TreeSyncState Bytes tkt DyAsToken provisionalGroupContext.groupId
  pendingCommit: API.PendingCreateCommit2 Bytes leafInd
  commitResult: API.ContinueCreateCommitResult treekem

/-- Port of `_generate_update_path_tree`. -/
public
def generateUpdatePathTree' (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (updatePathsync: PathSync Bytes tkt st.treekem.treeState.levels)
  (treekemPendingCreateCommit: API.PendingCreateCommit st.treekem) (joiners: List (KeyPackage Bytes tkt × Nat)):
  Traceful (GenerateUpdatePathTreeResult' st.leafIndex st.treekem)
:= do
  if h: st.treesync.levels = st.treekem.treeState.levels then
    guard (st.leafIndex < 2^st.treesync.levels)

    let updatePathsync: PathSync Bytes tkt st.treesync.levels := h ▸ updatePathsync
    let treesyncPendingCommit ← extractResult (TreeSync.API.prepareCommit st.treesync st.leafIndex updatePathsync)
    let token ← Symbolic.API.getTokenFor me authServiceSid treesyncPendingCommit.asInput
    let newTreesync ← extractResult (TreeSync.API.finalizeCommit treesyncPendingCommit token)
    logLeafNodeVerificationEvent me updatePathsync.getPathLeaf st.groupContext.groupId st.leafIndex

    let provisionalGroupContext ← makeProvisionalGroupContext' st.groupContext newTreesync

    let addedLeaves := joiners.map (·.2)
    let continueCreateCommitRand ← generateRandomness (API.continueCreateCommitEntropyLengths st.treekem addedLeaves)
    let (pendingCommit, commitResult) ← extractResult
      (API.continueCreateCommit treekemPendingCreateCommit addedLeaves provisionalGroupContext.val continueCreateCommitRand)

    pure {
      provisionalGroupContext := provisionalGroupContext.val
      newTreesync := (congrArg (TreeSyncState Bytes tkt DyAsToken) provisionalGroupContext.property).mpr newTreesync
      pendingCommit
      commitResult
    }
  else
    failure

/-- Port of `generate_opt_update_path_result`. -/
public
structure GenerateOptUpdatePathResult (leafIndex: Nat) where
  provisionalGroupContext: GroupContext Bytes
  optUpdatePath: Option (TreeKEM.UpdatePath Bytes)
  newTreesync: TreeSyncState Bytes tkt DyAsToken provisionalGroupContext.groupId
  pendingCommit: API.PendingCreateCommit2 Bytes leafIndex
  joinersAndPathSecrets: List (KeyPackage Bytes tkt × Option Bytes)
  pskIds: List (PreSharedKeyId Bytes)

/-- Port of `_generate_update_path`. -/
public
def generateUpdatePath' (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender): Traceful (GenerateOptUpdatePathResult st.leafIndex)
:= do
  let st0 := st
  let (st, joiners, pskIds, _otherProposals, _canAddOnly) ← processProposals' me authServiceSid updateCacheSid st proposals
  if h: st.leafIndex = st0.leafIndex then
    let (updatePathsync, treekemPendingCreateCommit) ← generateUpdatePathPath' me st
    let { provisionalGroupContext, newTreesync, pendingCommit, commitResult } ←
      generateUpdatePathTree' me authServiceSid st updatePathsync treekemPendingCreateCommit joiners
    guard (provisionalGroupContext.groupId = st.groupContext.groupId)

    let uncompressedUpdatePath := mlsStarPathsToUpdatePath updatePathsync commitResult.updatePath
    let updatePath ← extractResult (compressUpdatePath uncompressedUpdatePath)

    guard ((joiners.map (·.1)).length = commitResult.addedLeavesPathSecrets.length)
    let joinersAndPathSecrets := List.zip (joiners.map (·.1)) (commitResult.addedLeavesPathSecrets.map some)

    pure {
      provisionalGroupContext
      optUpdatePath := some updatePath
      newTreesync
      pendingCommit := h ▸ pendingCommit
      joinersAndPathSecrets
      pskIds
    }
  else
    failure

/-- Port of `mk_joiner_without_path_secret`. -/
public
def mkJoinerWithoutPathSecret (keyPackage: KeyPackage Bytes tkt): KeyPackage Bytes tkt × Option Bytes :=
  (keyPackage, none)

/-- Port of `_generate_no_update_path`. -/
public
def generateNoUpdatePath' (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender): Traceful (GenerateOptUpdatePathResult st.leafIndex)
:= do
  let st0 := st
  let (st, joiners, pskIds, _otherProposals, canAddOnly) ← processProposals' me authServiceSid updateCacheSid st proposals
  if h: st.leafIndex = st0.leafIndex then
    guard canAddOnly

    let pendingCommit ← extractResult (API.prepareCreateAddOnlyCommit st.treekem)
    let provisionalGroupContext ← makeProvisionalGroupContext' st.groupContext st.treesync

    let joinersAndPathSecrets := (joiners.map (·.1)).map mkJoinerWithoutPathSecret

    pure {
      provisionalGroupContext := provisionalGroupContext.val
      optUpdatePath := none
      newTreesync := (congrArg (TreeSyncState Bytes tkt DyAsToken) provisionalGroupContext.property).mpr st.treesync
      pendingCommit := h ▸ pendingCommit
      joinersAndPathSecrets
      pskIds
    }
  else
    failure

/-- Port of `_generate_opt_update_path`. -/
public
def generateOptUpdatePath' (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender) (fullCommit: Bool):
  Traceful (GenerateOptUpdatePathResult st.leafIndex)
:=
  if fullCommit then
    generateUpdatePath' me authServiceSid updateCacheSid st proposals
  else
    generateNoUpdatePath' me authServiceSid updateCacheSid st proposals

/-- Port of `_create_commit_result`. -/
public
structure CreateCommitResult' where
  newSt: TreeSyncTreeKEMState
  joinersAndPathSecrets: List (KeyPackage Bytes tkt × Option Bytes)
  joinerSecret: Bytes
  txHashInput: ConfirmedTranscriptHashInput Bytes
  psks: List (PreSharedKeyId Bytes × Bytes)

/--
Port of `_create_commit`.
Returns the result, and the new handle of the PSK store.
MLS* requires `tx_hash_input_skeleton.content.content.content_type == CT_commit`; otherwise, this function fails.
-/
public
def createCommit' (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st: TreeSyncTreeKEMState) (txHashInputSkeleton: ConfirmedTranscriptHashInput Bytes): Traceful (CreateCommitResult' × Nat)
:= do
  let st0 := st
  let framedCommitSkeleton := txHashInputSkeleton.content
  let ⟨.commit, (commitSkeleton: Commit Bytes)⟩ := framedCommitSkeleton.content | failure

  let proposalsOrRefs := commitSkeleton.proposals.val
  let proposals ← retrieveProposals me proposalCacheSid st.leafIndex proposalsOrRefs

  let { provisionalGroupContext, optUpdatePath, newTreesync, pendingCommit, joinersAndPathSecrets, pskIds } ←
    generateOptUpdatePath' me authServiceSid updateCacheSid st proposals commitSkeleton.path.isSome

  let psks ← retrievePsks me pskStoreSid pskIds

  let commit: Commit Bytes := {
    commitSkeleton with
    path := optUpdatePath
  }
  guard (st.leafIndex < 2^32)
  let framedCommit: FramedContent Bytes := {
    framedCommitSkeleton with
    groupId := st.groupContext.groupId
    epoch := st.groupContext.epoch
    sender := .member st.leafIndex.toUInt32
    content := {
      contentType := .commit
      content := commit
    }
  }

  let txHashInput: ConfirmedTranscriptHashInput Bytes := {
    txHashInputSkeleton with
    content := framedCommit
  }

  let confirmedTranscriptHash ← extractResult (computeConfirmedTranscriptHash' st txHashInput)
  let newGroupContext: GroupContext Bytes := { provisionalGroupContext with confirmedTranscriptHash }
  let commitResult ← extractResult (API.finalizeCreateCommit pendingCommit newGroupContext psks)

  let st: TreeSyncTreeKEMState := {
    st with
    groupContext := newGroupContext
    treesync := newTreesync
    treekem := commitResult.newState
  }

  let pskStoreSid ← rememberPsk me pskStoreSid
    (.resumptionPsk st.groupContext.groupId st.groupContext.epoch) (API.getEpochKeys st.treekem).resumptionPsk

  ProtocolEvent.logEvent ({
    prin := me
    how := .processedCommit {
      previousInitSecret := st0.treekem.keyscheduleState.initSecret
      previousGroupContext := st0.groupContext
      previousTreeHeight := st0.treesync.levels
      previousTree := st0.treesync.tree
      commitTy := if commit.path.isSome then .fullCommit else .addOnlyCommit
      joiners := joinersAndPathSecrets.map (·.1)
    }
    groupContext := st.groupContext
    treeHeight := st.treesync.levels
    tree := st.treesync.tree
    psks
    epochKeys := st.treekem.keyscheduleState
  }: IAmInGroup)

  pure ({
    newSt := st
    joinersAndPathSecrets
    joinerSecret := commitResult.joinerSecret
    txHashInput
    psks
  }, pskStoreSid)

/--
Port of `_create_commit_and_welcome`.
Also returns the new handle of the PSK store.
MLS* requires `tx_hash_input_skeleton.content.content.content_type == CT_commit`; otherwise, this function fails.
-/
public
def createCommitAndWelcome' (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st: TreeSyncTreeKEMState) (txHashInputSkeleton: ConfirmedTranscriptHashInput Bytes):
  Traceful (ConfirmedTranscriptHashInput Bytes × Option (Welcome Bytes) × GroupInfo Bytes × TreeSyncTreeKEMState × Nat)
:= do
  let ({ newSt := st, joinersAndPathSecrets, joinerSecret, txHashInput, psks }, pskStoreSid) ←
    createCommit' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st txHashInputSkeleton

  let groupInfoInputs: CreateGroupInfoParameters := {
    groupInfoExtensions := emptyExtensions
  }
  let groupInfo ← createGroupInfo' me st groupInfoInputs

  let welcomeInputs: CreateWelcomeParameters := {
    joinerSecret
    joinersAndPathSecrets
    psks
  }
  let welcome ← createWelcome' st groupInfo welcomeInputs

  pure (txHashInput, welcome, groupInfo, st, pskStoreSid)

/--
Port of `create_commit_and_welcome_result`.
Unlike MLS*, it contains the handle of the new group state (`newGroupStateSid`).
-/
public
structure CreateCommitAndWelcomeResult where
  newGroupStateSid: Nat
  messageTs: Nat
  optWelcomeTs: Option Nat
  groupInfoTs: Nat
  ratchetTreeTs: Nat

/--
Port of `create_commit_and_welcome`.
Also returns the new handle of the PSK store.
Unlike MLS*, the result contains the handle of the new group state.
-/
public
def createCommitAndWelcome (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (groupStateSid: Nat) (messageSkeletonTs: Nat): Traceful (CreateCommitAndWelcomeResult × Nat)
:= do
  let st ← getTreesyncTreekemState me groupStateSid
  let messageSkeletonBytes ← Network.receiveMessage messageSkeletonTs
  let some messageSkeleton := (ConfirmedTranscriptHashInput.mf (Bytes := Bytes)).toExtensible.parse messageSkeletonBytes
    | failure
  guard (messageSkeleton.content.content.contentType = .commit)
  let (message, optWelcome, groupInfo, st, pskStoreSid) ←
    createCommitAndWelcome' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st messageSkeleton
  let newGroupStateSid ← storeTreesyncTreekemState me st
  let messageTs ← Network.sendMessage (serializeNE ConfirmedTranscriptHashInput.mf message)
  let optWelcomeTs ←
    match optWelcome with
    | none => pure none
    | some welcome => do
      let welcomeTs ← Network.sendMessage (serializeNE Welcome.mf welcome)
      pure (some welcomeTs)
  let groupInfoTs ← Network.sendMessage (serializeNE GroupInfo.mf groupInfo)
  let ratchetTree ← extractResult (treesyncToRatchetTree st.treesync.tree)
  let ratchetTreeTs ← Network.sendMessage (serializeNE (RatchetTree.mf tkt) ratchetTree)
  pure ({
    newGroupStateSid
    messageTs
    optWelcomeTs
    groupInfoTs
    ratchetTreeTs
  }, pskStoreSid)

end MLS.TreeKEM
