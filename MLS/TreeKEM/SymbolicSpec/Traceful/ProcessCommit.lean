module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace
public import MLS.TreeKEM.Code.API
public import MLS.TreeDEM.Code.Message.Transcript
public import MLS.Glue.Code.NetworkBinder

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessCommit`.

The function `processCommit` updates the group state by processing a Commit,
as specified in the MLS RFC:
- process proposals
- process the UpdatePath if it is present:
  * apply the UpdatePath in TreeSync
  * compute the provisional GroupContext (using the new tree hash)
  * apply and decrypt the UpdatePath in TreeKEM
- compute the new GroupContext
- update the Key Schedule

Port-specific differences:
- MLS*'s functions with a leading underscore (`_process_commit`, …) end with a prime.
- The refinements of the proposals (e.g. `P_add? proposal`) and of the transcript hash inputs
  (`tx_hash_input.content.content.content_type == CT_commit`) are dropped:
  the functions fail when they are not satisfied.
- `_process_update_path` does not check `path_filtering_ok`: MLS* only checks it for the refinement types
  of `prepare_process_full_commit`, which is not a precondition in Lean.
- MLS*'s `fold_leftM` is Lean's `List.foldlM`.
- DyLean's states are immutable: `processCommit'` and `processCommit` also return the new handle of the PSK store.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Process Commit -/

/--
Port of `_process_group_context_extensions_proposal`.
MLS* requires `P_group_context_extensions? proposal`; otherwise, this function fails.
-/
public
def processGroupContextExtensionsProposal' (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  Traceful TreeSyncTreeKEMState
:= do
  let .groupContextExtensions { extensions } := proposal | failure
  pure { st with groupContext := { st.groupContext with extensions } }

/--
Port of `_process_add_proposal_aux`.
MLS* requires `P_add? proposal`; otherwise, this function fails.
-/
public
def processAddProposalAux' (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes): Traceful (KeyPackage Bytes tkt × Nat × TreeSyncTreeKEMState)
:= do
  let .add { keyPackage } := proposal | failure
  let leafNode := keyPackage.tbs.leafNode
  let tbs := serializeNE (KeyPackageTBS.mf tkt) keyPackage.tbs
  guard (verifyWithLabel leafNode.data.signatureKey.val "KeyPackageTBS" tbs keyPackage.signature.val)
  let addPend ← extractResult (TreeSync.API.prepareAdd st.treesync leafNode)
  let token ← Symbolic.API.getTokenFor me authServiceSid addPend.asInput
  let (treesync, addIndex) ← extractResult (TreeSync.API.finalizeAdd addPend token)
  ProtocolEvent.logEvent ({ prin := me, keyPackage }: KeyPackageHasBeenVerified)
  logLeafNodeVerificationEvent me leafNode st.groupContext.groupId addIndex
  let (treekem, _) := API.add st.treekem { publicKey := keyPackage.tbs.leafNode.data.content.val }
  pure (keyPackage, addIndex, { st with treesync, treekem })

/--
Port of `_process_add_proposal`.
MLS* requires `P_add? proposal`; otherwise, this function fails.
-/
public
def processAddProposal' (me: Participant) (authServiceSid: Nat)
  (lSt: List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  Traceful (List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState)
:= do
  let (l, st) := lSt
  let (keyPackage, addIndex, st) ← processAddProposalAux' me authServiceSid st proposal
  pure ((keyPackage, addIndex) :: l, st)

/--
Port of `_process_update_proposal`.
MLS* requires `P_update? proposal.proposal`; otherwise, this function fails.
-/
public
def processUpdateProposal' (me: Participant) (authServiceSid: Nat) (updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposal: ProposalAndSender): Traceful TreeSyncTreeKEMState
:= do
  let .update { leafNode } := proposal.proposal | failure
  guard (proposal.sender < 2^st.treesync.levels)
  let senderIndex := proposal.sender
  let pendUpdate ← extractResult (TreeSync.API.prepareUpdate st.treesync leafNode senderIndex)
  let token ← Symbolic.API.getTokenFor me authServiceSid pendUpdate.asInput
  let treesync := TreeSync.API.finalizeUpdate pendUpdate token
  logLeafNodeVerificationEvent me leafNode st.groupContext.groupId senderIndex
  guard (st.treesync.levels = st.treekem.treeState.levels)
  let treekem ←
    if senderIndex = st.leafIndex then do
      let leafSkSid ← findUpdateLeafSk me updateCacheSid leafNode
      let leafSk ← getLeafNodeKey me leafSkSid
      pure (API.updateMyself st.treekem { publicKey := leafNode.data.content.val } leafSk)
    else
      pure (API.updateOther st.treekem { publicKey := leafNode.data.content.val } senderIndex)
  pure { st with treesync, treekem }

/--
Port of `_process_remove_proposal`.
MLS* requires `P_remove? proposal`; otherwise, this function fails.
-/
public
def processRemoveProposal' (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes): Traceful TreeSyncTreeKEMState := do
  let .remove { removed } := proposal | failure
  let removed := removed.toNat
  guard (removed < 2^st.treesync.levels)
  guard (removed ≠ st.leafIndex)
  guard (st.treesync.levels = st.treekem.treeState.levels)
  let removePend ← extractResult (TreeSync.API.prepareRemove st.treesync removed)
  let treesync := TreeSync.API.finalizeRemove removePend
  let treekem := API.remove st.treekem removed
  pure { st with treesync, treekem }

/--
Port of `sort_proposals_output`.
The refinements on the proposals (e.g. `P_add? proposal`) are dropped.
-/
public
structure SortProposalsOutput where
  groupContextExtensions: List (Proposal Bytes)
  adds: List (Proposal Bytes)
  updates: List ProposalAndSender
  removes: List (Proposal Bytes)
  psks: List (PreSharedKeyId Bytes)
  other: List (Proposal Bytes)

/-- Port of `_sort_proposals`. -/
public
def sortProposals': List ProposalAndSender → SortProposalsOutput
  | [] => {
    groupContextExtensions := []
    adds := []
    updates := []
    removes := []
    psks := []
    other := []
  }
  | h :: t =>
    let tmp := sortProposals' t
    match h.proposal with
    | .groupContextExtensions _ => { tmp with groupContextExtensions := h.proposal :: tmp.groupContextExtensions }
    | .add _ => { tmp with adds := h.proposal :: tmp.adds }
    | .update _ => { tmp with updates := h :: tmp.updates }
    | .remove _ => { tmp with removes := h.proposal :: tmp.removes }
    | .psk { psk } => { tmp with psks := psk :: tmp.psks }
    | _ => { tmp with other := h.proposal :: tmp.other }

/-- Port of `_process_proposals`. -/
public
def processProposals' (me: Participant) (authServiceSid: Nat) (updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender):
  Traceful (TreeSyncTreeKEMState × List (KeyPackage Bytes tkt × Nat) × List (PreSharedKeyId Bytes) × List (Proposal Bytes) × Bool)
:= do
  let sortedProposals := sortProposals' proposals
  let st ← sortedProposals.groupContextExtensions.foldlM processGroupContextExtensionsProposal' st
  let st ← sortedProposals.updates.foldlM (processUpdateProposal' me authServiceSid updateCacheSid) st
  let st ← sortedProposals.removes.foldlM processRemoveProposal' st
  let (adds, st) ← sortedProposals.adds.foldlM (processAddProposal' me authServiceSid) ([], st)
  let canAddOnly :=
    !proposals.isEmpty &&
    sortedProposals.groupContextExtensions.isEmpty &&
    sortedProposals.updates.isEmpty &&
    sortedProposals.removes.isEmpty
  pure (st, adds.reverse, sortedProposals.psks, sortedProposals.other, canAddOnly)

/--
Port of `_make_provisional_group_context`.
The refinement of the result (it has the same group identifier) is a subtype.
-/
public
def makeProvisionalGroupContext' {groupId: MlsBytes Bytes}
  (groupContext: GroupContext Bytes) (treesync: TreeSyncState Bytes tkt DyAsToken groupId):
  Traceful {provisionalGroupContext: GroupContext Bytes // provisionalGroupContext.groupId = groupContext.groupId}
:=
  extractResult (do
    let treeHash ← TreeSync.API.computeTreeHash treesync
    let treeHash ← mkMlsBytes treeHash "_make_provisional_group_context" "tree_hash"
    if groupContext.epoch.toNat + 1 < 2^64 then
      pure ⟨{ groupContext with treeHash, epoch := groupContext.epoch + 1 }, rfl⟩
    else
      Result.error "_make_provisional_group_context: epoch too big"
  )

/-- Port of `_process_update_path`. -/
public
def processUpdatePath' (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (senderIndex: Nat) (path: TreeKEM.UpdatePath Bytes)
  (joiners: List (KeyPackage Bytes tkt × Nat)):
  Traceful (TreeSyncState Bytes tkt DyAsToken st.groupContext.groupId × API.PendingProcessCommit st.treekem × GroupContext Bytes)
:= do
  guard (senderIndex < 2^st.treesync.levels)
  guard (senderIndex ≠ st.leafIndex)
  let uncompressedPath ← extractResult (uncompressUpdatePath senderIndex st.treesync.tree path)

  let treesyncPath := updatePathToTreesync uncompressedPath
  let commitPend ← extractResult (TreeSync.API.prepareCommit st.treesync senderIndex treesyncPath)
  let token ← Symbolic.API.getTokenFor me authServiceSid commitPend.asInput
  let treesync ← extractResult (TreeSync.API.finalizeCommit commitPend token)
  logLeafNodeVerificationEvent me treesyncPath.getPathLeaf st.groupContext.groupId senderIndex

  let provisionalGroupContext ← makeProvisionalGroupContext' st.groupContext treesync

  let treekemPath := updatePathToTreekem uncompressedPath
  if h: st.treesync.levels = st.treekem.treeState.levels then
    let treekemPath: PathKEM Bytes st.treekem.treeState.levels := h ▸ treekemPath
    guard (st.leafIndex ∉ joiners.map (·.2))
    let pendingTreekem ← extractResult (API.prepareProcessFullCommit st.treekem {
      commitLeafInd := senderIndex
      path := treekemPath
      excludedLeaves := joiners.map (·.2)
      provisionalGroupContext := provisionalGroupContext.val
    })
    pure (treesync, pendingTreekem, provisionalGroupContext.val)
  else
    failure

/-- Port of `_process_no_update_path`. -/
public
def processNoUpdatePath' (st: TreeSyncTreeKEMState):
  Traceful (TreeSyncState Bytes tkt DyAsToken st.groupContext.groupId × API.PendingProcessCommit st.treekem × GroupContext Bytes)
:= do
  let provisionalGroupContext ← makeProvisionalGroupContext' st.groupContext st.treesync
  let pendingTreekem ← extractResult (API.prepareProcessAddOnlyCommit st.treekem)
  pure (st.treesync, pendingTreekem, provisionalGroupContext.val)

/-- Port of `_process_opt_update_path`. -/
public
def processOptUpdatePath' (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (senderIndex: Nat) (optPath: Option (TreeKEM.UpdatePath Bytes))
  (joiners: List (KeyPackage Bytes tkt × Nat))
  (newConfirmedTranscriptHash: MlsBytes Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)): Traceful TreeSyncTreeKEMState
:= do
  let (newTreesync, pendingTreekem, provisionalGroupContext) ←
    match optPath with
    | some path => processUpdatePath' me authServiceSid st senderIndex path joiners
    | none => processNoUpdatePath' st
  let newGroupContext: GroupContext Bytes := {
    provisionalGroupContext with
    groupId := st.groupContext.groupId
    confirmedTranscriptHash := newConfirmedTranscriptHash
  }
  let (newTreekem, _encryptionSecret) ← extractResult (API.finalizeProcessCommit pendingTreekem psks newGroupContext)
  pure {
    leafIndex := st.leafIndex
    groupContext := newGroupContext
    mySignatureKeySid := st.mySignatureKeySid
    treesync := newTreesync
    treekem := newTreekem
  }

/--
Port of `_compute_confirmed_transcript_hash`.
MLS* requires `tx_hash_input.content.content.content_type == CT_commit`; this precondition is not needed here.
-/
public
def computeConfirmedTranscriptHash' (st: TreeSyncTreeKEMState) (txHashInput: ConfirmedTranscriptHashInput Bytes):
  Result (MlsBytes Bytes)
:= do
  let interimTranscriptHash ←
    computeInterimTranscriptHash st.treekem.keyscheduleState.epochKeys.confirmationTag st.groupContext.confirmedTranscriptHash.val
  let confirmedTranscriptHash ← computeConfirmedTranscriptHash txHashInput interimTranscriptHash
  mkMlsBytes confirmedTranscriptHash "_compute_confirmed_transcript_hash" "confirmed_transcript_hash"

/--
Port of `_process_commit`.
Returns the new state, and the new handle of the PSK store.
MLS* requires `tx_hash_input.content.content.content_type == CT_commit`; otherwise, this function fails.
-/
public
def processCommit' (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st: TreeSyncTreeKEMState) (txHashInput: ConfirmedTranscriptHashInput Bytes): Traceful (TreeSyncTreeKEMState × Nat)
:= do
  let originalSt := st
  let framedCommit := txHashInput.content
  let ⟨.commit, (commit: Commit Bytes)⟩ := framedCommit.content | failure

  let senderIndex ←
    match framedCommit.sender with
    | .member senderIndex => pure senderIndex.toNat
    | _ => failure

  let newConfirmedTranscriptHash ← extractResult (computeConfirmedTranscriptHash' st txHashInput)

  let proposalsOrRefs := commit.proposals.val
  let proposals ← retrieveProposals me proposalCacheSid senderIndex proposalsOrRefs

  let (st, joiners, pskIds, _otherProposals, canAddOnly) ← processProposals' me authServiceSid updateCacheSid st proposals
  guard (canAddOnly || commit.path.isSome)
  let psks ← retrievePsks me pskStoreSid pskIds
  let st ← processOptUpdatePath' me authServiceSid st senderIndex commit.path joiners newConfirmedTranscriptHash psks

  let pskStoreSid ← rememberPsk me pskStoreSid
    (.resumptionPsk st.groupContext.groupId st.groupContext.epoch) (API.getEpochKeys st.treekem).resumptionPsk

  ProtocolEvent.logEvent ({
    prin := me
    how := .processedCommit {
      previousInitSecret := originalSt.treekem.keyscheduleState.initSecret
      previousGroupContext := originalSt.groupContext
      previousTreeHeight := originalSt.treesync.levels
      previousTree := originalSt.treesync.tree
      commitTy := if commit.path.isSome then .fullCommit else .addOnlyCommit
      joiners := joiners.map (·.1)
    }
    groupContext := st.groupContext
    treeHeight := st.treesync.levels
    tree := st.treesync.tree
    psks
    epochKeys := st.treekem.keyscheduleState
  }: IAmInGroup)

  pure (st, pskStoreSid)

/--
Port of `process_commit`.
Returns the handle of the new group state, and the new handle of the PSK store.
-/
public
def processCommit (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (groupStateSid: Nat) (commitTs: Nat): Traceful (Nat × Nat)
:= do
  let st ← getTreesyncTreekemState me groupStateSid
  let commitBytes ← Network.receiveMessage commitTs
  let some commit := (ConfirmedTranscriptHashInput.mf (Bytes := Bytes)).toExtensible.parse commitBytes | failure
  guard (commit.content.content.contentType = .commit)
  let (st, pskStoreSid) ← processCommit' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st commit
  let newGroupStateSid ← storeTreesyncTreekemState me st
  pure (newGroupStateSid, pskStoreSid)

end MLS.TreeKEM
