module

public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateKeyPackage
public import MLS.Common.Code.Extensions
public import MLS.TreeKEM.Code.API

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.CreateGroup`.

The function `createGroup` creates a new group, as specified by the MLS RFC:
- create a fresh leaf node
  (using a leaf node skeleton as in update proposal creation)
- create the group context with empty confirmed transcript hash
- create a random epoch secret
- give to the attacker the handle of the group state

Port-specific differences:
- MLS*'s functions with a leading underscore (`_create_group`) end with a prime.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Create group -/

/-- Port of `_create_group`. -/
public
def createGroup' (me: Participant) (mySignatureKeySid: Nat) (authServiceSid: Nat) (leafNodeSkeleton: LeafNode Bytes tkt):
  Traceful TreeSyncTreeKEMState
:= do
  let groupId ← Random.genRand 32
  let groupId ← extractResult (mkMlsBytes groupId "_create_group" "group_id")
  let (leafNode, leafNodeKeySid) ← generateLeafNode' me leafNodeSkeleton mySignatureKeySid
  let pendingCreate ← extractResult (TreeSync.API.prepareCreate groupId leafNode)
  let token ← Symbolic.API.getTokenFor me authServiceSid pendingCreate.asInput
  let treesync := TreeSync.API.finalizeCreate pendingCreate token
  logLeafNodeVerificationEvent me leafNode groupId 0

  let treeHash ← extractResult (TreeSync.API.computeTreeHash treesync)
  let treeHash ← extractResult (mkMlsBytes treeHash "_create_group" "tree_hash")

  let groupContext: GroupContext Bytes := {
    version := .mls10
    cipherSuite := availableCiphersuiteToNetwork (CryptoBytes.ciphersuite Bytes)
    groupId
    epoch := 0
    treeHash
    confirmedTranscriptHash := MlsBytes.empty
    extensions := emptyExtensions
  }

  let leafSk ← getLeafNodeKey me leafNodeKeySid
  let leafPk := DySlop.HPKE.hpkePk leafSk
  guard (leafPk = leafNode.data.content.val)

  let epochSecret ← Random.genRand (CryptoBytes.kdfLength Bytes)
  let (treekem, _) ← extractResult (API.create leafSk leafPk epochSecret groupContext)

  ProtocolEvent.logEvent ({
    prin := me
    how := .justCreated
    groupContext
    treeHeight := treesync.levels
    tree := treesync.tree
    psks := []
    epochKeys := treekem.keyscheduleState
  }: IAmInGroup)

  pure {
    leafIndex := 0
    groupContext
    mySignatureKeySid
    treesync
    treekem
  }

/-- Port of `create_group`. Returns the handle of the group state. -/
public
def createGroup (me: Participant) (mySignatureKeySid: Nat) (authServiceSid: Nat) (leafNodeSkeletonTs: Nat): Traceful Nat := do
  let leafNodeSkeletonBytes ← Network.receiveMessage leafNodeSkeletonTs
  let some leafNodeSkeleton := (LeafNode.mf tkt).toExtensible.parse leafNodeSkeletonBytes | failure
  let st ← createGroup' me mySignatureKeySid authServiceSid leafNodeSkeleton
  storeTreesyncTreekemState me st

end MLS.TreeKEM
