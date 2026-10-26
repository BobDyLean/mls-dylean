module

public import MLS.TreeKEM.Symbolic.Traceful.CreateGroup
public import MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal
public import MLS.TreeKEM.Symbolic.Traceful.ProcessProposal
public import MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome
public import MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome
meta import MLS.TreeKEM.Symbolic.Traceful.CreateGroup
meta import MLS.TreeKEM.Symbolic.Traceful.GenerateUpdateProposal
meta import MLS.TreeKEM.Symbolic.Traceful.ProcessProposal
meta import MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome
meta import MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome

/-!
Sanity checks for the symbolic specification of TreeKEM (not in MLS*):
an honest run of the traceful functions (`MLS.TreeKEM.Symbolic.Traceful.*`),
in which the attacker only forwards the messages of honest participants,
must succeed (`#guard`).
In `scenario`, Alice creates a group, then adds Bob and Charlie (proposals by value, full commit, Welcome);
Bob adds Dave, proposed by Charlie (proposal by reference, add-only commit);
finally, Alice commits the update proposal of Bob (by reference), the removal of Dave,
a resumption PSK and group context extensions.
After each epoch, the members check that they agree on the epoch secrets.

`scenario` stops at epoch 3: the symbolic terms of the key schedule embed several copies of those of the previous epoch,
and DyLean's equality on bytes does not take advantage of the sharing,
so reading a group state (`getTreesyncTreekemState`, which compares confirmation tags)
costs about 8 times more at each epoch.
`fullScenario` is a longer run (epochs 0 to 6) which is not checked yet, as it would take hours.

Reachability of this run is not proved yet.
-/

namespace MLS.TreeKEM.SanityChecks

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap
open DySlop.Map (Map)

/-! ## Top-level instances (execution only) -/

#combine +toplevel into BytesFunctor, BytesLength, attackerKnowledge from
  DY.Random,
  DY.Literal,
  DY.Concat,
  DY.Hash,
  DySlop.KdfExtract,
  DySlop.KdfExpand,
  DySlop.Kem,
  DySlop.Signature,
  DySlop.Aead,
  DySlop.Mac

public instance: HasSymbolicBytes where

#combine +toplevel into ExecEntryT, baseAttackerKnowledge from
  Network,
  DY.Random,
  PersistentLocalState.CompromisableState TreeSyncSignatureKeyState,
  PersistentLocalState.CompromisableState (TreeSyncPublicState TreeKEM.tkt),
  PersistentLocalState.CompromisableState (Map AsCacheKey AsCacheValue),
  PersistentLocalState.CompromisableState (Map GroupManagerKey GroupManagerValue),
  PersistentLocalState.CompromisableState (Map (KeyPackage Bytes TreeKEM.tkt) KeyPackageManagerValue),
  ProtocolEvent (LeafNodeSignedEvent TreeKEM.tkt),
  ProtocolEvent (GroupHasTreeEvent TreeKEM.tkt),
  PersistentLocalState.CompromisableState TreeKEMNodeKeysState,
  PersistentLocalState.CompromisableState TreeKEMEpochSecret,
  PersistentLocalState.CompromisableState BareTreeSyncTreeKEMState,
  PersistentLocalState.CompromisableState OnePskState,
  PersistentLocalState.CompromisableState (Map PskStoreKey PskStoreValue),
  PersistentLocalState.CompromisableState (Map ProposalCacheKey ProposalAndSender),
  PersistentLocalState.CompromisableState (Map UpdateCacheKey UpdateCacheValue),
  PersistentLocalState.CompromisableState BootstrapInitKeyState,
  PersistentLocalState.CompromisableState KeyPackageStorePre,
  ProtocolEvent IAmInGroup,
  ProtocolEvent KeyPackageHasBeenVerified,
  ProtocolEvent (LeafNodeHasBeenVerified TreeKEM.tkt)

public instance: HasTreeSyncExecTrace TreeKEM.tkt where
public instance: HasTreeKEMExecTrace where

/-! ## Messages crafted by the attacker -/

/-- The empty `MlsList`. -/
public
def emptyMlsList {α: Type} {mf: NonExtensibleMessageFormat Bytes α} [mf.ParseConsumes]: MlsList mf :=
  ⟨[], by simp [BytesLike.empty_length, mlsNatPred]⟩

/-- A leaf node skeleton: its credential, keys and signature are replaced by the honest participant. -/
public
def leafNodeSkeleton (source: LeafNodeSource): LeafNode Bytes TreeKEM.tkt := {
  data := {
    content := (MlsBytes.empty: HpkePublicKey Bytes)
    signatureKey := MlsBytes.empty
    credential := .basic MlsBytes.empty
    capabilities := {
      versions := emptyMlsList
      ciphersuites := emptyMlsList
      extensions := emptyMlsList
      proposals := emptyMlsList
      credentials := emptyMlsList
    }
    source
    lifetime := StaticOption.mk { notBefore := 0, notAfter := 0 }
    parentHash := StaticOption.mk MlsBytes.empty
    extensions := emptyExtensions
  }
  signature := MlsBytes.empty
}

/-- A key package skeleton: its init key, leaf node and signature are replaced by the honest participant. -/
public
def keyPackageSkeleton: KeyPackage Bytes TreeKEM.tkt := {
  tbs := {
    version := .mls10
    cipherSuite := availableCiphersuiteToNetwork (CryptoBytes.ciphersuite Bytes)
    initKey := MlsBytes.empty
    leafNode := leafNodeSkeleton .keyPackage
    extensions := emptyExtensions
  }
  signature := MlsBytes.empty
}

/--
A commit skeleton: its group identifier, epoch, sender and update path are replaced by the honest participant;
the update path is present if and only if `fullCommit`.
-/
public
def commitSkeleton (proposals: List (ProposalOrRef Bytes)) (fullCommit: Bool):
  Traceful (ConfirmedTranscriptHashInput Bytes)
:= do
  let proposals ← extractResult (mkMlsList proposals "commitSkeleton" "proposals")
  let commit: Commit Bytes := {
    proposals
    path := if fullCommit then some { leafNode := leafNodeSkeleton .commit, nodes := emptyMlsList } else none
  }
  pure {
    wireFormat := .mlsPublicMessage
    content := {
      groupId := MlsBytes.empty
      epoch := 0
      sender := .member 0
      authenticatedData := MlsBytes.empty
      content := { contentType := .commit, content := commit }
    }
    signature := MlsBytes.empty
  }

/-- The attacker reads a key package from the network. -/
public
def receiveKeyPackage (keyPackageTs: Nat): Traceful (KeyPackage Bytes TreeKEM.tkt) := do
  let keyPackageBytes ← Network.receiveMessage keyPackageTs
  let some keyPackage := (KeyPackage.mf TreeKEM.tkt).toExtensible.parse keyPackageBytes | failure
  pure keyPackage

/-- The attacker reads a proposal from the network. -/
public
def receiveProposal (proposalTs: Nat): Traceful (Proposal Bytes) := do
  let proposalBytes ← Network.receiveMessage proposalTs
  let some proposal := (Proposal.mf (Bytes := Bytes)).toExtensible.parse proposalBytes | failure
  pure proposal

/-- The attacker sends a proposal on the network. -/
public
def sendProposal (proposal: Proposal Bytes): Traceful Nat :=
  Network.sendMessage (serializeNE Proposal.mf proposal)

/-- The reference to a proposal, for proposals sent separately from the commit. -/
public
def proposalRef (proposal: Proposal Bytes): Traceful (ProposalOrRef Bytes) := do
  let ref ← extractResult (makeProposalRef (serializeNE Proposal.mf proposal))
  let ref ← extractResult (mkMlsBytes ref "proposalRef" "ref")
  pure (.reference ref)

/-! ## Honest clients -/

/-- The handles of the states of a client. -/
public
structure Client where
  me: Participant
  signatureKeySid: Nat
  authServiceSid: Nat
  keyPackageStoreSid: Nat
  proposalCacheSid: Nat
  updateCacheSid: Nat
  pskStoreSid: Nat
  groupStateSid: Nat

/-- Initializes the states of a client. -/
public
def Client.initialize (me: Participant): Traceful Client := do
  let signatureKeySid ← mkSignatureKey me
  let authServiceSid ← initializeAsCache me
  let keyPackageStoreSid ← initializeKeyPackageStore me
  let proposalCacheSid ← initializeProposalCache me
  let updateCacheSid ← initializeUpdateCache me
  let pskStoreSid ← initializePskStore me
  pure { me, signatureKeySid, authServiceSid, keyPackageStoreSid, proposalCacheSid, updateCacheSid, pskStoreSid, groupStateSid := 0 }

/-- The authentication service of `c` verifies the credential of `other`. -/
public
def Client.verifyCredential (c other: Client): Traceful Client := do
  let verificationKey ← getSignatureKeyVk other.me other.signatureKeySid
  let verificationKey ← extractResult (mkMlsBytes verificationKey "verifyCredential" "verificationKey")
  let some credential := principalToCredential (Bytes := Bytes) other.me | failure
  let authServiceSid ← addVerifiedCredential c.me c.authServiceSid { verificationKey, credential } { token := { time := 0 } }
  pure { c with authServiceSid }

/-- The authentication service of `c` verifies the credentials of `others`. -/
public
def Client.verifyCredentials (c: Client) (others: List Client): Traceful Client :=
  others.foldlM Client.verifyCredential c

/-- `c` creates a group. -/
public
def Client.createGroup (c: Client): Traceful Client := do
  let leafNodeSkeletonTs ← Network.sendMessage (serializeNE (LeafNode.mf TreeKEM.tkt) (leafNodeSkeleton .keyPackage))
  let groupStateSid ← TreeKEM.createGroup c.me c.signatureKeySid c.authServiceSid leafNodeSkeletonTs
  pure { c with groupStateSid }

/-- Returns the handle of the key package. -/
public
def Client.generateKeyPackage (c: Client): Traceful (Nat × Client) := do
  let keyPackageSkeletonTs ← Network.sendMessage (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackageSkeleton)
  let (keyPackageTs, keyPackageStoreSid) ←
    TreeKEM.generateKeyPackage c.me keyPackageSkeletonTs c.signatureKeySid c.keyPackageStoreSid
  pure (keyPackageTs, { c with keyPackageStoreSid })

/-- Returns the handle of the update proposal. -/
public
def Client.generateUpdateProposal (c: Client): Traceful (Nat × Client) := do
  let leafNodeSkeletonTs ← Network.sendMessage (serializeNE (LeafNode.mf TreeKEM.tkt) (leafNodeSkeleton .update))
  let (proposalTs, updateCacheSid) ←
    TreeKEM.generateUpdateProposal c.me c.updateCacheSid c.groupStateSid leafNodeSkeletonTs c.signatureKeySid
  pure (proposalTs, { c with updateCacheSid })

/-- `c` stores the proposal of `sender` in its proposal cache. -/
public
def Client.processProposal (c: Client) (proposalTs: Nat) (sender: Nat): Traceful Client := do
  let proposalCacheSid ← TreeKEM.processProposal c.me c.proposalCacheSid proposalTs sender
  pure { c with proposalCacheSid }

/-- `c` creates a commit (with an update path if and only if `fullCommit`), and the Welcome message if any. -/
public
def Client.commit (c: Client) (proposals: List (ProposalOrRef Bytes)) (fullCommit: Bool):
  Traceful (CreateCommitAndWelcomeResult × Client)
:= do
  let messageSkeletonTs ← Network.sendMessage (serializeNE ConfirmedTranscriptHashInput.mf (← commitSkeleton proposals fullCommit))
  let (res, pskStoreSid) ←
    createCommitAndWelcome c.me c.authServiceSid c.proposalCacheSid c.updateCacheSid c.pskStoreSid c.groupStateSid messageSkeletonTs
  pure (res, { c with groupStateSid := res.newGroupStateSid, pskStoreSid })

/-- `c` processes a commit. -/
public
def Client.processCommit (c: Client) (commitTs: Nat): Traceful Client := do
  let (groupStateSid, pskStoreSid) ←
    TreeKEM.processCommit c.me c.authServiceSid c.proposalCacheSid c.updateCacheSid c.pskStoreSid c.groupStateSid commitTs
  pure { c with groupStateSid, pskStoreSid }

/-- `c` joins a group from a Welcome message. -/
public
def Client.processWelcome (c: Client) (welcomeTs ratchetTreeTs: Nat): Traceful Client := do
  let (groupStateSid, pskStoreSid) ←
    TreeKEM.processWelcome c.me c.keyPackageStoreSid c.authServiceSid c.pskStoreSid welcomeTs ratchetTreeTs
  pure { c with groupStateSid, pskStoreSid }

/-- The group state of `c`. -/
public
def Client.state (c: Client): Traceful TreeSyncTreeKEMState :=
  getTreesyncTreekemState c.me c.groupStateSid

/--
Checks that the members `(c, leafIndex)` of the group are at their leaf index, in the epoch `epoch`,
and agree on the group identifier, the tree hash and the epoch secrets.
-/
public
def checkGroup (epoch: UInt64) (members: List (Client × Nat)): Traceful Unit := do
  let sts ← members.mapM fun (c, leafIndex) => do
    let st ← c.state
    guard (st.leafIndex = leafIndex)
    guard (st.groupContext.epoch = epoch)
    pure st
  let stRef :: sts := sts | failure
  for st in sts do
    guard (st.groupContext.groupId = stRef.groupContext.groupId)
    guard (st.groupContext.treeHash = stRef.groupContext.treeHash)
    guard ((API.getEpochKeys st.treekem).epochAuthenticator = (API.getEpochKeys stRef.treekem).epochAuthenticator)

/-! ## Scenario -/

/-- The honest run, described in the module docstring. -/
public
def scenario: Traceful Unit := do
  let alice ← Client.initialize "Alice"
  let bob ← Client.initialize "Bob"
  let charlie ← Client.initialize "Charlie"
  let dave ← Client.initialize "Dave"
  let alice ← alice.verifyCredentials [alice, bob, charlie, dave]
  let bob ← bob.verifyCredentials [alice, bob, charlie, dave]
  let charlie ← charlie.verifyCredentials [alice, bob, charlie, dave]
  let dave ← dave.verifyCredentials [alice, bob, charlie, dave]

  -- Epoch 0: Alice creates the group
  let alice ← alice.createGroup
  checkGroup 0 [(alice, 0)]

  -- Epoch 1: Alice adds Bob and Charlie (proposals by value, full commit)
  let (bobKeyPackageTs, bob) ← bob.generateKeyPackage
  let (charlieKeyPackageTs, charlie) ← charlie.generateKeyPackage
  let addBob: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage bobKeyPackageTs }
  let addCharlie: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage charlieKeyPackageTs }
  let (res, alice) ← alice.commit [.proposal addBob, .proposal addCharlie] true
  let some welcomeTs := res.optWelcomeTs | failure
  let bob ← bob.processWelcome welcomeTs res.ratchetTreeTs
  let charlie ← charlie.processWelcome welcomeTs res.ratchetTreeTs
  checkGroup 1 [(alice, 0), (bob, 1), (charlie, 2)]

  -- Epoch 2: Charlie proposes to add Dave, Bob commits it (proposal by reference, add-only commit)
  let (daveKeyPackageTs, dave) ← dave.generateKeyPackage
  let addDave: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage daveKeyPackageTs }
  let addDaveTs ← sendProposal addDave
  let alice ← alice.processProposal addDaveTs 2
  let bob ← bob.processProposal addDaveTs 2
  let charlie ← charlie.processProposal addDaveTs 2
  let (res, bob) ← bob.commit [← proposalRef addDave] false
  let some welcomeTs := res.optWelcomeTs | failure
  let alice ← alice.processCommit res.messageTs
  let charlie ← charlie.processCommit res.messageTs
  let dave ← dave.processWelcome welcomeTs res.ratchetTreeTs
  checkGroup 2 [(alice, 0), (bob, 1), (charlie, 2), (dave, 3)]

  -- Epoch 3: Bob proposes to update his leaf; Alice commits it (proposal by reference),
  -- along with the removal of Dave, the resumption PSK of epoch 2, and group context extensions
  -- (proposals by value, full commit)
  let (updateBobTs, bob) ← bob.generateUpdateProposal
  let updateBob ← receiveProposal updateBobTs
  let alice ← alice.processProposal updateBobTs 1
  let bob ← bob.processProposal updateBobTs 1
  let charlie ← charlie.processProposal updateBobTs 1
  let dave ← dave.processProposal updateBobTs 1
  let groupId := (← alice.state).groupContext.groupId
  let pskNonce ← extractResult (mkMlsBytes (← Random.genRand 32) "scenario" "pskNonce")
  let removeDave: Proposal Bytes := .remove { removed := 3 }
  let pskEpoch2: Proposal Bytes := .psk { psk := .resumption .application groupId 2 pskNonce }
  let groupContextExtensions: Proposal Bytes := .groupContextExtensions { extensions := emptyExtensions }
  let (res, alice) ← alice.commit
    [← proposalRef updateBob, .proposal removeDave, .proposal pskEpoch2, .proposal groupContextExtensions] true
  guard res.optWelcomeTs.isNone
  let bob ← bob.processCommit res.messageTs
  let charlie ← charlie.processCommit res.messageTs
  -- Dave has been removed: he cannot process the commit
  let daveFailed ← (do let _ ← dave.processCommit res.messageTs; pure false) <|> pure true
  guard daveFailed
  checkGroup 3 [(alice, 0), (bob, 1), (charlie, 2)]

#guard (scenario.run Trace.nil).fst = some ()

/--
A longer honest run, not checked yet (see the module docstring):
- epoch 1: Alice adds Bob and Charlie (proposals by value, full commit),
- epoch 2: Alice proposes to add Dave, Bob commits it (proposal by reference, add-only commit),
- epoch 3: Charlie commits without proposals (full commit),
- epoch 4: Alice commits the update proposal of Bob (by reference), the removal of Charlie,
  the resumption PSK of epoch 2 (which Dave stored when joining by Welcome), and group context extensions,
- epoch 5: Dave adds Charlie back, in the leaf left blank by his removal (full commit),
- epoch 6: Bob removes Alice and Dave (full commit).
-/
public
def fullScenario: Traceful Unit := do
  let alice ← Client.initialize "Alice"
  let bob ← Client.initialize "Bob"
  let charlie ← Client.initialize "Charlie"
  let dave ← Client.initialize "Dave"
  let alice ← alice.verifyCredentials [alice, bob, charlie, dave]
  let bob ← bob.verifyCredentials [alice, bob, charlie, dave]
  let charlie ← charlie.verifyCredentials [alice, bob, charlie, dave]
  let dave ← dave.verifyCredentials [alice, bob, charlie, dave]

  -- Epoch 0: Alice creates the group
  let alice ← alice.createGroup
  checkGroup 0 [(alice, 0)]

  -- Epoch 1: Alice adds Bob and Charlie (proposals by value, full commit)
  let (bobKeyPackageTs, bob) ← bob.generateKeyPackage
  let (charlieKeyPackageTs, charlie) ← charlie.generateKeyPackage
  let addBob: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage bobKeyPackageTs }
  let addCharlie: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage charlieKeyPackageTs }
  let (res, alice) ← alice.commit [.proposal addBob, .proposal addCharlie] true
  let some welcomeTs := res.optWelcomeTs | failure
  let bob ← bob.processWelcome welcomeTs res.ratchetTreeTs
  let charlie ← charlie.processWelcome welcomeTs res.ratchetTreeTs
  checkGroup 1 [(alice, 0), (bob, 1), (charlie, 2)]

  -- Epoch 2: Alice proposes to add Dave, Bob commits it (proposal by reference, add-only commit)
  let (daveKeyPackageTs, dave) ← dave.generateKeyPackage
  let addDave: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage daveKeyPackageTs }
  let addDaveTs ← sendProposal addDave
  let alice ← alice.processProposal addDaveTs 0
  let bob ← bob.processProposal addDaveTs 0
  let charlie ← charlie.processProposal addDaveTs 0
  let (res, bob) ← bob.commit [← proposalRef addDave] false
  let some welcomeTs := res.optWelcomeTs | failure
  let alice ← alice.processCommit res.messageTs
  let charlie ← charlie.processCommit res.messageTs
  let dave ← dave.processWelcome welcomeTs res.ratchetTreeTs
  checkGroup 2 [(alice, 0), (bob, 1), (charlie, 2), (dave, 3)]

  -- Epoch 3: Charlie commits without proposals (full commit)
  let (res, charlie) ← charlie.commit [] true
  guard res.optWelcomeTs.isNone
  let alice ← alice.processCommit res.messageTs
  let bob ← bob.processCommit res.messageTs
  let dave ← dave.processCommit res.messageTs
  checkGroup 3 [(alice, 0), (bob, 1), (charlie, 2), (dave, 3)]

  -- Epoch 4: Bob proposes to update his leaf; Alice commits it (proposal by reference),
  -- along with the removal of Charlie, the resumption PSK of epoch 2 (which Dave stored when joining),
  -- and group context extensions (proposals by value, full commit)
  let (updateBobTs, bob) ← bob.generateUpdateProposal
  let updateBob ← receiveProposal updateBobTs
  let alice ← alice.processProposal updateBobTs 1
  let bob ← bob.processProposal updateBobTs 1
  let charlie ← charlie.processProposal updateBobTs 1
  let dave ← dave.processProposal updateBobTs 1
  let groupId := (← alice.state).groupContext.groupId
  let pskNonce ← extractResult (mkMlsBytes (← Random.genRand 32) "fullScenario" "pskNonce")
  let removeCharlie: Proposal Bytes := .remove { removed := 2 }
  let pskEpoch2: Proposal Bytes := .psk { psk := .resumption .application groupId 2 pskNonce }
  let groupContextExtensions: Proposal Bytes := .groupContextExtensions { extensions := emptyExtensions }
  let (res, alice) ← alice.commit
    [← proposalRef updateBob, .proposal removeCharlie, .proposal pskEpoch2, .proposal groupContextExtensions] true
  guard res.optWelcomeTs.isNone
  let bob ← bob.processCommit res.messageTs
  let dave ← dave.processCommit res.messageTs
  -- Charlie has been removed: he cannot process the commit
  let charlieFailed ← (do let _ ← charlie.processCommit res.messageTs; pure false) <|> pure true
  guard charlieFailed
  checkGroup 4 [(alice, 0), (bob, 1), (dave, 3)]

  -- Epoch 5: Dave adds Charlie back, in the blank leaf (full commit)
  let (charlieKeyPackageTs, charlie) ← charlie.generateKeyPackage
  let addCharlie: Proposal Bytes := .add { keyPackage := ← receiveKeyPackage charlieKeyPackageTs }
  let (res, dave) ← dave.commit [.proposal addCharlie] true
  let some welcomeTs := res.optWelcomeTs | failure
  let alice ← alice.processCommit res.messageTs
  let bob ← bob.processCommit res.messageTs
  let charlie ← charlie.processWelcome welcomeTs res.ratchetTreeTs
  checkGroup 5 [(alice, 0), (bob, 1), (charlie, 2), (dave, 3)]

  -- Epoch 6: Bob removes Alice and Dave (proposals by value, full commit)
  let (res, bob) ← bob.commit [.proposal (.remove { removed := 0 }), .proposal (.remove { removed := 3 })] true
  guard res.optWelcomeTs.isNone
  let charlie ← charlie.processCommit res.messageTs
  checkGroup 6 [(bob, 1), (charlie, 2)]

-- Too slow for now (see the module docstring).
-- #guard (fullScenario.run Trace.nil).fst = some ()

end MLS.TreeKEM.SanityChecks
