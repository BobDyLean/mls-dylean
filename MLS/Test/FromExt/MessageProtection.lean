module

public import MLS.TreeDEM.Code.Message.Framing
public import MLS.Test.FromExt.CryptoBasics
public import MLS.Test.Types
public import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.MessageProtection`.

Port-specific differences:
- MLS* types have no `DecidableEq`: messages are compared through their serialization.
- Parsing uses the `BytesLike` structure of the `CryptoBytes` instance (see `MLS.Test.FromExt.TreeKEM`).
-/

namespace MLS.Test.FromExt.MessageProtection

open Comparse
open MLS MLS.TreeDEM
open MLS.Test
open MLS.Test.FromExt.CryptoBasics

section CryptoBytes

variable [CryptoBytes ByteArray]

/-! ## Utility functions -/

/-- Port of `extract_public_message`. -/
@[expose]
public
def extractPublicMessage (s: String): IO (PublicMessage ByteArray) := do
  match MlsMessage.mf.toExtensible.parse (← hexStringToBytes s) with
  | none => throw (IO.userError "extract_public_message: not a parseable mls_message")
  | some (.mls10 (.publicMessage res)) => pure res
  | some _ => throw (IO.userError "extract_public_message: not a public message")

/-- Port of `extract_private_message`. -/
@[expose]
public
def extractPrivateMessage (s: String): IO (PrivateMessage ByteArray) := do
  match MlsMessage.mf.toExtensible.parse (← hexStringToBytes s) with
  | none => throw (IO.userError "extract_private_message: not a parseable mls_message")
  | some (.mls10 (.privateMessage res)) => pure res
  | some _ => throw (IO.userError "extract_private_message: not a private message")

/-- Port of `get_group_context`. -/
@[expose]
public
def getGroupContext (t: MessageProtectionTest): IO (GroupContext ByteArray) := do
  genGroupContext (CryptoBytes.ciphersuite ByteArray) (← hexStringToBytes t.groupId) t.epoch.toNat (← hexStringToBytes t.treeHash) (← hexStringToBytes t.confirmedTranscriptHash)

/-- Port of `unprotect_public_message`. -/
@[expose]
public
def unprotectPublicMessage (pubMsgStr: String) (t: MessageProtectionTest): IO (AuthenticatedContent ByteArray) := do
  let pubMsg ← extractPublicMessage pubMsgStr
  let groupContext ← getGroupContext t
  let membershipKey ← hexStringToBytes t.membershipKey
  extractResult (publicMessageToAuthenticatedContent pubMsg (StaticOption.mk groupContext) (StaticOption.mk membershipKey))

/-- Port of `unprotect_private_message`. -/
@[expose]
public
def unprotectPrivateMessage (privMsgStr: String) (t: MessageProtectionTest): IO (AuthenticatedContent ByteArray) := do
  let privMsg ← extractPrivateMessage privMsgStr
  let encryptionSecret ← hexStringToBytes t.encryptionSecret
  let senderDataSecret ← hexStringToBytes t.senderDataSecret
  extractResult (privateMessageToAuthenticatedContent privMsg 1 encryptionSecret senderDataSecret)

/-- Port of `check_signature`. -/
@[expose]
public
def checkSignature (authMsg: AuthenticatedContent ByteArray) (t: MessageProtectionTest): IO Unit := do
  let groupContext ← getGroupContext t
  let signaturePub ← hexStringToBytes t.signaturePub
  if !checkAuthenticatedContentSignature authMsg signaturePub (StaticOption.mk groupContext) then
    throw (IO.userError "check_signature: bad signature")

/-- Port of `compute_framed_content_auth_data`. -/
@[expose]
public
def computeFramedContentAuthData (wf: WireFormat) (content: FramedContent ByteArray) (groupContext: GroupContext ByteArray)
  (signaturePriv: ByteArray): IO (FramedContentAuthData ByteArray content.content.contentType)
:= do
  let nonce := mkZeroVector (CryptoBytes.signSignMinEntropyLength ByteArray)
  let signature ← extractResult (computeMessageSignature signaturePriv nonce wf content (StaticOption.mk groupContext))
  pure {
    signature
    confirmationTag := StaticOption.mk (← extractResult (mkMlsBytes zeroVector "" ""))
  }

/-- Compare two authenticated contents (MLS*'s `auth_msg <> auth_msg_roundtrip`) through their serialization. -/
@[expose]
public
def authenticatedContentEq (x y: AuthenticatedContent ByteArray): Bool :=
  serializeNE AuthenticatedContent.mf x == serializeNE AuthenticatedContent.mf y

/-- Port of `check_public_message_roundtrip`. -/
@[expose]
public
def checkPublicMessageRoundtrip (msg: FramedContent ByteArray) (t: MessageProtectionTest): IO Unit := do
  let groupContext ← getGroupContext t
  let signaturePriv ← hexStringToBytes t.signaturePriv
  let membershipKey ← hexStringToBytes t.membershipKey
  let auth ← computeFramedContentAuthData .mlsPublicMessage msg groupContext signaturePriv
  let authMsg: AuthenticatedContent ByteArray := { wireFormat := .mlsPublicMessage, content := msg, auth }
  let pubMsg ← extractResult (authenticatedContentToPublicMessage authMsg (StaticOption.mk groupContext) (StaticOption.mk membershipKey))
  let authMsgRoundtrip ← extractResult (publicMessageToAuthenticatedContent pubMsg (StaticOption.mk groupContext) (StaticOption.mk membershipKey))
  checkSignature authMsgRoundtrip t
  if !authenticatedContentEq authMsg authMsgRoundtrip then
    throw (IO.userError "check_public_message_roundtrip: roundtrip is not equal to original value")

/-- Port of `check_private_message_roundtrip`. -/
@[expose]
public
def checkPrivateMessageRoundtrip (msg: FramedContent ByteArray) (t: MessageProtectionTest): IO Unit := do
  let groupContext ← getGroupContext t
  let signaturePriv ← hexStringToBytes t.signaturePriv
  let encryptionSecret ← hexStringToBytes t.encryptionSecret
  let senderDataSecret ← hexStringToBytes t.senderDataSecret
  let ratchet ← extractResult (do
    let leafTreeSecret ← leafKdf encryptionSecret 1 0 1
    match msg.content.contentType with
    | .application => initApplicationRatchet leafTreeSecret
    | _ => initHandshakeRatchet leafTreeSecret
  )
  let auth ← computeFramedContentAuthData .mlsPrivateMessage msg groupContext signaturePriv
  let authMsg: AuthenticatedContent ByteArray := { wireFormat := .mlsPrivateMessage, content := msg, auth }
  let (privMsg, _) ← extractResult (authenticatedContentToPrivateMessage authMsg ratchet (mkZeroVector 4) senderDataSecret)
  let authMsgRoundtrip ← extractResult (privateMessageToAuthenticatedContent privMsg 1 encryptionSecret senderDataSecret)
  checkSignature authMsgRoundtrip t
  if !authenticatedContentEq authMsg authMsgRoundtrip then
    throw (IO.userError "check_private_message_roundtrip: roundtrip is not equal to original value")

/-! ## Proposal test -/

/-- Port of `extract_proposal`. -/
@[expose]
public
def extractProposal (content: AuthenticatedContent ByteArray): IO (Proposal ByteArray) :=
  match content.content.content with
  | { contentType := .proposal, content := p } => pure p
  | _ => throw (IO.userError "extract_proposal: not a proposal")

/-- Port of `test_proposal_protection`. -/
@[expose]
public
def testProposalProtection (t: MessageProtectionTest): IO Unit := do
  let proposal ← hexStringToBytes t.proposal
  let authenticatedProposalPub ← unprotectPublicMessage t.proposalPub t
  let authenticatedProposalPriv ← unprotectPrivateMessage t.proposalPriv t
  checkSignature authenticatedProposalPub t
  checkSignature authenticatedProposalPriv t
  checkPublicMessageRoundtrip authenticatedProposalPub.content t
  checkPrivateMessageRoundtrip authenticatedProposalPriv.content t
  checkEqual "proposal_pub" bytesToHexString proposal (serializeNE Proposal.mf (← extractProposal authenticatedProposalPub))
  checkEqual "proposal_priv" bytesToHexString proposal (serializeNE Proposal.mf (← extractProposal authenticatedProposalPriv))

/-! ## Commit test -/

/-- Port of `extract_commit`. -/
@[expose]
public
def extractCommit (content: AuthenticatedContent ByteArray): IO (Commit ByteArray) :=
  match content.content.content with
  | { contentType := .commit, content := c } => pure c
  | _ => throw (IO.userError "extract_commit: not a commit")

/-- Port of `test_commit_protection`. -/
@[expose]
public
def testCommitProtection (t: MessageProtectionTest): IO Unit := do
  let commit ← hexStringToBytes t.commit
  let authenticatedCommitPub ← unprotectPublicMessage t.commitPub t
  let authenticatedCommitPriv ← unprotectPrivateMessage t.commitPriv t
  checkSignature authenticatedCommitPub t
  checkSignature authenticatedCommitPriv t
  checkPublicMessageRoundtrip authenticatedCommitPub.content t
  checkPrivateMessageRoundtrip authenticatedCommitPriv.content t
  checkEqual "commit_pub" bytesToHexString commit (serializeNE Commit.mf (← extractCommit authenticatedCommitPub))
  checkEqual "commit_priv" bytesToHexString commit (serializeNE Commit.mf (← extractCommit authenticatedCommitPriv))

/-! ## Application test -/

/-- Port of `extract_application`. -/
@[expose]
public
def extractApplication (content: AuthenticatedContent ByteArray): IO ByteArray :=
  match content.content.content with
  | { contentType := .application, content := a } => pure a.val
  | _ => throw (IO.userError "extract_application: not a application")

/-- Port of `test_application_protection`. -/
@[expose]
public
def testApplicationProtection (t: MessageProtectionTest): IO Unit := do
  let application ← hexStringToBytes t.application
  let authenticatedApplicationPriv ← unprotectPrivateMessage t.applicationPriv t
  checkSignature authenticatedApplicationPriv t
  checkPrivateMessageRoundtrip authenticatedApplicationPriv.content t
  checkEqual "application_priv" bytesToHexString application (← extractApplication authenticatedApplicationPriv)

end CryptoBytes

/-! ## Boilerplate -/

/-- Port of `test_message_protection_one`. -/
@[expose]
public
def testMessageProtectionOne (t: MessageProtectionTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    testProposalProtection t
    testCommitProtection t
    testApplicationProtection t
    pure true

/-- Port of `test_message_protection`. -/
@[expose]
public
def testMessageProtection: List MessageProtectionTest → IO Nat :=
  testList "Message Protection" testMessageProtectionOne

end MLS.Test.FromExt.MessageProtection
