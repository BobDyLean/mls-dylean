module

/-!
Port of `MLS.Test.Types` (the parts needed by the ported tests).
-/

namespace MLS.Test

/-! ## Crypto Basics -/

public
structure CryptoBasicsRefHash where
  label: String
  value: String
  out: String

public
structure CryptoBasicsExpandWithLabel where
  secret: String
  label: String
  context: String
  length: UInt16
  out: String

public
structure CryptoBasicsDeriveSecret where
  secret: String
  label: String
  out: String

public
structure CryptoBasicsDeriveTreeSecret where
  secret: String
  label: String
  generation: UInt32
  length: UInt16
  out: String

public
structure CryptoBasicsSignWithLabel where
  priv: String
  pub: String
  content: String
  label: String
  signature: String

public
structure CryptoBasicsEncryptWithLabel where
  priv: String
  pub: String
  label: String
  context: String
  plaintext: String
  kemOutput: String
  ciphertext: String

public
structure CryptoBasicsTest where
  cipherSuite: UInt16
  refHash: CryptoBasicsRefHash
  expandWithLabel: CryptoBasicsExpandWithLabel
  deriveSecret: CryptoBasicsDeriveSecret
  deriveTreeSecret: CryptoBasicsDeriveTreeSecret
  signWithLabel: CryptoBasicsSignWithLabel
  encryptWithLabel: CryptoBasicsEncryptWithLabel

/-! ## Tree Validation -/

public
structure TreeValidationTest where
  cipherSuite: UInt16
  tree: String
  groupId: String
  resolutions: List (List UInt32)
  treeHashes: List String

/-! ## Tree Operations -/

public
structure TreeOperationsTest where
  treeBefore: String
  proposal: String
  proposalSender: UInt32
  treeAfter: String

/-! ## Secret Tree -/

public
structure SecretTreeSenderData where
  senderDataSecret: String
  ciphertext: String
  key: String
  nonce: String

public
structure SecretTreeLeaf where
  generation: UInt32
  handshakeKey: String
  handshakeNonce: String
  applicationKey: String
  applicationNonce: String

public
structure SecretTreeTest where
  cipherSuite: UInt16
  senderData: SecretTreeSenderData
  encryptionSecret: String
  leaves: List (List SecretTreeLeaf)

/-! ## Message Protection -/

public
structure MessageProtectionTest where
  cipherSuite: UInt16

  groupId: String
  epoch: UInt64
  treeHash: String
  confirmedTranscriptHash: String

  signaturePriv: String
  signaturePub: String

  encryptionSecret: String
  senderDataSecret: String
  membershipKey: String

  proposal: String
  proposalPub: String
  proposalPriv: String

  commit: String
  commitPub: String
  commitPriv: String

  application: String
  applicationPriv: String

/-! ## Key Schedule -/

public
structure KeyscheduleTestEpochInput where
  treeHash: String
  commitSecret: String
  pskSecret: String
  confirmedTranscriptHash: String
  exporterLabel: String
  exporterContext: String
  exporterLength: UInt32

public
structure KeyscheduleTestEpochOutput where
  groupContext: String

  joinerSecret: String
  welcomeSecret: String
  initSecret: String

  senderDataSecret: String
  encryptionSecret: String
  exporterSecret: String
  epochAuthenticator: String
  externalSecret: String
  confirmationKey: String
  membershipKey: String
  resumptionPsk: String

  externalPub: String
  exportedSecret: String

public
structure KeyscheduleTest where
  cipherSuite: UInt16
  groupId: String
  initialInitSecret: String
  epochs: List (KeyscheduleTestEpochInput × KeyscheduleTestEpochOutput)

/-! ## Pre-Shared Keys -/

public
structure PskTestPsk where
  pskId: String
  psk: String
  pskNonce: String

public
structure PskTest where
  cipherSuite: UInt16
  psks: List PskTestPsk
  pskSecret: String

/-! ## Transcript Hashes -/

public
structure TranscriptHashesTest where
  cipherSuite: UInt16

  confirmationKey: String
  authenticatedContent: String
  interimTranscriptHashBefore: String

  confirmedTranscriptHashAfter: String
  interimTranscriptHashAfter: String

/-! ## Welcome -/

public
structure WelcomeTest where
  cipherSuite: UInt16
  initPriv: String
  signerPub: String
  keyPackage: String
  welcome: String

/-! ## TreeKEM -/

public
structure TreeKEMLeafPathSecret where
  node: UInt32
  pathSecret: String

public
structure TreeKEMLeafPrivate where
  index: UInt32
  encryptionPriv: String
  signaturePriv: String
  pathSecrets: List TreeKEMLeafPathSecret

public
structure TreeKEMUpdatePath where
  sender: UInt32
  updatePath: String
  pathSecrets: List (Option String)
  commitSecret: String
  treeHashAfter: String

public
structure TreeKEMTest where
  cipherSuite: UInt16
  groupId: String
  epoch: UInt64
  confirmedTranscriptHash: String
  ratchetTree: String
  leavesPrivate: List TreeKEMLeafPrivate
  updatePaths: List TreeKEMUpdatePath

/-! ## Messages -/

public
structure MessagesTest where
  mlsWelcome: String
  mlsGroupInfo: String
  mlsKeyPackage: String

  ratchetTree: String
  groupSecrets: String

  addProposal: String
  updateProposal: String
  removeProposal: String
  preSharedKeyProposal: String
  reInitProposal: String
  externalInitProposal: String
  groupContextExtensionsProposal: String

  commit: String

  publicMessageApplication: String
  publicMessageProposal: String
  publicMessageCommit: String
  privateMessage: String

public
inductive TestType where
  | cryptoBasics
  | treeValidation
  | treeOperations
  | secretTree
  | messageProtection
  | keySchedule
  | preSharedKeys
  | transcriptHashes
  | welcome
  | treekem
  | messages

public
inductive Testsuite where
  | cryptoBasicsTest: List CryptoBasicsTest → Testsuite
  | treeValidationTest: List TreeValidationTest → Testsuite
  | treeOperationsTest: List TreeOperationsTest → Testsuite
  | secretTreeTest: List SecretTreeTest → Testsuite
  | messageProtectionTest: List MessageProtectionTest → Testsuite
  | keyScheduleTest: List KeyscheduleTest → Testsuite
  | preSharedKeysTest: List PskTest → Testsuite
  | transcriptHashesTest: List TranscriptHashesTest → Testsuite
  | welcomeTest: List WelcomeTest → Testsuite
  | treekemTest: List TreeKEMTest → Testsuite
  | messagesTest: List MessagesTest → Testsuite

end MLS.Test
