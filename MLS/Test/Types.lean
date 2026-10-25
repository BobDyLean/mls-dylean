/-!
Port of `MLS.Test.Types` (the parts needed by the ported tests).
-/

namespace MLS.Test

/-! ## Crypto Basics -/

structure CryptoBasicsRefHash where
  label: String
  value: String
  out: String

structure CryptoBasicsExpandWithLabel where
  secret: String
  label: String
  context: String
  length: UInt16
  out: String

structure CryptoBasicsDeriveSecret where
  secret: String
  label: String
  out: String

structure CryptoBasicsDeriveTreeSecret where
  secret: String
  label: String
  generation: UInt32
  length: UInt16
  out: String

structure CryptoBasicsSignWithLabel where
  priv: String
  pub: String
  content: String
  label: String
  signature: String

structure CryptoBasicsEncryptWithLabel where
  priv: String
  pub: String
  label: String
  context: String
  plaintext: String
  kemOutput: String
  ciphertext: String

structure CryptoBasicsTest where
  cipherSuite: UInt16
  refHash: CryptoBasicsRefHash
  expandWithLabel: CryptoBasicsExpandWithLabel
  deriveSecret: CryptoBasicsDeriveSecret
  deriveTreeSecret: CryptoBasicsDeriveTreeSecret
  signWithLabel: CryptoBasicsSignWithLabel
  encryptWithLabel: CryptoBasicsEncryptWithLabel

/-! ## Tree Validation -/

structure TreeValidationTest where
  cipherSuite: UInt16
  tree: String
  groupId: String
  resolutions: List (List UInt32)
  treeHashes: List String

/-! ## Tree Operations -/

structure TreeOperationsTest where
  treeBefore: String
  proposal: String
  proposalSender: UInt32
  treeAfter: String

/-! ## Key Schedule -/

structure KeyscheduleTestEpochInput where
  treeHash: String
  commitSecret: String
  pskSecret: String
  confirmedTranscriptHash: String
  exporterLabel: String
  exporterContext: String
  exporterLength: UInt32

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

structure KeyscheduleTest where
  cipherSuite: UInt16
  groupId: String
  initialInitSecret: String
  epochs: List (KeyscheduleTestEpochInput × KeyscheduleTestEpochOutput)

/-! ## Pre-Shared Keys -/

structure PskTestPsk where
  pskId: String
  psk: String
  pskNonce: String

structure PskTest where
  cipherSuite: UInt16
  psks: List PskTestPsk
  pskSecret: String

/-! ## TreeKEM -/

structure TreeKEMLeafPathSecret where
  node: UInt32
  pathSecret: String

structure TreeKEMLeafPrivate where
  index: UInt32
  encryptionPriv: String
  signaturePriv: String
  pathSecrets: List TreeKEMLeafPathSecret

structure TreeKEMUpdatePath where
  sender: UInt32
  updatePath: String
  pathSecrets: List (Option String)
  commitSecret: String
  treeHashAfter: String

structure TreeKEMTest where
  cipherSuite: UInt16
  groupId: String
  epoch: UInt64
  confirmedTranscriptHash: String
  ratchetTree: String
  leavesPrivate: List TreeKEMLeafPrivate
  updatePaths: List TreeKEMUpdatePath

/-! ## Messages -/

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

inductive TestType where
  | cryptoBasics
  | treeValidation
  | treeOperations
  | keySchedule
  | preSharedKeys
  | treekem
  | messages

inductive Testsuite where
  | cryptoBasicsTest: List CryptoBasicsTest → Testsuite
  | treeValidationTest: List TreeValidationTest → Testsuite
  | treeOperationsTest: List TreeOperationsTest → Testsuite
  | keyScheduleTest: List KeyscheduleTest → Testsuite
  | preSharedKeysTest: List PskTest → Testsuite
  | treekemTest: List TreeKEMTest → Testsuite
  | messagesTest: List MessagesTest → Testsuite

end MLS.Test
