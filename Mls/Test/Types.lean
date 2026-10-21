/-!
Port of `MLS.Test.Types` (the parts needed by the ported tests).
-/

namespace Mls.Test

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
  | messages

inductive Testsuite where
  | cryptoBasicsTest: List CryptoBasicsTest → Testsuite
  | messagesTest: List MessagesTest → Testsuite

end Mls.Test
