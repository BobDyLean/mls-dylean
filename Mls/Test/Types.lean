/-!
Port of `MLS.Test.Types` (the parts needed by the ported tests).
-/

namespace Mls.Test

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
  | messages

inductive Testsuite where
  | messagesTest: List MessagesTest → Testsuite

end Mls.Test
