module

public import MLS.Test.Types
public import MLS.Test.Reader
public import MLS.Test.Utils
public import MLS.Test.FromExt.CryptoBasics
public import MLS.Test.FromExt.Messages
public import MLS.Test.FromExt.TreeValidation
public import MLS.Test.FromExt.TreeOperations
public import MLS.Test.FromExt.TreeKEM
public import MLS.Test.FromExt.KeySchedule
public import MLS.Test.FromExt.PreSharedKeys
public import MLS.Test.FromExt.Welcome
public import MLS.Test.FromExt.SecretTree
public import MLS.Test.FromExt.MessageProtection
public import MLS.Test.FromExt.TranscriptHashes
public import OpenSSL.Test

/-!
Port of `MLS.Test`.

The test vectors are read from `<root>/test_vectors/data/`,
where `<root>` defaults to the current directory.
They are downloaded by Lake (targets `*TestVector` in `lakefile.lean`) before building `mls-test`.
-/

namespace MLS.Test

open MLS.Test.FromExt.CryptoBasics
open MLS.Test.FromExt.Messages
open MLS.Test.FromExt.TreeValidation
open MLS.Test.FromExt.TreeOperations
open MLS.Test.FromExt.TreeKEM
open MLS.Test.FromExt.KeySchedule
open MLS.Test.FromExt.PreSharedKeys
open MLS.Test.FromExt.Welcome
open MLS.Test.FromExt.SecretTree
open MLS.Test.FromExt.MessageProtection
open MLS.Test.FromExt.TranscriptHashes

/-- Port of `run_tests`. -/
public
def runTests {a: Type} (testVectorsDir: System.FilePath) (name: String) (ty: TestType)
  (extractTestsuite: Testsuite → Option (List a)) (runTest: List a → IO Nat)
  : IO Unit := do
  let testsuite ← getTestsuite testVectorsDir ty
  match extractTestsuite testsuite with
  | none => throw (IO.userError s!"{name}: failed to read tests")
  | some testsuite =>
    IO.println s!"{name}: running tests..."
    let nRun ← runTest testsuite
    IO.println s!"{name}: success! ({nRun}/{testsuite.length})"

/-- Port of `run_crypto_basics_tests`. -/
public
def runCryptoBasicsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Crypto Basics" .cryptoBasics (fun | .cryptoBasicsTest l => some l | _ => none) testCryptoBasics

/-- Port of `run_tree_validation_tests`. -/
public
def runTreeValidationTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Validation" .treeValidation (fun | .treeValidationTest l => some l | _ => none) testTreeValidation

/-- Port of `run_tree_operations_tests`. -/
public
def runTreeOperationsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Operations" .treeOperations (fun | .treeOperationsTest l => some l | _ => none) testTreeOperations

/-- Port of `run_secret_tree_tests`. -/
public
def runSecretTreeTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Secret Tree" .secretTree (fun | .secretTreeTest l => some l | _ => none) testSecretTree

/-- Port of `run_message_protection_tests`. -/
public
def runMessageProtectionTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Message Protection" .messageProtection (fun | .messageProtectionTest l => some l | _ => none) testMessageProtection

/-- Port of `run_transcript_hashes_tests`. -/
public
def runTranscriptHashesTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Transcript Hashes" .transcriptHashes (fun | .transcriptHashesTest l => some l | _ => none) testTranscriptHashes

/-- Port of `run_keyschedule_tests`. -/
public
def runKeyscheduleTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Key Schedule" .keySchedule (fun | .keyScheduleTest l => some l | _ => none) testKeyschedule

/-- Port of `run_psk_tests`. -/
public
def runPskTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Pre-Shared Keys" .preSharedKeys (fun | .preSharedKeysTest l => some l | _ => none) testPsk

/-- Port of `run_welcome_tests`. -/
public
def runWelcomeTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Welcome" .welcome (fun | .welcomeTest l => some l | _ => none) testWelcome

/-- Port of `run_treekem_tests`. -/
public
def runTreekemTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "TreeKEM" .treekem (fun | .treekemTest l => some l | _ => none) testTreekem

/-- Port of `run_messages_tests`. -/
public
def runMessagesTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Messages" .messages (fun | .messagesTest l => some l | _ => none) testMessages

/-- Port of `main`. -/
public
def main (testVectorsDir: System.FilePath): IO Unit := do
  OpenSSL.Test.main
  runCryptoBasicsTests testVectorsDir
  runSecretTreeTests testVectorsDir
  runMessageProtectionTests testVectorsDir
  runKeyscheduleTests testVectorsDir
  runPskTests testVectorsDir
  runTranscriptHashesTests testVectorsDir
  runWelcomeTests testVectorsDir
  runTreeValidationTests testVectorsDir
  runTreeOperationsTests testVectorsDir
  runTreekemTests testVectorsDir
  runMessagesTests testVectorsDir

end MLS.Test
