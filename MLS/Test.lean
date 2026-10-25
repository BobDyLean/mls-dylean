import MLS.Test.Types
import MLS.Test.Reader
import MLS.Test.Utils
import MLS.Test.FromExt.CryptoBasics
import MLS.Test.FromExt.Messages
import MLS.Test.FromExt.TreeValidation
import MLS.Test.FromExt.TreeOperations
import MLS.Test.FromExt.TreeKEM
import MLS.Test.FromExt.KeySchedule
import MLS.Test.FromExt.PreSharedKeys
import MLS.Test.FromExt.Welcome
import OpenSSL.Test

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

/-- Port of `run_tests`. -/
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
def runCryptoBasicsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Crypto Basics" .cryptoBasics (fun | .cryptoBasicsTest l => some l | _ => none) testCryptoBasics

/-- Port of `run_tree_validation_tests`. -/
def runTreeValidationTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Validation" .treeValidation (fun | .treeValidationTest l => some l | _ => none) testTreeValidation

/-- Port of `run_tree_operations_tests`. -/
def runTreeOperationsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Operations" .treeOperations (fun | .treeOperationsTest l => some l | _ => none) testTreeOperations

/-- Port of `run_keyschedule_tests`. -/
def runKeyscheduleTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Key Schedule" .keySchedule (fun | .keyScheduleTest l => some l | _ => none) testKeyschedule

/-- Port of `run_psk_tests`. -/
def runPskTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Pre-Shared Keys" .preSharedKeys (fun | .preSharedKeysTest l => some l | _ => none) testPsk

/-- Port of `run_welcome_tests`. -/
def runWelcomeTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Welcome" .welcome (fun | .welcomeTest l => some l | _ => none) testWelcome

/-- Port of `run_treekem_tests`. -/
def runTreekemTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "TreeKEM" .treekem (fun | .treekemTest l => some l | _ => none) testTreekem

/-- Port of `run_messages_tests`. -/
def runMessagesTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Messages" .messages (fun | .messagesTest l => some l | _ => none) testMessages

/-- Port of `main`. -/
def main (testVectorsDir: System.FilePath): IO Unit := do
  OpenSSL.Test.main
  runCryptoBasicsTests testVectorsDir
  runKeyscheduleTests testVectorsDir
  runPskTests testVectorsDir
  runWelcomeTests testVectorsDir
  runTreeValidationTests testVectorsDir
  runTreeOperationsTests testVectorsDir
  runTreekemTests testVectorsDir
  runMessagesTests testVectorsDir

end MLS.Test
