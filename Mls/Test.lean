import Mls.Test.Types
import Mls.Test.Reader
import Mls.Test.Utils
import Mls.Test.FromExt.CryptoBasics
import Mls.Test.FromExt.Messages
import Mls.Test.FromExt.TreeValidation
import Mls.Test.FromExt.TreeOperations
import OpenSSL.Test

/-!
Port of `MLS.Test`.

The test vectors are read from `<root>/test_vectors/data/`,
where `<root>` defaults to the current directory.
They are downloaded by Lake (targets `*TestVector` in `lakefile.lean`) before building `mls-test`.
-/

namespace Mls.Test

open Mls.Test.FromExt.CryptoBasics
open Mls.Test.FromExt.Messages
open Mls.Test.FromExt.TreeValidation
open Mls.Test.FromExt.TreeOperations

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

def runCryptoBasicsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Crypto Basics" .cryptoBasics (fun | .cryptoBasicsTest l => some l | _ => none) testCryptoBasics

def runTreeValidationTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Validation" .treeValidation (fun | .treeValidationTest l => some l | _ => none) testTreeValidation

def runTreeOperationsTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Tree Operations" .treeOperations (fun | .treeOperationsTest l => some l | _ => none) testTreeOperations

def runMessagesTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Messages" .messages (fun | .messagesTest l => some l | _ => none) testMessages

def main (testVectorsDir: System.FilePath): IO Unit := do
  OpenSSL.Test.main
  runCryptoBasicsTests testVectorsDir
  runTreeValidationTests testVectorsDir
  runTreeOperationsTests testVectorsDir
  runMessagesTests testVectorsDir

end Mls.Test
