import Mls.Test.Types
import Mls.Test.Reader
import Mls.Test.Utils
import Mls.Test.FromExt.Messages

/-!
Port of `MLS.Test`.

The test vectors are read from `<root>/test_vectors/data/`,
where `<root>` defaults to the current directory.
They are downloaded by Lake (target `messagesTestVector` in `lakefile.lean`) before building `mls-test`.
-/

namespace Mls.Test

open Mls.Test.FromExt.Messages

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

def runMessagesTests (testVectorsDir: System.FilePath): IO Unit :=
  runTests testVectorsDir "Messages" .messages (fun | .messagesTest l => some l) testMessages

def main (testVectorsDir: System.FilePath): IO Unit := do
  runMessagesTests testVectorsDir

end Mls.Test
