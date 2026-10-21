import Lake
open Lake DSL

package mls

require dylean from git "https://github.com/BobDyLean/dylean" @ "v4.36.0-rc1"

@[default_target]
lean_lib Mls

@[default_target]
lean_exe mls where
  root := `Main

/-! ## Test vectors -/

/-- Commit of https://github.com/mlswg/mls-implementations from which the test vectors are fetched. -/
def testVectorsCommit := "f07090a844ebece12c064ce94ab853fd477db12f"

/-- Download `test_vectors/data/<name>.json`, unless it is up to date. -/
def fetchTestVector (pkg: Package) (name: String): FetchM (Job System.FilePath) := Job.async do
  let file := pkg.dir / "test_vectors" / "data" / s!"{name}.json"
  addPureTrace testVectorsCommit "commit"
  buildFileUnlessUpToDate' file (text := true) do
    download s!"https://raw.githubusercontent.com/mlswg/mls-implementations/{testVectorsCommit}/test-vectors/{name}.json" file
  return file

target messagesTestVector pkg : System.FilePath :=
  fetchTestVector pkg "messages"

@[test_driver]
lean_exe «mls-test» where
  root := `TestMain
  needs := #[messagesTestVector]
