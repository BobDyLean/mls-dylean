import Lake
open Lake DSL

package mls

require dylean from git "https://github.com/BobDyLean/dylean" @ "v4.36.0-rc1"

/-! ## OpenSSL bindings (`OpenSSL/`) -/

target opensslLeanO pkg : System.FilePath := do
  let srcJob ← inputTextFile <| pkg.dir / "OpenSSL" / "c" / "openssl_lean.c"
  let oFile := pkg.buildDir / "c" / "openssl_lean.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

target opensslLean pkg : System.FilePath := do
  let o ← opensslLeanO.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "opensslLean") #[o]

@[default_target]
lean_lib OpenSSL where
  srcDir := "OpenSSL"
  moreLinkObjs := #[opensslLean]
  moreLinkArgs := #["-lcrypto"]

/-! ## DY* compatibility layer for DyLean (`DySlop/`) -/

@[default_target]
lean_lib DySlop

/-! ## MLS -/

@[default_target]
lean_lib MLS

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

target cryptoBasicsTestVector pkg : System.FilePath :=
  fetchTestVector pkg "crypto-basics"

target treeValidationTestVector pkg : System.FilePath :=
  fetchTestVector pkg "tree-validation"

target treeOperationsTestVector pkg : System.FilePath :=
  fetchTestVector pkg "tree-operations"

target messagesTestVector pkg : System.FilePath :=
  fetchTestVector pkg "messages"

target treekemTestVector pkg : System.FilePath :=
  fetchTestVector pkg "treekem"

target keyScheduleTestVector pkg : System.FilePath :=
  fetchTestVector pkg "key-schedule"

target pskSecretTestVector pkg : System.FilePath :=
  fetchTestVector pkg "psk_secret"

target welcomeTestVector pkg : System.FilePath :=
  fetchTestVector pkg "welcome"

target secretTreeTestVector pkg : System.FilePath :=
  fetchTestVector pkg "secret-tree"

target messageProtectionTestVector pkg : System.FilePath :=
  fetchTestVector pkg "message-protection"

target transcriptHashesTestVector pkg : System.FilePath :=
  fetchTestVector pkg "transcript-hashes"

@[test_driver]
lean_exe «mls-test» where
  root := `TestMain
  needs := #[cryptoBasicsTestVector, treeValidationTestVector, treeOperationsTestVector, messagesTestVector, treekemTestVector, keyScheduleTestVector, pskSecretTestVector, welcomeTestVector,
    secretTreeTestVector, messageProtectionTestVector, transcriptHashesTestVector]
