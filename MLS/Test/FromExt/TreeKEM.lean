import MLS.TreeSync.Code.Operations
import MLS.TreeSync.Code.TreeHash
import MLS.TreeKEM.Code.API.Tree
import MLS.Glue.Code.NetworkBinder
import MLS.Glue.Code.TreeSyncTreeKEMBinder
import MLS.Test.FromExt.CryptoBasics
import MLS.Test.Types
import MLS.Test.Utils

/-!
Port of `MLS.Test.FromExt.TreeKEM`.

Port-specific differences:
- `level` (from `MLS.TreeMath.Internal`, which is not ported yet) is defined here.
- The `assume`s of MLS* on the TreeKEM invariants are not needed, as these invariants are not ported.
- When MLS* uses `l = st.state.levels` to typecheck, the trees and paths are cast with this equality.
- The cipher suite P-521 (not supported by MLS*) is skipped: see `testTreekemOne`.
-/

namespace MLS.Test.FromExt.TreeKEM

open Comparse
open MLS MLS.TreeSync MLS.TreeKEM
open MLS.Test
open MLS.Test.FromExt.CryptoBasics

/--
Port of `MLS.TreeMath.Internal.level`.
The level of a node index (in the array representation of the tree): its number of trailing ones.
-/
def level (x: Nat): Nat :=
  if x % 2 = 1 then level (x / 2) + 1 else 0

/-- Port of `participant_state`. -/
structure ParticipantState where
  leafInd: Nat
  state: TreeKEMTreeState ByteArray leafInd
  signatureKey: ByteArray

/-- Port of `List.nth` (from `FStar.List`), which fails when the index is too big. -/
def listNth {α: Type} (l: List α) (n: Nat): IO α :=
  match l[n]? with
  | some x => pure x
  | none => throw (IO.userError "nth: index too big")

/-- Cast a TreeKEM state of `l` levels. -/
def getLevels {leafInd: Nat} (st: TreeKEMTreeState ByteArray leafInd) (l: Nat) (name: String): IO (PLift (st.levels = l)) :=
  if h: st.levels = l then pure ⟨h⟩
  else throw (IO.userError s!"{name}: bad levels")

section CryptoBytes

variable [CryptoBytes ByteArray]

/-- Port of `set_path_secret`. -/
def setPathSecret {l: Nat} (pathSecret: ByteArray) (height: Nat) (t: TreeKEM ByteArray l) (li: Nat)
  (p: TreeKEMPriv ByteArray l) : IO (TreeKEMPriv ByteArray l)
:=
  if height > l then
    throw (IO.userError "set_path_secret: bad height")
  else
    match l, t.intoChildSiblingView li, p with
    | _, .leaf _ _, .leaf _ => throw (IO.userError "set_path_secret: height = 0")
    | l+1, .node content child _, .node priv pNext =>
      if height = l+1 then do
        let (sk, pk) ← extractResult (deriveKeypairFromPathSecret pathSecret)
        if !(content.map (·.publicKey) == some pk) then
          throw (IO.userError "set_path_secret: bad public key")
        else
          pure (.node (some sk) pNext)
      else do
        pure (.node priv (← setPathSecret pathSecret height child li pNext))

/-- Port of `get_leaf_treekem_tree_state`. -/
def getLeafTreekemTreeState {l: Nat} (tree: TreeKEM ByteArray l) (leafPriv: TreeKEMLeafPrivate): IO ParticipantState := do
  let leafInd := leafPriv.index.toNat
  if !(leafInd < 2^l) then throw (IO.userError "get_leaf_treekem_tree_state: leaf_ind too big")
  let encryptionPriv ← extractResult (mkHpkePrivateKey (← hexStringToBytes leafPriv.encryptionPriv) "get_leaf_treekem_tree_state" "encryption_priv")
  let priv ← leafPriv.pathSecrets.foldrM
    (fun pathSecret priv => do setPathSecret (← hexStringToBytes pathSecret.pathSecret) (level pathSecret.node.toNat) tree leafInd priv)
    (createEmptyPriv encryptionPriv)
  pure {
    leafInd
    state := {
      levels := l
      tree
      priv
    }
    signatureKey := ← hexStringToBytes leafPriv.signaturePriv
  }

/-- Port of `check_one_update_path`. -/
def checkOneUpdatePath {l: Nat} (groupContext: GroupContext ByteArray) (_tsync: TreeSync ByteArray tkt l)
  (li: Nat) (treekemPath: PathKEM ByteArray l) (expectedCommitSecret: ByteArray) (expectedOptPathSecrets: List (Option String))
  (st: ParticipantState)
  : IO Unit
:= do
  if li = st.leafInd then
    if (← listNth expectedOptPathSecrets st.leafInd).isSome then
      throw (IO.userError "check_one_update_path: path_secret should be null")
  else
    let expectedOptPathSecret ← listNth expectedOptPathSecrets st.leafInd
    let ⟨h⟩ ← getLevels st.state l "check_one_update_path"
    let tree: TreeKEM ByteArray l := h ▸ st.state.tree
    let priv: TreeKEMPriv ByteArray l := h ▸ st.state.priv
    let some expectedPathSecret := expectedOptPathSecret
      | throw (IO.userError "check_one_update_path: path_secret should be non-null")
    if !checkUpdatePathCiphertextsLengthes tree li treekemPath then
      throw (IO.userError "check_one_update_path: bad ciphertext lengthes")
    let expectedPathSecret ← hexStringToBytes expectedPathSecret
    let (pathSecret, leastCommonAncestorLevel) ← extractResult (getPathSecret tree st.leafInd li priv treekemPath groupContext)
    let newTree := treeApplyPath tree li treekemPath
    let (_, commitSecret) ← extractResult (pathApplyPath newTree st.leafInd priv pathSecret leastCommonAncestorLevel)
    checkEqual "path_secret" bytesToHexString expectedPathSecret pathSecret
    checkEqual "commit_secret" bytesToHexString expectedCommitSecret commitSecret

/-- Port of `check_update_path`. -/
def checkUpdatePath {l: Nat} (groupContext: GroupContext ByteArray) (tsync: TreeSync ByteArray tkt l)
  (treekemTreeStates: List ParticipantState) (t: TreeKEMUpdatePath)
  : IO Unit
:= do
  let sender := t.sender.toNat
  let commitSecret ← hexStringToBytes t.commitSecret
  if !(sender < 2^l) then throw (IO.userError "check_update_path: sender too big")
  -- `parse` is specialized to `bytesLikeByteArray`: use the `BytesLike` structure of the `CryptoBytes` instance.
  let some updatePath := UpdatePath.mf.toExtensible.parse (← hexStringToBytes t.updatePath)
    | throw (IO.userError "update_path: parse failed")
  let uncompressedPath ← extractResult (uncompressUpdatePath sender tsync updatePath)
  let treesyncPath := updatePathToTreesync uncompressedPath
  let treekemPath := updatePathToTreekem uncompressedPath
  let tsyncAfter ← extractResult (TreeSync.applyPath tsync sender treesyncPath)
  let treeHashAfter ← extractResult (mkMlsBytes (← extractResult (treeHash tsyncAfter)) "check_update_path" "tree_hash_after")
  let groupContext := { groupContext with treeHash := treeHashAfter }
  if !TreeSync.pathIsValid groupContext.groupId tsync sender treesyncPath then
    throw (IO.userError "check_update_path: invalid path")
  treekemTreeStates.forM (checkOneUpdatePath groupContext tsync sender treekemPath commitSecret t.pathSecrets)
  for (i, optPathSecret) in (List.range t.pathSecrets.length).zip t.pathSecrets do
    if !(i < 2^l) then throw (IO.userError "check_update_path: bad i")
    if !((i = sender || (leafAt tsync i).isNone) == optPathSecret.isNone) then
      throw (IO.userError "check_update_path: incoherent null path secret")
  checkEqual "tree_hash_after" bytesToHexString (← hexStringToBytes t.treeHashAfter) treeHashAfter.val

/-- Port of `generate_my_update_path`. -/
def generateMyUpdatePath {l: Nat} (groupContext: GroupContext ByteArray) (tsync: TreeSync ByteArray tkt l)
  (st: ParticipantState)
  : IO (UpdatePath ByteArray × ByteArray)
:= do
  if !(st.leafInd < 2^l) then throw (IO.userError "generate_my_update_path: leaf_ind too big")
  let ⟨h⟩ ← getLevels st.state l "generate_my_update_path"
  let tsync: TreeSync ByteArray tkt st.state.levels := h ▸ tsync
  let rand := initRandState st.leafInd
  let (rand, prepareCreateCommitRand) := genRandRandomness rand (API.Tree.prepareCreateCommitEntropyLengths ByteArray)
  let (rand, signNonce) := genRandBytes rand (CryptoBytes.signSignMinEntropyLength ByteArray)
  let signatureKey := st.signatureKey
  let (pendingCreateCommit, preUpdatePath) ← extractResult (API.Tree.prepareCreateCommit st.state prepareCreateCommitRand)
  let updatePathSync ← extractResult (do
    let myNewLeafPackageData ← do
      let optMyLeafPackage := leafAt tsync st.leafInd
      let myLeafPackage ← Result.fromOption "generate_update_path: my leaf is blanked" optMyLeafPackage
      pure ({
        myLeafPackage.data with
        source := .update
        lifetime := ()
        parentHash := ()
      }: LeafNodeData ByteArray tkt)
    let extUpdatePath ← treekemToTreesync myNewLeafPackageData preUpdatePath
    if !(extUpdatePath.getPathLeaf.source == .update) then Result.error "" else
    TreeSync.externalPathToPath tsync st.leafInd extUpdatePath groupContext.groupId signatureKey signNonce
  )
  let (_, finalizeCreateCommitRand) := genRandRandomness rand (API.Tree.finalizeCreateCommitEntropyLengths st.state [])
  let createCommitResult ← extractResult (API.Tree.finalizeCreateCommit pendingCreateCommit [] groupContext finalizeCreateCommitRand)
  let uncompressedUpdatePath := mlsStarPathsToUpdatePath updatePathSync createCommitResult.updatePath
  pure (← extractResult (compressUpdatePath uncompressedUpdatePath), createCommitResult.commitSecret)

/-- Port of `check_one_my_update_path`. -/
def checkOneMyUpdatePath {l: Nat} (groupContext: GroupContext ByteArray) (tsync: TreeSync ByteArray tkt l)
  (st: ParticipantState) (sender: Nat) (updatePath: UpdatePath ByteArray) (expectedCommitSecret: ByteArray)
  : IO Unit
:= do
  if !(sender < 2^l) then throw (IO.userError "check_one_my_update_path: sender too big")
  let ⟨h⟩ ← getLevels st.state l "check_one_my_update_path"
  let tsync: TreeSync ByteArray tkt st.state.levels := h ▸ tsync
  if sender = st.leafInd then pure () else
    let uncompressedPath ← extractResult (uncompressUpdatePath sender tsync updatePath)
    let treesyncPath := updatePathToTreesync uncompressedPath
    let treekemPath := updatePathToTreekem uncompressedPath
    if !TreeSync.pathIsValid groupContext.groupId tsync sender treesyncPath then
      throw (IO.userError "check_one_my_update_path: invalid path")
    let (_, commitSecret) ← extractResult (API.Tree.commit st.state sender treekemPath [] groupContext)
    checkEqual "commit_secret" bytesToHexString expectedCommitSecret commitSecret

/-- Port of `check_my_update_path`. -/
def checkMyUpdatePath {l: Nat} (groupContext: GroupContext ByteArray) (tsync: TreeSync ByteArray tkt l)
  (states: List ParticipantState)
  : IO Unit
:=
  states.forM fun stGen => do
    let (updatePath, expectedCommitSecret) ← generateMyUpdatePath groupContext tsync stGen
    states.forM fun stProcess =>
      checkOneMyUpdatePath groupContext tsync stProcess stGen.leafInd updatePath expectedCommitSecret

end CryptoBytes

/-- Port of `test_treekem_one`. -/
def testTreekemOne (t: TreeKEMTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success .mls_256_dhkemp521_aes256gcm_sha512_p521 =>
    -- Unsupported: OpenSSL's `DeriveKeyPair` requires `Nsk` (66) bytes of `ikm`,
    -- but path secrets have `Nh` (64) bytes (MLS*'s `hpke_ikm` has the same requirement).
    pure false
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    let some ratchetTree := parse (RatchetTree.mf tkt) (← hexStringToBytes t.ratchetTree)
      | throw (IO.userError "ratchet_tree: parse failed")
    let ⟨_, tsync⟩ ← extractResult (ratchetTreeToTreesync ratchetTree)
    let tkem := treesyncToTreekem tsync
    let treeHash ← extractResult (treeHash tsync)
    let groupContext ← genGroupContext (CryptoBytes.ciphersuite ByteArray) (← hexStringToBytes t.groupId) t.epoch.toNat treeHash (← hexStringToBytes t.confirmedTranscriptHash)
    let states ← t.leavesPrivate.mapM (getLeafTreekemTreeState tkem)
    t.updatePaths.forM (checkUpdatePath groupContext tsync states)
    checkMyUpdatePath groupContext tsync states
    pure true

/-- Port of `test_treekem`. -/
def testTreekem: List TreeKEMTest → IO Nat :=
  testList "TreeKEM" testTreekemOne

end MLS.Test.FromExt.TreeKEM
