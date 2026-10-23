import Mls.TreeSync.TreeHash
import Mls.TreeSync.Invariants.ValidLeaves
import Mls.TreeSync.Invariants.UnmergedLeaves
import Mls.TreeSync.Invariants.ParentHash
import Mls.TreeKEM.NetworkTypes
import Mls.Glue.NetworkBinder
import Mls.Test.FromExt.CryptoBasics
import Mls.Test.Types
import Mls.Test.Utils

/-!
Port of `MLS.Test.FromExt.TreeValidation`.

Port-specific differences:
- `node_index_to_node_index` uses the closed formula `2*i + 2^l - 1`
  instead of `MLS.TreeMath.Internal.parent`, which is not ported yet.
-/

namespace Mls.Test.FromExt.TreeValidation

open Comparse
open Mls Mls.TreeSync Mls.TreeKEM
open Mls.Test
open Mls.Test.FromExt.CryptoBasics

/-- Port of `compute_tree_hashes`. -/
def computeTreeHashes [CryptoBytes ByteArray] {l: Nat} (t: TreeSync ByteArray tkt l): IO (List ByteArray) :=
  match t.intoLeftRightView with
  | .leaf _ _ => do
    pure [← extractResult (treeHash t)]
  | .node _ left right => do
    let myHash ← extractResult (treeHash t)
    pure ((← computeTreeHashes left) ++ [myHash] ++ (← computeTreeHashes right))

/--
Port of `node_index_to_node_index`.
The node index (in the array representation of the tree) of the subtree of height `l` starting at leaf `i`.
-/
def nodeIndexToNodeIndex (n: NodeIndex): Nat :=
  2 * n.position + 2^n.levels - 1

/-- Port of `compute_resolutions`. -/
def computeResolutions [BytesLike ByteArray] {l: Nat} (t: TreeSync ByteArray tkt l): List (List Nat) :=
  match t.intoLeftRightView with
  | .leaf _ _ => [(resolution t).map nodeIndexToNodeIndex]
  | .node _ left right =>
    computeResolutions left ++ [(resolution t).map nodeIndexToNodeIndex] ++ computeResolutions right

/-- Port of `test_tree_validation_one`. -/
def testTreeValidationOne (t: TreeValidationTest): IO Bool := do
  match uint16ToCiphersuite t.cipherSuite with
  | .protocolError _ =>
    -- Unsupported ciphersuite
    pure false
  | .internalError s =>
    throw (IO.userError s!"Internal error! '{s}'")
  | .success cs =>
    let _: CryptoBytes ByteArray := mkConcreteCryptoBytes cs
    let some ratchetTree := parse (RatchetTree.mf tkt) (← hexStringToBytes t.tree)
      | throw (IO.userError "ratchet_tree: parse failed")
    let groupId ← extractResult (mkMlsBytes (← hexStringToBytes t.groupId) "test_tree_validation_one" "group_id")
    let ⟨_, tree⟩ ← extractResult (ratchetTreeToTreesync ratchetTree)
    if !unmergedLeavesOk tree then
      throw (IO.userError "test_tree_validation_one: bad unmerged leaves")
    if !parentHashInvariant tree then
      throw (IO.userError "test_tree_validation_one: bad parent-hash")
    if !validLeavesInvariant groupId tree then
      throw (IO.userError "test_tree_validation_one: bad leaf signature")
    let myTreeHashes ← computeTreeHashes tree
    if myTreeHashes.length != t.treeHashes.length then
      throw (IO.userError s!"tree_hash: expected {t.treeHashes.length} hashes, got {myTreeHashes.length}")
    for (expectedTreeHash, myTreeHash) in t.treeHashes.zip myTreeHashes do
      checkEqual "tree_hash" bytesToHexString (← hexStringToBytes expectedTreeHash) myTreeHash
    let myResolutions := computeResolutions tree
    if myResolutions.length != t.resolutions.length then
      throw (IO.userError s!"resolution: expected {t.resolutions.length} resolutions, got {myResolutions.length}")
    for (expectedResolution, myResolution) in t.resolutions.zip myResolutions do
      checkEqual "resolution" toString (expectedResolution.map UInt32.toNat) myResolution
    pure true

/-- Port of `test_tree_validation`. -/
def testTreeValidation: List TreeValidationTest → IO Nat :=
  testList "Tree Validation" testTreeValidationOne

end Mls.Test.FromExt.TreeValidation
