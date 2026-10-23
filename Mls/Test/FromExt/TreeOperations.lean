import Mls.TreeSync.Operations
import Mls.TreeKEM.NetworkTypes
import Mls.TreeDEM.NetworkTypes
import Mls.Glue.NetworkBinder
import Mls.Test.Types
import Mls.Test.Utils

/-!
Port of `MLS.Test.FromExt.TreeOperations`.
-/

namespace Mls.Test.FromExt.TreeOperations

open Comparse
open Mls Mls.TreeSync Mls.TreeKEM Mls.TreeDEM
open Mls.Test

attribute [local instance] bytesLikeByteArray

/--
Port of `fully_truncate_tree`.
Truncate the tree while its right half is empty.
-/
def fullyTruncateTree: {l: Nat} → TreeSync ByteArray tkt l → (newL: Nat) × TreeSync ByteArray tkt newL
  | 0, t => ⟨0, t⟩
  | _+1, t =>
    if isTreeEmpty t.right then
      fullyTruncateTree (treeTruncate t)
    else
      ⟨_, t⟩

def checkLeafIndex {l: Nat} (t: TreeSync ByteArray tkt l) (li: Nat) (name: String): IO Nat :=
  if t.containsLeafIndex li then pure li
  else throw (IO.userError s!"test_tree_operation_one: {name} too big")

/-- Port of `test_tree_operations_one`. -/
def testTreeOperationsOne (t: TreeOperationsTest): IO Bool := do
  let some treeBefore := parse (RatchetTree.mf tkt) (← hexStringToBytes t.treeBefore)
    | throw (IO.userError "tree_before: parse failed")
  let ⟨_, treesyncBefore⟩ ← extractResult (ratchetTreeToTreesync treeBefore)
  let some proposal := parse Proposal.mf (← hexStringToBytes t.proposal)
    | throw (IO.userError "proposal: parse failed")
  let proposalSender := t.proposalSender.toNat
  let ⟨_, treesyncAfter⟩: (l: Nat) × TreeSync ByteArray tkt l ←
    match proposal with
    | .add add => do
      let ln := add.keyPackage.tbs.leafNode
      match findEmptyLeaf treesyncBefore with
      | some li => pure ⟨_, ← extractResult (treeAdd treesyncBefore li ln)⟩
      | none =>
        let extendedTree := treeExtend treesyncBefore
        match findEmptyLeaf extendedTree with
        | some li => pure ⟨_, ← extractResult (treeAdd extendedTree li ln)⟩
        | none => throw (IO.userError "test_tree_operation_one: couldn't find empty leaf (impossible?)")
    | .update update => do
      let li ← checkLeafIndex treesyncBefore proposalSender "proposal sender"
      pure ⟨_, treeUpdate treesyncBefore li update.leafNode⟩
    | .remove remove => do
      let li ← checkLeafIndex treesyncBefore remove.removed.toNat "removed"
      pure (fullyTruncateTree (treeRemove treesyncBefore li))
    | _ => throw (IO.userError "test_tree_operations_one: bad proposal")
  let treeAfter ← extractResult (treesyncToRatchetTree treesyncAfter)
  checkEqual "tree_after" bytesToHexString (← hexStringToBytes t.treeAfter) (serialize (RatchetTree.mf tkt) treeAfter)
  pure true

/-- Port of `test_tree_operations`. -/
def testTreeOperations: List TreeOperationsTest → IO Nat :=
  testList "Tree Operations" testTreeOperationsOne

end Mls.Test.FromExt.TreeOperations
