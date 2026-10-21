import Mls.TreeSync.Types

/-!
Port of `MLS.TreeSync.Invariants.UnmergedLeaves`.
-/

namespace Mls.TreeSync

open Comparse
open Mls

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-- Check that the unmerged leaf `li` is in a non-blank leaf in `t`'s subtree. -/
def unmergedLeafExists {l: Nat} {i: TreeIndex l} (t: TreeSync Bytes tkt l i) (li: Nat): Bool :=
  if h: leafIndexInside l i li then (t.leafAt ⟨li, h⟩).isSome else false

/-- Check that the unmerged leaf `li` is unmerged everywhere it can be in `t`'s subtree. -/
def unmergedLeafConsistent: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → UInt32 → Bool
  | _, _, .leaf _, _ => true
  | l+1, i, .node optContent left right, li =>
    (match optContent with
      | none => true
      -- Read as: leafIndexInside ... → li ∈ content.unmergedLeaves
      | some content => !(leafIndexInside (l+1) i li.toNat) || content.unmergedLeaves.val.contains li) &&
    unmergedLeafConsistent left li &&
    unmergedLeafConsistent right li

/-- Check that the unmerged leaves are sorted. -/
def unmergedLeavesSorted (l: List UInt32): Bool :=
  decide (l.Pairwise (· < ·))

/--
The unmerged leaves invariant:
every non-blank node has unmerged leaves satisfying the three properties above.
-/
def unmergedLeavesOk: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → Bool
  | _, _, .leaf _ => true
  | _, _, t@(.node optContent left right) =>
    let contentOk :=
      match optContent with
      | none => true
      | some content =>
        content.unmergedLeaves.val.all (fun li => unmergedLeafExists t li.toNat) &&
        content.unmergedLeaves.val.all (unmergedLeafConsistent t) &&
        unmergedLeavesSorted content.unmergedLeaves.val
    contentOk && unmergedLeavesOk left && unmergedLeavesOk right

end Mls.TreeSync
