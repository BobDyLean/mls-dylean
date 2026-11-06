module

public import MLS.TreeSync.Code.Types
public import MLS.Common.Code.MiscLemmas

/-!
Port of `MLS.TreeSync.Invariants.UnmergedLeaves`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `unmerged_leaf_exists`.
Check that the unmerged leaf `li` is in a non-blank leaf in `t`'s subtree.
-/
@[expose]
public
def unmergedLeafExists {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): Bool :=
  t.containsLeafIndex li && (leafAt t li).isSome

/--
Port of `unmerged_leaf_consistent`.
Check that the unmerged leaf `li` is unmerged everywhere it can be in `t`'s subtree.
-/
@[expose]
public
def unmergedLeafConsistent {l: Nat} (t: TreeSync Bytes tkt l) (li: UInt32): Bool :=
  match t.intoLeftRightView with
  | .leaf _ _ => true
  | .node optContent left right =>
    (match optContent with
      | none => true
      | some content => (t.containsLeafIndex li.toNat) → content.unmergedLeaves.val.contains li) &&
    unmergedLeafConsistent left li &&
    unmergedLeafConsistent right li

/--
Port of `unmerged_leaves_sorted`.
Check that the unmerged leaves are sorted.
-/
@[expose]
public
def unmergedLeavesSorted (l: List UInt32): Bool :=
  ListChain (· < ·) l

/--
Port of `unmerged_leaves_ok`.
The unmerged leaves invariant:
every non-blank node has unmerged leaves satisfying the three properties above.
-/
@[expose]
public
def unmergedLeavesOk {l: Nat} (t: TreeSync Bytes tkt l): Bool :=
  match t.intoLeftRightView with
  | .leaf _ _ => true
  | .node optContent left right =>
    let contentOk :=
      match optContent with
      | none => true
      | some content =>
        content.unmergedLeaves.val.all (fun li => unmergedLeafExists t li.toNat) &&
        content.unmergedLeaves.val.all (unmergedLeafConsistent t) &&
        unmergedLeavesSorted content.unmergedLeaves.val
    contentOk && unmergedLeavesOk left && unmergedLeavesOk right

end MLS.TreeSync
