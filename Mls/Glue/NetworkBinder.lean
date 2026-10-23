import Mls.TreeSync.Types
import Mls.Crypto.Derived

/-!
Port of `MLS.NetworkBinder` (the parts needed by the ported tests).

Port-specific differences:
- `ratchet_tree_to_treesync_aux` does not require `List.length nodes = pow2 (l+1) - 1`:
  it fails when this precondition is not met.
-/

namespace Mls

open Comparse
open Mls.TreeSync

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-! ## ratchet_tree extension (13.4.3.3) -/

/-- Port of `TreeMath.Internal.log2`: the largest `k` such that `2^k ≤ x`. -/
def log2 (x: Nat): Nat := Nat.log2 x

/--
Port of `ratchet_tree_l`.
Pad the list of nodes with blank nodes, so that its length is `2^(l+1) - 1`.
Returns the padded list, together with `l`.
-/
def ratchetTreeL (nodes: List (Option (Node Bytes tkt))):
  Result ((l: Nat) × {newNodes: List (Option (Node Bytes tkt)) // newNodes.length = 2^(l+1) - 1})
:=
  let nNodes := nodes.length
  if nNodes % 2 = 0 then
    Result.error "ratchet_tree_l: length must be odd"
  else
    let n := (nNodes + 1) / 2
    let l := log2 n
    if h: nNodes = 2^(l+1) - 1 then
      pure ⟨l, ⟨nodes, h⟩⟩
    else
      let newNodes := nodes ++ List.replicate (2^(l+2) - 1 - nNodes) none
      if h': newNodes.length = 2^(l+2) - 1 then
        pure ⟨l+1, ⟨newNodes, h'⟩⟩
      else
        Result.internalFailure "ratchet_tree_l: wrong length"

/--
Port of `ratchet_tree_to_treesync_aux`.
MLS* requires `List.length nodes = pow2 (l+1) - 1`; otherwise, this function fails.
-/
def ratchetTreeToTreesyncAux: (l: Nat) → (position: Nat) → (nodes: List (Option (Node Bytes tkt))) →
  Result (TreeSync Bytes tkt l)
  | 0, position, nodes =>
    match nodes with
    | [some (.leaf kp)] => pure (LeftRightView.leaf (some kp) position).pack
    | [some _] => Result.error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | [none] => pure (LeftRightView.leaf none position).pack
    | _ => Result.internalFailure "ratchet_tree_to_treesync_aux: wrong length"
  | l+1, position, nodes =>
    match nodes.drop (2^(l+1) - 1) with
    | myNode :: rightNodes => do
      let leftRes ← ratchetTreeToTreesyncAux l position (nodes.take (2^(l+1) - 1))
      let rightRes ← ratchetTreeToTreesyncAux l (position + 2^l) rightNodes
      match myNode with
      | some (.parent pn) => pure (LeftRightView.node (some pn) leftRes rightRes).pack
      | some _ => Result.error "ratchet_tree_to_treesync_aux: node must be a parent!"
      | none => pure (LeftRightView.node none leftRes rightRes).pack
    | [] => Result.internalFailure "ratchet_tree_to_treesync_aux: wrong length"

/-- Port of `ratchet_tree_to_treesync`. -/
def ratchetTreeToTreesync (nodes: RatchetTree Bytes tkt): Result ((l: Nat) × TreeSync Bytes tkt l) := do
  let ⟨l, ⟨newNodes, _⟩⟩ ← ratchetTreeL nodes.val
  let res ← ratchetTreeToTreesyncAux l 0 newNodes
  pure ⟨l, res⟩

/-- Port of `treesync_to_ratchet_tree_aux`. -/
def treesyncToRatchetTreeAux {l: Nat} (t: TreeSync Bytes tkt l): Result (List (Option (Node Bytes tkt))) :=
  match t.intoLeftRightView with
  | .leaf none _ => pure [none]
  | .leaf (some lp) _ => pure [some (.leaf lp)]
  | .node onp left right => do
    let parentNode := onp.map Node.parent
    let leftRatchet ← treesyncToRatchetTreeAux left
    let rightRatchet ← treesyncToRatchetTreeAux right
    pure (leftRatchet ++ [parentNode] ++ rightRatchet)

/-- Port of `shrink_ratchet_tree_aux`. -/
def shrinkRatchetTreeAux: List (Option (Node Bytes tkt)) → Option (List (Option (Node Bytes tkt)))
  | [] => none
  | optH :: t =>
    match optH, shrinkRatchetTreeAux t with
    | none, none => none
    | some _, none => some [optH]
    | _, some shrinkedT => some (optH :: shrinkedT)

/-- Port of `shrink_ratchet_tree`. -/
def shrinkRatchetTree (l: List (Option (Node Bytes tkt))): Result (RatchetTree Bytes tkt) :=
  match shrinkRatchetTreeAux l with
  | none => mkMlsList [] "shrink_ratchet_tree" "ratchet_tree"
  | some res => mkMlsList res "shrink_ratchet_tree" "ratchet_tree"

/-- Port of `treesync_to_ratchet_tree`. -/
def treesyncToRatchetTree {l: Nat} (t: TreeSync Bytes tkt l): Result (RatchetTree Bytes tkt) := do
  let preRatchetTree ← treesyncToRatchetTreeAux t
  shrinkRatchetTree preRatchetTree

end Mls
