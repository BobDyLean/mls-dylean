import Mls.TreeSync.Types
import Mls.Crypto.Derived

/-!
Port of `MLS.NetworkBinder` (the parts needed by the ported tests).

Port-specific differences:
- `ratchet_tree_to_treesync_aux` takes the length invariant `nodes.length = 2^(l+1) - 1` as a proof,
  and recursion is structural on `l`.
-/

namespace Mls

open Comparse
open Mls.TreeSync

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-! ## ratchet_tree extension (13.4.3.3) -/

/-- Port of `TreeMath.Internal.log2`: the largest `k` such that `2^k ≤ x`. -/
def log2 (x: Nat): Nat := Nat.log2 x

/--
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

theorem length_split {l: Nat} (n: Nat) (h: n = 2^(l+2) - 1):
  2^(l+1) - 1 ≤ n ∧ n - (2^(l+1) - 1) - 1 = 2^(l+1) - 1 ∧ 0 < n - (2^(l+1) - 1)
:= by
  have: 2^(l+2) = 2^(l+1) * 2 := Nat.pow_succ 2 (l+1)
  have: 0 < 2^(l+1) := Nat.two_pow_pos _
  omega

def ratchetTreeToTreesyncAux: (l: Nat) → (i: TreeIndex l) → (nodes: List (Option (Node Bytes tkt))) →
  nodes.length = 2^(l+1) - 1 → Result (TreeSync Bytes tkt l i)
  | 0, _, nodes, h =>
    match nodes, h with
    | [some (.leaf kp)], _ => pure (.leaf (some kp))
    | [some _], _ => Result.error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | [none], _ => pure (.leaf none)
  | l+1, i, nodes, h => do
    have hs := length_split nodes.length h
    let leftNodes := nodes.take (2^(l+1) - 1)
    let rest := nodes.drop (2^(l+1) - 1)
    have hRest: rest.length = nodes.length - (2^(l+1) - 1) := List.length_drop
    match rest, hRest with
    | myNode :: rightNodes, hRest => do
      let leftRes ← ratchetTreeToTreesyncAux l i.left leftNodes (by simp [leftNodes, List.length_take]; omega)
      let rightRes ← ratchetTreeToTreesyncAux l i.right rightNodes (by simp at hRest; omega)
      match myNode with
      | some (.parent pn) => pure (.node (some pn) leftRes rightRes)
      | some _ => Result.error "ratchet_tree_to_treesync_aux: node must be a parent!"
      | none => pure (.node none leftRes rightRes)
    | [], hRest => absurd hRest (by simp; omega)

def ratchetTreeToTreesync (nodes: RatchetTree Bytes tkt): Result ((l: Nat) × TreeSync Bytes tkt l (TreeIndex.zero l)) := do
  let ⟨l, ⟨newNodes, h⟩⟩ ← ratchetTreeL nodes.val
  let res ← ratchetTreeToTreesyncAux l (TreeIndex.zero l) newNodes h
  pure ⟨l, res⟩

def treesyncToRatchetTreeAux: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → Result (List (Option (Node Bytes tkt)))
  | _, _, .leaf none => pure [none]
  | _, _, .leaf (some lp) => pure [some (.leaf lp)]
  | _, _, .node onp left right => do
    let parentNode := onp.map Node.parent
    let leftRatchet ← treesyncToRatchetTreeAux left
    let rightRatchet ← treesyncToRatchetTreeAux right
    pure (leftRatchet ++ [parentNode] ++ rightRatchet)

def shrinkRatchetTreeAux: List (Option (Node Bytes tkt)) → Option (List (Option (Node Bytes tkt)))
  | [] => none
  | optH :: t =>
    match optH, shrinkRatchetTreeAux t with
    | none, none => none
    | some _, none => some [optH]
    | _, some shrinkedT => some (optH :: shrinkedT)

def shrinkRatchetTree (l: List (Option (Node Bytes tkt))): Result (RatchetTree Bytes tkt) :=
  match shrinkRatchetTreeAux l with
  | none => mkMlsList [] "shrink_ratchet_tree" "ratchet_tree"
  | some res => mkMlsList res "shrink_ratchet_tree" "ratchet_tree"

def treesyncToRatchetTree {l: Nat} {i: TreeIndex l} (t: TreeSync Bytes tkt l i): Result (RatchetTree Bytes tkt) := do
  let preRatchetTree ← treesyncToRatchetTreeAux t
  shrinkRatchetTree preRatchetTree

end Mls
