module

public import MLS.TreeSync.Code.TreeHash
public import MLS.Common.Proofs.Tree
public import MLS.Common.Proofs.Crypto.Derived
public import MLS.Common.Proofs.Crypto.HashCollision

/-!
Port of `MLS.TreeSync.TreeHash.Proofs`.

Port-specific differences:
- MLS*'s `tree_hash_inj` is a function with a `Pure` specification:
  it is split into the function `treeHashInj` and its correctness theorem `treeHashInj_spec`.
  It is not stated as an existential: a hash collision always exists,
  the point is that `treeHashInj` computes it (in polynomial time).
- The equality of trees at possibly different heights (MLS*'s `l1 == l2 /\ i1 == i2 /\ t1 == t2`)
  is an equality of dependent pairs `⟨l1, t1⟩ = ⟨l2, t2⟩` (the position is part of the tree).
- `treeHashInj` does not use decidable equality on trees and tree hash inputs:
  it compares the serialized hash inputs (equivalent, since serialization is injective),
  and recurses on the right children when the recursion on the left children does not find a hash collision
  (instead of when the left children are equal).
-/

namespace MLS.TreeSync

open Comparse
open MLS

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `get_tree_hash_input`. -/
@[expose]
public
def getTreeHashInput {l: Nat} (t: TreeSync Bytes tkt l): Result (TreeHashInput Bytes tkt) :=
  match t.intoLeftRightView with
  | .leaf olp position => do
    let i ← mkUInt32 position "tree_hash" "i"
    pure (.leaf { leafIndex := i, leafNode := olp })
  | .node onp left right => do
    let leftHash ← treeHash left
    let leftHash ← mkMlsBytes leftHash "tree_hash" "left_bytes"
    let rightHash ← treeHash right
    let rightHash ← mkMlsBytes rightHash "tree_hash" "right_bytes"
    pure (.parent { parentNode := onp, leftHash, rightHash })

public
theorem getTreeHashInput_zero (t: TreeSync Bytes tkt 0) (hashInput: TreeHashInput Bytes tkt):
  getTreeHashInput t = .success hashInput ↔
    t.position < 2^32 ∧ hashInput = .leaf { leafIndex := t.position.toUInt32, leafNode := t.leafContent }
:= by
  obtain ⟨_, ⟨_⟩⟩ := t
  simp [getTreeHashInput, Tree.intoLeftRightView, Tree.leafContent]
  grind

public
theorem getTreeHashInput_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (hashInput: TreeHashInput Bytes tkt):
  getTreeHashInput t = .success hashInput ↔
    ∃ leftHash rightHash,
      treeHash t.left = .success leftHash.val ∧ treeHash t.right = .success rightHash.val ∧
      hashInput = .parent { parentNode := t.nodeContent, leftHash, rightHash }
:= by
  simp [getTreeHashInput]
  grind

public
theorem treeHash_eq_success {l: Nat} (t: TreeSync Bytes tkt l) (th: Bytes):
  treeHash t = .success th ↔
    ∃ hashInput, getTreeHashInput t = .success hashInput ∧
      CryptoBytes.hashHash (serializeNE (TreeHashInput.mf tkt) hashInput) = .success th
:= by
  obtain ⟨_, bt⟩ := t
  rw [treeHash.eq_def]
  cases bt <;> simp [getTreeHashInput, Tree.intoLeftRightView] <;> grind

/--
Port of `tree_hash_inj`.
The tree hash injectivity theorem.
Since hash functions are not injective, we can't exactly prove injectivity,
but we do prove injectivity modulo hash collisions.
Given two trees that have the same hash, then either:
- the two trees are equal, and at the same position (same height `l` and same leftmost leaf index `i`),
- or we compute (in polynomial time) a hash collision.

This function computes the pair of bytes, its specification is `treeHashInj_spec`.
-/
@[expose]
public
def treeHashInj {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2): Bytes × Bytes :=
  match getTreeHashInput t1, getTreeHashInput t2 with
  | .success hashInput1, .success hashInput2 =>
    let serializedHashInput1 := serializeNE (TreeHashInput.mf tkt) hashInput1
    let serializedHashInput2 := serializeNE (TreeHashInput.mf tkt) hashInput2
    if serializedHashInput1 ≠ serializedHashInput2 then
      (serializedHashInput1, serializedHashInput2)
    else
      match t1.intoLeftRightView, t2.intoLeftRightView with
      | .node _ left1 right1, .node _ left2 right2 =>
        let leftCollision := treeHashInj left1 left2
        if isHashCollision leftCollision then
          leftCollision
        else
          treeHashInj right1 right2
      | _, _ => (BytesLike.empty, BytesLike.empty)
  | _, _ => (BytesLike.empty, BytesLike.empty)
termination_by l1

theorem treeHashInj_succ_of_eq {l1 l2: Nat} (t1: TreeSync Bytes tkt (l1+1)) (t2: TreeSync Bytes tkt (l2+1))
  (hashInput: TreeHashInput Bytes tkt)
  (hi1: getTreeHashInput t1 = .success hashInput) (hi2: getTreeHashInput t2 = .success hashInput):
  treeHashInj t1 t2 =
    let leftCollision := treeHashInj t1.left t2.left
    if isHashCollision leftCollision then leftCollision else treeHashInj t1.right t2.right
:= by
  grind [treeHashInj.eq_def]

/--
One step of `treeHashInj`: when the trees have equal tree hash,
either `treeHashInj` returns a hash collision (between their serialized hash inputs), or their hash inputs are equal.
-/
theorem isHashCollision_treeHashInj_or_eq {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2) (th: Bytes)
  (h1: treeHash t1 = .success th) (h2: treeHash t2 = .success th):
  isHashCollision (treeHashInj t1 t2) ∨
    ∃ hashInput, getTreeHashInput t1 = .success hashInput ∧ getTreeHashInput t2 = .success hashInput
:= by
  grind [treeHash_eq_success, treeHashInj.eq_def, isHashCollision]

/--
Specification of `treeHashInj` (MLS*'s postcondition of `tree_hash_inj`):
if the trees `t1` and `t2` have equal tree hash,
then either they are equal, or the two bytes computed by `treeHashInj` are a hash collision.
-/
public
theorem treeHashInj_spec {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2) (th: Bytes)
  (h1: treeHash t1 = .success th) (h2: treeHash t2 = .success th):
  (⟨l1, t1⟩: (l: Nat) × TreeSync Bytes tkt l) = ⟨l2, t2⟩ ∨
    isHashCollision (treeHashInj t1 t2)
:= by
  induction t1, t2 using Tree.leftRightInduction₂ generalizing th with
  | leafLeaf t1 t2 =>
    grind [isHashCollision_treeHashInj_or_eq, Tree.sigma_eq_zero, getTreeHashInput_zero]
  | leafNode t1 t2 | nodeLeaf t1 t2 =>
    grind [isHashCollision_treeHashInj_or_eq, getTreeHashInput_zero, getTreeHashInput_succ]
  | nodeNode t1 t2 ihl ihr =>
    grind [isHashCollision_treeHashInj_or_eq, treeHashInj_succ_of_eq, Tree.sigma_eq_succ, getTreeHashInput_succ]

/-- Port of `tree_has_hash`. -/
@[expose]
public
def TreeHasHash {l: Nat} (t: TreeSync Bytes tkt l) (h: Bytes): Prop :=
  treeHash t = .success h

end MLS.TreeSync
