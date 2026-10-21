import Mls.TreeSync.Operations

/-!
Port of `MLS.TreeSync.Invariants.ParentHash`.

Port-specific differences:
- The "parent" tree `p` (of height `lp > ld` and not blank in MLS*) has height `lp+1`,
  so that it is a node by its type. Being non-blank is a separate hypothesis where needed.
- The descendant `d` (at tree index `id`) lies inside `p`: the refinement `leaf_index_inside lp ip id`
  is a hypothesis `hInside`, and `id` is used as a leaf index of `p` with `⟨id.val, hInside⟩`.
- `get_child_sibling p id` is `Tree.getChildSiblingPair`, which hides the indices of the child and sibling:
  the functions below only need index-polymorphic functions of them.
- `node_index` is `NodeIndex`, a dependent pair of a height and a tree index.
-/

namespace Mls.TreeSync

open Comparse
open Mls Mls.Tree

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

def nodeNotBlank {l: Nat} {i: TreeIndex l}: TreeSync Bytes tkt l i → Bool
  | .leaf (some _) => true
  | .node (some _) _ _ => true
  | _ => false

def nodeHasParentHash {l: Nat} {i: TreeIndex l}: TreeSync Bytes tkt l i → Bool
  | .leaf (some ln) => ln.data.source == .commit
  | .node (some _) _ _ => true
  | _ => false

def getParentHashOf {l: Nat} {i: TreeIndex l}: (t: TreeSync Bytes tkt l i) → nodeHasParentHash t → MlsBytes Bytes
  | .leaf (some content), h => content.data.parentHash.get (by simpa [nodeHasParentHash] using h)
  | .node (some content) _ _, _ => content.parentHash

def memUl (x: Nat): List UInt32 → Bool
  | [] => false
  | h::t => x == h.toNat || memUl x t

def unAddUnmergedLeaf (leaves: List UInt32) (i: Nat): Bool :=
  !(memUl i leaves)

/--
Remove, or "un-add" the leaves whose index are in a list.
This to compute the "original sibling" in the parent-hash check when joining a group.
-/
def unAdd {l: Nat} {i: TreeIndex l} (t: TreeSync Bytes tkt l i) (leaves: List UInt32): TreeSync Bytes tkt l i :=
  unAddP t (unAddUnmergedLeaf leaves)

def setEqualMem {α: Type} [DecidableEq α] (l: List α) (x: α): Bool :=
  l.contains x

def setEq {α: Type} [DecidableEq α] (l1 l2: List α): Bool :=
  l2.all (setEqualMem l1) && l1.all (setEqualMem l2)

/-- Port of `node_index`. -/
def NodeIndex := (l: Nat) × TreeIndex l

instance: DecidableEq NodeIndex := fun ⟨l1, i1⟩ ⟨l2, i2⟩ =>
  if h: l1 = l2 ∧ i1.val = i2.val then
    isTrue (by obtain ⟨rfl, hv⟩ := h; exact congrArg (Sigma.mk l1) (Subtype.ext hv))
  else
    isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)

def natToNodeIndex (n: Nat): NodeIndex := ⟨0, ⟨n, Nat.one_dvd n⟩⟩

def unmergedResolution (l: List UInt32): List NodeIndex :=
  l.map (fun x => natToNodeIndex x.toNat)

def resolution: {l: Nat} → {i: TreeIndex l} → TreeSync Bytes tkt l i → List NodeIndex
  | _, _, .leaf none => []
  | _, i, .leaf (some _) => [⟨0, i⟩]
  | _, _, .node none left right => resolution left ++ resolution right
  | l+1, i, .node (some content) _ _ => ⟨l+1, i⟩ :: unmergedResolution content.unmergedLeaves.val

/-- The unmerged leaves of a non-blank node. -/
def unmergedLeavesOf {l: Nat} {i: TreeIndex (l+1)}: (p: TreeSync Bytes tkt (l+1) i) → nodeNotBlank p → List UInt32
  | .node (some content) _ _, _ => content.unmergedLeaves.val

def lastUpdateLhs {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val) (_: TreeSync Bytes tkt ld id) (p: TreeSync Bytes tkt (lp+1) ip): List NodeIndex
:=
  let (⟨_, c⟩, _) := p.getChildSiblingPair ⟨id.val, hInside⟩
  (resolution c).filter (· != ⟨ld, id⟩)

def lastUpdateRhs {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val) (_: TreeSync Bytes tkt ld id) (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p):
  List NodeIndex
:=
  let (⟨ic, _⟩, _) := p.getChildSiblingPair ⟨id.val, hInside⟩
  unmergedResolution ((unmergedLeavesOf p hp).filter (fun x => leafIndexInside lp ic x.toNat))

def lastUpdateDInResC {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val) (_: TreeSync Bytes tkt ld id) (p: TreeSync Bytes tkt (lp+1) ip): Bool
:=
  let (⟨_, c⟩, _) := p.getChildSiblingPair ⟨id.val, hInside⟩
  (resolution c).contains ⟨ld, id⟩

/--
Given a "parent" tree P, and a "descendant" D,
check that D and P were last updated at the same time,
using the "ninja" equation used in the RFC involving the resolution.
-/
def lastUpdateCorrect {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val) (d: TreeSync Bytes tkt ld id) (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p): Bool
:=
  -- As in MLS*, set equality (and not list equality), see the comment in `MLS.TreeSync.Invariants.ParentHash`.
  lastUpdateDInResC hInside d p && setEq (lastUpdateLhs hInside d p) (lastUpdateRhs hInside d p hp)

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- The content of a non-blank node. -/
def contentOf {l: Nat} {i: TreeIndex (l+1)}: (p: TreeSync Bytes tkt (l+1) i) → nodeNotBlank p → ParentNode Bytes tkt
  | .node (some content) _ _, _ => content

/--
Given a "parent" tree P, and a "descendant" D,
check that the parent-hash stored at the root of D is correct with respect to P.
-/
def parentHashCorrect {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val)
  (d: TreeSync Bytes tkt ld id) (hd: nodeHasParentHash d) (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p): Bool
:=
  let pContent := contentOf p hp
  let expectedParentHash := getParentHashOf d hd
  let (_, ⟨_, sibling⟩) := p.getChildSiblingPair ⟨id.val, hInside⟩
  let originalSibling := unAdd sibling pContent.unmergedLeaves.val
  match computeParentHash pContent.content pContent.parentHash.val originalSibling with
  | .success ph => ph == expectedParentHash.val
  | _ => false

/--
The `parent-hash link` relationship between a "parent" tree P, and a "descendant" D.
It checks that:
- the parent-hash stored in D is correct with respect to P,
- D and P were last updated at the same time.
-/
def parentHashLinked {ld lp: Nat} {id: TreeIndex ld} {ip: TreeIndex (lp+1)}
  (hInside: leafIndexInside (lp+1) ip id.val)
  (d: TreeSync Bytes tkt ld id) (hd: nodeHasParentHash d) (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p): Bool
:=
  parentHashCorrect hInside d hd p hp && lastUpdateCorrect hInside d p hp

/--
Search a parent-hash link to `p` from `d` or below.
`d` lies inside `p` (`hInside`), and is strictly below it (`hl`).
-/
def nodeHasParentHashLinkAux {lp: Nat} {ip: TreeIndex (lp+1)} (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p):
  {ld: Nat} → {id: TreeIndex ld} → (d: TreeSync Bytes tkt ld id) → ld + 1 ≤ lp + 1 → leafIndexInside (lp+1) ip id.val → Bool
  | _, _, .leaf none, _, _ => false
  | _, _, .leaf (some lp'), _, hInside =>
    if hd: lp'.data.source == .commit then parentHashLinked hInside (.leaf (some lp')) hd p hp else false
  | _, _, .node (some c) left right, _, hInside =>
    parentHashLinked hInside (.node (some c) left right) rfl p hp
  | _, _, .node none left right, hl, hInside =>
    nodeHasParentHashLinkAux p hp left (by omega) (leafIndexInside_left_of_inside hInside) ||
    nodeHasParentHashLinkAux p hp right (by omega) (leafIndexInside_right_of_inside (by omega) hInside)

theorem leafIndexInside_self_left {l: Nat} (i: TreeIndex (l+1)): leafIndexInside (l+1) i i.left.val := by
  apply (leafIndexInside_iff _ _ _).mpr
  simp only [TreeIndex.left]
  have := Nat.two_pow_pos (l+1)
  omega

theorem leafIndexInside_self_right {l: Nat} (i: TreeIndex (l+1)): leafIndexInside (l+1) i i.right.val := by
  apply (leafIndexInside_iff _ _ _).mpr
  simp only [TreeIndex.right]
  have: 2^(l+1) = 2^l * 2 := Nat.pow_succ 2 l
  have := Nat.two_pow_pos l
  omega

def nodeHasParentHashLink {lp: Nat} {ip: TreeIndex (lp+1)} (p: TreeSync Bytes tkt (lp+1) ip) (hp: nodeNotBlank p): Bool :=
  match p, hp with
  | .node (some _) left right, hp =>
    nodeHasParentHashLinkAux (.node (some _) left right) hp left (by omega) (leafIndexInside_self_left ip) ||
    nodeHasParentHashLinkAux (.node (some _) left right) hp right (by omega) (leafIndexInside_self_right ip)

/--
The parent-hash invariant:
every non-blank node has a parent-hash link coming from a node below it.
-/
def parentHashInvariant: {lp: Nat} → {ip: TreeIndex lp} → TreeSync Bytes tkt lp ip → Bool
  | _, _, .leaf _ => true
  | _, _, .node none left right =>
    parentHashInvariant left && parentHashInvariant right
  | _, _, .node (some c) left right =>
    parentHashInvariant left && parentHashInvariant right && nodeHasParentHashLink (.node (some c) left right) rfl

end CryptoBytes

end Mls.TreeSync
