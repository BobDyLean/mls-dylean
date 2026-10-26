module

public import MLS.TreeSync.Code.Operations

/-!
Port of `MLS.TreeSync.Invariants.ParentHash`.

Port-specific differences:
- The "parent" tree `p` (of height `lp > ld` and not blank in MLS*) has height `lp+1`,
  so that it is a node by its type. Being non-blank is a separate hypothesis where needed.
- `get_child_sibling p id` is `p.child d.position` and `p.sibling d.position`:
  the position of the descendant `d` is used as a leaf index of `p`.
  MLS*'s refinement `leaf_index_inside lp ip id` is not needed to define the functions.
- Preconditions of MLS* (`node_has_parent_hash d`, `node_not_blank p`, `ld < lp`, `leaf_index_inside lp ip id`)
  are not ported: functions return `false` (or a default value) when they are not met (see the docstrings).
- Functions recurse on the views of `MLS.Tree`.
-/

namespace MLS.TreeSync

open Comparse
open MLS

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `node_not_blank`. -/
@[expose]
public
def nodeNotBlank {l: Nat} (t: TreeSync Bytes tkt l): Bool :=
  match t.intoLeftRightView with
  | .leaf content _ => content.isSome
  | .node content _ _ => content.isSome

/--
Port of `get_parent_hash_of`.
The parent hash stored in a node, if any.
MLS* requires `node_has_parent_hash t`; here, `none` is returned when it is not met.
-/
@[expose]
public
def getParentHashOf {l: Nat} (t: TreeSync Bytes tkt l): Option (MlsBytes Bytes) :=
  match t.intoLeftRightView with
  | .leaf (some ln) _ => if h: ln.data.source == .commit then some (ln.data.parentHash.get h) else none
  | .leaf none _ => none
  | .node (some content) _ _ => content.parentHash
  | .node none _ _ => none

/-- Port of `node_has_parent_hash`. -/
@[expose]
public
def nodeHasParentHash {l: Nat} (t: TreeSync Bytes tkt l): Bool :=
  (getParentHashOf t).isSome

/-- Port of `mem_ul`. -/
@[expose]
public
def memUl (x: Nat): List UInt32 → Bool
  | [] => false
  | h::t => x == h.toNat || memUl x t

/-- Port of `un_add_unmerged_leaf`. -/
@[expose]
public
def unAddUnmergedLeaf (leaves: List UInt32) (i: Nat): Bool :=
  !(memUl i leaves)

/--
Port of `un_add`.
Remove, or "un-add" the leaves whose index are in a list.
This to compute the "original sibling" in the parent-hash check when joining a group.
-/
@[expose]
public
def unAdd {l: Nat} (t: TreeSync Bytes tkt l) (leaves: List UInt32): TreeSync Bytes tkt l :=
  unAddP t (unAddUnmergedLeaf leaves)

/-- Port of `set_equal_mem`. -/
@[expose]
public
def setEqualMem {α: Type} [DecidableEq α] (l: List α) (x: α): Bool :=
  l.contains x

/-- Port of `set_eq`. -/
@[expose]
public
def setEq {α: Type} [DecidableEq α] (l1 l2: List α): Bool :=
  l2.all (setEqualMem l1) && l1.all (setEqualMem l2)

/-- Port of `unmerged_resolution`. -/
@[expose]
public
def unmergedResolution (l: List UInt32): List NodeIndex :=
  l.map (fun x => NodeIndex.ofLeafIndex x.toNat)

/-- Port of `resolution`. -/
@[expose]
public
def resolution {l: Nat} (t: TreeSync Bytes tkt l): List NodeIndex :=
  match t.intoLeftRightView with
  | .leaf none _ => []
  | .leaf (some _) _ => [t.nodeIndex]
  | .node none left right => resolution left ++ resolution right
  | .node (some content) _ _ => t.nodeIndex :: unmergedResolution content.unmergedLeaves.val

/--
Port of `unmerged_leaves_of` (from `MLS.TreeSync.Proofs.ParentHashGuarantees`).
The unmerged leaves of a node (empty for leaves and blank nodes).
-/
@[expose]
public
def unmergedLeavesOf {l: Nat} (t: TreeSync Bytes tkt l): List UInt32 :=
  match t.intoLeftRightView with
  | .leaf _ _ => []
  | .node none _ _ => []
  | .node (some content) _ _ => content.unmergedLeaves.val

/--
Port of `last_update_lhs`.
MLS* requires `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
-/
@[expose]
public
def lastUpdateLhs {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): List NodeIndex :=
  (resolution (p.child d.position)).filter (· != d.nodeIndex)

/--
Port of `last_update_rhs`.
MLS* requires `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
When `p` is blank, its unmerged leaves are considered empty.
-/
@[expose]
public
def lastUpdateRhs {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): List NodeIndex :=
  let c := p.child d.position
  unmergedResolution ((unmergedLeavesOf p).filter (fun x => c.containsLeafIndex x.toNat))

/--
Port of `last_update_d_in_res_c`.
MLS* requires `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
-/
@[expose]
public
def lastUpdateDInResC {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): Bool :=
  (resolution (p.child d.position)).contains d.nodeIndex

/--
Port of `last_update_correct`.
Given a "parent" tree P, and a "descendant" D,
check that D and P were last updated at the same time,
using the "ninja" equation used in the RFC involving the resolution.
MLS* requires `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
-/
@[expose]
public
def lastUpdateCorrect {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): Bool :=
  -- As in MLS*, set equality (and not list equality), see the comment in `MLS.TreeSync.Invariants.ParentHash`.
  lastUpdateDInResC d p && setEq (lastUpdateLhs d p) (lastUpdateRhs d p)

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `parent_hash_correct`.
Given a "parent" tree P, and a "descendant" D,
check that the parent-hash stored at the root of D is correct with respect to P.
MLS* requires `node_has_parent_hash d`, `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`;
here, the result is `false` when `d` has no parent hash or `p` is blank.
-/
@[expose]
public
def parentHashCorrect {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): Bool :=
  match p.nodeContent with
  | none => false
  | some pContent =>
    match getParentHashOf d with
    | none => false
    | some expectedParentHash =>
      let originalSibling := unAdd (p.sibling d.position) pContent.unmergedLeaves.val
      match computeParentHash pContent.content pContent.parentHash.val originalSibling with
      | .success ph => ph == expectedParentHash.val
      | _ => false

/--
Port of `parent_hash_linked`.
The `parent-hash link` relationship between a "parent" tree P, and a "descendant" D.
It checks that:
- the parent-hash stored in D is correct with respect to P,
- D and P were last updated at the same time.
MLS* requires `node_has_parent_hash d`, `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
-/
@[expose]
public
def parentHashLinked {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)): Bool :=
  parentHashCorrect d p && lastUpdateCorrect d p

/--
Port of `node_has_parent_hash_link_aux`.
Search a parent-hash link to `p` from `d` or below.
MLS* requires `node_not_blank p`, `ld < lp` and `leaf_index_inside lp ip id`.
-/
@[expose]
public
def nodeHasParentHashLinkAux  {ld: Nat} (d: TreeSync Bytes tkt ld) {lp: Nat} (p: TreeSync Bytes tkt (lp+1)): Bool :=
  match d.intoLeftRightView with
  | .leaf none _ => false
  | .leaf (some _) _ => parentHashLinked d p
  | .node (some _) _ _ => parentHashLinked d p
  | .node none left right => nodeHasParentHashLinkAux left p || nodeHasParentHashLinkAux right p

/--
Port of `node_has_parent_hash_link`.
MLS* requires `node_not_blank p`.
-/
@[expose]
public
def nodeHasParentHashLink {lp: Nat} (p: TreeSync Bytes tkt (lp+1)): Bool :=
  match p.intoLeftRightView with
  | .node _ left right => nodeHasParentHashLinkAux left p || nodeHasParentHashLinkAux right p

/--
Port of `parent_hash_invariant`.
The parent-hash invariant:
every non-blank node has a parent-hash link coming from a node below it.
-/
@[expose]
public
def parentHashInvariant {lp: Nat} (t: TreeSync Bytes tkt lp): Bool :=
  match t.intoLeftRightView with
  | .leaf _ _ => true
  | .node none left right =>
    parentHashInvariant left && parentHashInvariant right
  | .node (some _) left right =>
    parentHashInvariant left && parentHashInvariant right && nodeHasParentHashLink t

end CryptoBytes

end MLS.TreeSync
