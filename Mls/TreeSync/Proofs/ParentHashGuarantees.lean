import Mls.TreeSync.Proofs.Invariants.ParentHash.Proofs
import Mls.TreeSync.Proofs.ParentHash.Proofs

/-!
Port of `MLS.TreeSync.Proofs.ParentHashGuarantees`.

Port-specific differences:
- `equivalent` is the `Prop` `Equivalent`, and compares trees at possibly different heights
  as dependent pairs (the position is part of the tree).
- `canonicalize_unmerged_leaves` always un-adds `unmergedLeavesOf t`:
  on leaves and blank nodes, MLS* returns `t`, which is `unAdd t []` (see `unAdd_nil`).
- `is_subtree_with_blanks_between` is the inductive `IsSubtreeWithBlanksBetween`
  (as `is_subtree_of` is `Tree.IsSubtreeOf`).
- `unmerged_leaves_of` is in `Mls.TreeSync.Invariants.ParentHash` (it is used by `lastUpdateRhs`),
  and `filter_eq_lemma` is `List.filter_congr`.
- The functions with a `Pure` specification (`parent_hash_guarantee_theorem_step`, `parent_hash_guarantee_theorem_aux`,
  `parent_hash_guarantee_theorem`) are split into functions and `_spec` theorems,
  and do not use decidable equality on trees:
  `parentHashGuaranteeTheoremStep` always returns the result of `computeParentHashInj`
  (MLS* returns `(empty, empty)` when all the inputs are equal, in which case the parents are equivalent),
  and `parentHashGuaranteeTheoremAux` goes on when the step does not return a hash collision.
  The tree reasoning of `parent_hash_guarantee_theorem_step` is the lemma `equivalent_of_lastUpdateCorrect`.
- Tree lists are lists of dependent pairs (`OneTree`).
  `tree_list_is_parent_hash_linkedP` (and its reversed version) is the generic `ListChain`:
  the "Reversing" section is `ListChain.reverse`, `List.mem_reverse` and `List.head?_reverse`.
- `parent_hash_invariant_to_tree_list(_rev)` and `compute_parent_hash_link(_aux)` only compute a witness:
  they are the existential `exists_treeList_of_parentHashInvariant`.
- `path_to_tree_list_aux` goes through the path one node at a time (as MLS*'s `path_to_tree_list_pre_aux`),
  instead of jumping between non-blank nodes with `find_node_and_path_parent_hash_link(_aux)` (not ported,
  with their lemmas): it computes the same list, and terminates structurally.
  `pathToTreeList` returns a `Result`.
- `path_to_tree_list_pre_aux` is defined from the list computed by `pathToTreeListAux`,
  not by recursion on the path: its lemmas follow from the definition.
-/

namespace Mls

variable {Leaf Node: Type}

/-- Port of `is_subtree_of_node_index_inside`. -/
theorem Tree.IsSubtreeOf.containsNodeIndex {ld lp: Nat} {d: Tree Leaf Node ld} {p: Tree Leaf Node lp}
  (h: d.IsSubtreeOf p) {x: NodeIndex} (hx: d.containsNodeIndex x):
  p.containsNodeIndex x
:= by
  grind [Tree.containsNodeIndex]

/--
Two nodes containing `li`, whose siblings for `li` are at the same position, are at the same position.
MLS* gets it from the tree index arithmetic.
-/
theorem Tree.position_eq_of_sibling_position_eq {l: Nat} (t1 t2: Tree Leaf Node (l+1)) (li: Nat)
  (h1: t1.containsLeafIndex li) (h2: t2.containsLeafIndex li) (h: (t1.sibling li).position = (t2.sibling li).position):
  t1.position = t2.position
:= by
  grind [Tree.containsLeafIndex]

/--
Each element of the list is related to the next one by `R`.
MLS* defines it for each relation (e.g. `tree_list_is_parent_hash_linkedP`).
-/
def ListChain {α: Type} (R: α → α → Prop): List α → Prop
  | [] | [_] => True
  | a :: b :: l => R a b ∧ ListChain R (b :: l)

theorem ListChain.append_singleton {α: Type} {R: α → α → Prop} {l: List α} {a: α}
  (h: ListChain R l) (hlast: ∀ x ∈ l.getLast?, R x a):
  ListChain R (l ++ [a])
:= by
  induction l with
  | nil => trivial
  | cons x l ih =>
    cases l with
    | nil => exact ⟨hlast x rfl, trivial⟩
    | cons y l => exact ⟨h.1, ih h.2 (by simpa using hlast)⟩

/-- Port of `tree_list_is_parent_hash_linkedP_rev_eq` and `tree_list_is_parent_hash_linkedP_rev_acc_eq`. -/
theorem ListChain.reverse {α: Type} {R: α → α → Prop} {l: List α} (h: ListChain (flip R) l):
  ListChain R l.reverse
:= by
  induction l with
  | nil => trivial
  | cons x l ih =>
    rw [List.reverse_cons]
    apply ListChain.append_singleton
    · cases l <;> grind [ListChain]
    · cases l <;> simp_all [ListChain, flip]

theorem StaticOption.mk_inj {b: Bool} {a: Type} (h: b = true) {x y: a}:
  (StaticOption.mk x: StaticOption b a) = StaticOption.mk y ↔ x = y
:= by
  subst h
  rfl

/-- Port of `is_tree_empty_eq_lemma`. -/
theorem eq_of_isTreeEmpty {l: Nat} (t1 t2: Tree (Option Leaf) (Option Node) l)
  (hp: t1.position = t2.position) (h1: isTreeEmpty t1) (h2: isTreeEmpty t2):
  t1 = t2
:= by
  induction t1 using Tree.leftRightInduction with
  | leaf t1 => apply Tree.ext_zero <;> grind [isTreeEmpty_zero, Option.isNone_iff_eq_none]
  | node t1 ihLeft ihRight =>
    rw [isTreeEmpty_succ _ t1.position] at h1
    rw [isTreeEmpty_succ _ t1.position] at h2
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h1 h2
    apply Tree.ext_succ t1.position <;> grind

end Mls

namespace Mls.TreeSync

open Comparse
open Mls

section BytesLike

variable {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}

/-! ## Tree equivalence definition -/

/--
Port of `canonicalize_leaf_signature`.
Empty the signature of one specific leaf.
Later, we will prove that thanks to the parent-hash,
the signature of a leaf covers many subtrees above it.
Except that the signature doesn't cover itself,
so we first have to remove it before stating our integrity theorem.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`);
otherwise, the function follows the path to the leaf closest to `li`.
-/
def canonicalizeLeafSignature {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): TreeSync Bytes tkt l :=
  match t.intoChildSiblingView li with
  | .leaf oln position =>
    (ChildSiblingView.leaf (oln.map fun ln => { ln with signature := MlsBytes.empty }) position).pack
  | .node content child sibling =>
    (ChildSiblingView.node content (canonicalizeLeafSignature child li) sibling).pack
termination_by l

/--
Port of `canonicalize_unmerged_leaves`.
Remove unmerged leaves from a subtree.
Unmerged leaves represent leaves that were added after the subtree was last authenticated,
hence we remove them to state our integrity theorem.
-/
def canonicalizeUnmergedLeaves {l: Nat} (t: TreeSync Bytes tkt l): TreeSync Bytes tkt l :=
  unAdd t (unmergedLeavesOf t)

/--
Port of `canonicalize`.
Do the full canonicalization:
- remove unmerged leaves of the root node,
- remove the signature of one leaf (the one who last updated the subtree).
-/
def canonicalize {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): TreeSync Bytes tkt l :=
  canonicalizeLeafSignature (canonicalizeUnmergedLeaves t) li

/--
Port of `equivalent`.
Two subtrees are said to be equivalent (with respect to a leaf index `li`)
when they have the same canonicalization.
-/
def Equivalent {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2) (li: Nat): Prop :=
  t1.containsLeafIndex li ∧
    (⟨l1, canonicalize t1 li⟩: (l: Nat) × TreeSync Bytes tkt l) = ⟨l2, canonicalize t2 li⟩

/-! ## Theorems about canonicalization -/

/-- Port of `is_unmerged_leaves_canonicalized`. -/
def isUnmergedLeavesCanonicalized {l: Nat} (t: TreeSync Bytes tkt l): Bool :=
  (unmergedLeavesOf t).isEmpty

/-- Port of `is_leaf_signature_canonicalized`. -/
def isLeafSignatureCanonicalized {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): Bool :=
  match leafAt t li with
  | none => true
  | some ln => BytesLike.recognizeEmpty ln.signature.val

/-- Port of `is_canonicalized`. -/
def isCanonicalized {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): Bool :=
  isUnmergedLeavesCanonicalized t && isLeafSignatureCanonicalized t li

@[simp] theorem canonicalizeLeafSignature_position {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  (canonicalizeLeafSignature t li).position = t.position
:= by
  induction t using Tree.childInduction li <;> grind [canonicalizeLeafSignature.eq_def]

grind_pattern canonicalizeLeafSignature_position => (canonicalizeLeafSignature t li).position

theorem leafContent_canonicalizeLeafSignature (t: TreeSync Bytes tkt 0) (li: Nat):
  (canonicalizeLeafSignature t li).leafContent = t.leafContent.map fun ln => { ln with signature := MlsBytes.empty }
:= by
  grind [canonicalizeLeafSignature.eq_def]

/-- `canonicalizeLeafSignature` of a node, through the child / sibling view for `li`. -/
theorem canonicalizeLeafSignature_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  (canonicalizeLeafSignature t li).nodeContent = t.nodeContent ∧
  (canonicalizeLeafSignature t li).child li = canonicalizeLeafSignature (t.child li) li ∧
  (canonicalizeLeafSignature t li).sibling li = t.sibling li
:= by
  grind [canonicalizeLeafSignature.eq_def]

theorem unmergedLeavesOf_zero (t: TreeSync Bytes tkt 0): unmergedLeavesOf t = [] := by
  obtain ⟨_, ⟨_⟩⟩ := t
  rfl

/-- Port of `canonicalize_unmerged_leaves_idempotent`. -/
theorem canonicalizeUnmergedLeaves_eq_self {l: Nat} (t: TreeSync Bytes tkt l) (h: isUnmergedLeavesCanonicalized t):
  canonicalizeUnmergedLeaves t = t
:= by
  grind [canonicalizeUnmergedLeaves, isUnmergedLeavesCanonicalized, unAdd_nil]

/-- Port of `canonicalize_leaf_signature_idempotent`. -/
theorem canonicalizeLeafSignature_eq_self {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (h: isLeafSignatureCanonicalized t li):
  canonicalizeLeafSignature t li = t
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    apply Tree.ext_zero
    · simp
    · rw [leafContent_canonicalizeLeafSignature]
      cases hc: t.leafContent with
      | none => rfl
      | some ln =>
        obtain ⟨_, ⟨_, _⟩⟩ := ln
        simp_all [isLeafSignatureCanonicalized, leafAt.eq_def, BytesLike.recognizeEmpty_correct, MlsBytes.empty]
  | node t ih =>
    have := canonicalizeLeafSignature_succ t li
    apply Tree.ext_succ li <;> grind [isLeafSignatureCanonicalized, leafAt.eq_def]

/-- Port of `canonicalize_idempotent`. -/
theorem canonicalize_eq_self {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (h: isCanonicalized t li):
  canonicalize t li = t
:= by
  grind [canonicalize, isCanonicalized, canonicalizeUnmergedLeaves_eq_self, canonicalizeLeafSignature_eq_self]

/-! ## Induction step -/

theorem nodeNotBlank_zero (t: TreeSync Bytes tkt 0): nodeNotBlank t = t.leafContent.isSome := by
  obtain ⟨_, ⟨_⟩⟩ := t
  rfl

theorem nodeNotBlank_of_nodeHasParentHash {l: Nat} (t: TreeSync Bytes tkt l) (h: nodeHasParentHash t):
  nodeNotBlank t
:= by
  cases l with
  | zero => cases hc: t.leafContent <;> simp_all [nodeHasParentHash, getParentHashOf_zero, nodeNotBlank_zero]
  | succ l => grind [nodeHasParentHash, getParentHashOf_succ, nodeNotBlank_succ]

/--
Port of `get_parent_hash_of_canonicalize`.
MLS* also proves `node_not_blank (canonicalize t li)`, which follows (`nodeNotBlank_of_nodeHasParentHash`).
-/
theorem getParentHashOf_canonicalize {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  getParentHashOf (canonicalize t li) = getParentHashOf t
:= by
  cases l with
  | zero =>
    simp only [canonicalize, canonicalizeUnmergedLeaves, unmergedLeavesOf_zero, unAdd_nil]
    rw [canonicalizeLeafSignature.eq_def]
    obtain ⟨_, ⟨c⟩⟩ := t
    cases c <;> rfl
  | succ l =>
    have := canonicalizeLeafSignature_succ (canonicalizeUnmergedLeaves t) li
    have := unAddP_succ t li (unAddUnmergedLeaf (unmergedLeavesOf t))
    rw [canonicalize, getParentHashOf_succ, getParentHashOf_succ]
    cases hc: t.nodeContent <;> cases hc': (unAdd t (unmergedLeavesOf t)).nodeContent <;>
      simp_all [canonicalizeUnmergedLeaves, unAdd]

theorem getParentHashOf_eq_of_equivalent {l1 l2: Nat} (t1: TreeSync Bytes tkt l1) (t2: TreeSync Bytes tkt l2) (li: Nat)
  (h: Equivalent t1 t2 li):
  getParentHashOf t1 = getParentHashOf t2
:= by
  obtain ⟨-, h⟩ := h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj h
  rw [heq_eq_eq] at h
  rw [← getParentHashOf_canonicalize t1 li, h, getParentHashOf_canonicalize]

/--
Port of `un_addP_eq_lemma`.
MLS*'s `filter_eq_lemma` is `List.filter_congr`.
-/
theorem unAddP_congr {l: Nat} (t: TreeSync Bytes tkt l) (p1 p2: Nat → Bool)
  (hok: unmergedLeavesOk t) (h: ∀ li, t.containsLeafIndex li → p1 li = p2 li):
  unAddP t p1 = unAddP t p2
:= by
  induction t using Tree.leftRightInduction with
  | leaf t => grind [unAddP_zero]
  | node t ihLeft ihRight =>
    have := unmergedLeavesOk_left_right t hok
    apply unAddP_eq_unAddP_succ (li := t.position)
    · rfl
    · grind
    · grind
    · rfl
    cases hc: t.nodeContent with
    | none => rfl
    | some c => grind [List.filter_congr, unmergedLeavesOk_content]

/-- Port of `unmerged_leaves_ok_subtree`. -/
theorem unmergedLeavesOk_of_isSubtreeOf {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp)
  (hok: unmergedLeavesOk p) (hsub: d.IsSubtreeOf p):
  unmergedLeavesOk d
:= by
  induction hsub <;> grind [unmergedLeavesOk_child_sibling]

/-- Port of `leaf_at_subtree_leaf`. -/
theorem leafAt_of_isSubtreeOf_zero {lc: Nat} (d: TreeSync Bytes tkt 0) (c: TreeSync Bytes tkt lc)
  (hsub: d.IsSubtreeOf c):
  leafAt c d.position = d.leafContent
:= by
  rw [hsub.leafAt_eq d.containsLeafIndex_position]
  grind [leafAt.eq_def]

/-- Port of `resolution_cap_subtree`. -/
theorem mem_resolution_iff_of_isSubtreeOf {ld lc: Nat} (d: TreeSync Bytes tkt ld) (c: TreeSync Bytes tkt lc)
  (x: NodeIndex) (hsub: d.IsSubtreeOf c) (hd: d.nodeIndex ∈ resolution c) (hok: unmergedLeavesOk c):
  (x ∈ resolution c ∧ d.containsNodeIndex x) ↔ x ∈ resolution d
:= by
  obtain ⟨xl, xp⟩ := x
  induction hsub with
  | refl => grind [containsNodeIndex_of_mem_resolution]
  | @child lc c hsub ih =>
    have := unmergedLeavesOk_child_sibling c d.position hok
    rw [mem_resolution_succ c d.position] at hd ⊢
    cases hc: c.nodeContent with
    | none =>
      have := containsNodeIndex_of_mem_resolution (c.sibling d.position)
      grind [Tree.containsNodeIndex, Tree.nodeIndex]
    | some content =>
      -- `d` is an unmerged leaf of `c`
      obtain rfl: ld = 0 := by grind [Tree.nodeIndex]
      have := unmergedLeavesOk_content c content hc hok
      have := leafAt_of_isSubtreeOf_zero d c (Tree.IsSubtreeOf.of_child hsub)
      grind [resolution_zero, Tree.containsNodeIndex, Tree.nodeIndex, Tree.containsLeafIndex, memUl_iff]

/-- Port of `non_blank_resolution_eq_unmerged_leaves_of`. -/
theorem mem_resolution_ofLeafIndex_iff {l: Nat} (t: TreeSync Bytes tkt l) (x: Nat) (hnb: nodeNotBlank t):
  NodeIndex.ofLeafIndex x ∈ resolution t ↔ t.nodeIndex = .ofLeafIndex x ∨ memUl x (unmergedLeavesOf t)
:= by
  cases l with
  | zero => grind [resolution_zero, unmergedLeavesOf_zero, nodeNotBlank_zero, memUl]
  | succ l => grind [resolution_succ, unmergedLeavesOf_eq, nodeNotBlank_succ, NodeIndex.ofLeafIndex]

/--
Port of `last_update_unmerged_leaves_eq`.
MLS* requires `node_not_blank p`, which is not needed.
-/
theorem memUl_unmergedLeavesOf_iff {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (x: Nat)
  (hph: nodeHasParentHash d) (hsub: d.IsSubtreeOf p) (hl: ld ≤ lp) (hlu: lastUpdateCorrect d p)
  (hok: unmergedLeavesOk p):
  memUl x (unmergedLeavesOf d) ↔ memUl x (unmergedLeavesOf p) ∧ d.containsLeafIndex x
:= by
  have hsubc := hsub.child_of_le hl
  have := mem_resolution_iff_of_isSubtreeOf d (p.child d.position) (.ofLeafIndex x) hsubc
  have := mem_resolution_ofLeafIndex_iff d x (nodeNotBlank_of_nodeHasParentHash d hph)
  have := unmergedLeavesOk_child_sibling p d.position hok
  rw [lastUpdateCorrect_iff] at hlu
  cases ld <;> grind [unmergedLeavesOf_zero, memUl, Tree.containsNodeIndex, NodeIndex.ofLeafIndex, Tree.nodeIndex]

/--
Port of `parent_hash_guarantee_theorem_step_for_d`.
MLS* requires `node_not_blank p`, which is not needed.
-/
theorem canonicalize_eq_of_lastUpdateCorrect {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1))
  (li: Nat) (hph: nodeHasParentHash d) (hsub: d.IsSubtreeOf p) (hl: ld ≤ lp) (hlu: lastUpdateCorrect d p)
  (hok: unmergedLeavesOk p):
  canonicalize d li = canonicalizeLeafSignature (unAdd d (unmergedLeavesOf p)) li
:= by
  rw [canonicalize, canonicalizeUnmergedLeaves, unAdd, unAdd]
  congr 1
  apply unAddP_congr d
  · exact unmergedLeavesOk_of_isSubtreeOf d p hok hsub
  · grind [unAddUnmergedLeaf, memUl_unmergedLeavesOf_iff]

/--
Port of `is_subtree_with_blanks_between`.
`d` is a subtree of `p`, and the nodes between them are blank, with empty siblings.
-/
inductive IsSubtreeWithBlanksBetween {ld: Nat} (d: TreeSync Bytes tkt ld): {lp: Nat} → TreeSync Bytes tkt lp → Prop
  | refl: IsSubtreeWithBlanksBetween d d
  | child {lp: Nat} (p: TreeSync Bytes tkt (lp+1)):
    p.nodeContent = none → isTreeEmpty (p.sibling d.position) →
    IsSubtreeWithBlanksBetween d (p.child d.position) → IsSubtreeWithBlanksBetween d p

theorem IsSubtreeWithBlanksBetween.le {ld lp: Nat} {d: TreeSync Bytes tkt ld} {p: TreeSync Bytes tkt lp}
  (h: IsSubtreeWithBlanksBetween d p):
  ld ≤ lp
:= by
  induction h <;> grind

/--
Port of `is_subtree_with_blanks_between_eq_lemma`.
MLS*'s `p1` and `p2` have the same position by their types.
-/
theorem IsSubtreeWithBlanksBetween.eq {ld lp: Nat} {d: TreeSync Bytes tkt ld} {p1 p2: TreeSync Bytes tkt lp}
  (h1: IsSubtreeWithBlanksBetween d p1) (h2: IsSubtreeWithBlanksBetween d p2) (hp: p1.position = p2.position):
  p1 = p2
:= by
  induction h1 with
  | refl =>
    cases h2 with
    | refl => rfl
    | child _ _ _ h2 => exfalso; grind [h2.le]
  | @child lp p1 hc1 hs1 h1 ih =>
    cases h2 with
    | refl => exfalso; grind [h1.le]
    | child _ hc2 hs2 h2 =>
      have := eq_of_isTreeEmpty (p1.sibling d.position) (p2.sibling d.position) (by grind) hs1 hs2
      apply Tree.ext_succ d.position <;> grind

/-- Port of `blank_sibling`. -/
theorem isTreeEmpty_unAdd {l: Nat} (t: TreeSync Bytes tkt l) (leaves: List UInt32)
  (h: ∀ x ∈ resolution t, x ∈ unmergedResolution leaves):
  isTreeEmpty (unAdd t leaves)
:= by
  induction t using Tree.leftRightInduction with
  | leaf t =>
    have := h t.nodeIndex
    rw [resolution_zero] at this
    rw [unAdd, unAddP_zero, isTreeEmpty_zero]
    grind [unAddUnmergedLeaf, Tree.nodeIndex]
  | node t ihLeft ihRight =>
    have := unAddP_succ t t.position (unAddUnmergedLeaf leaves)
    rw [resolution_succ] at h
    rw [unAdd] at ihLeft ihRight ⊢
    rw [isTreeEmpty_succ _ t.position]
    cases hc: t.nodeContent with
    | none =>
      have: (unAddP t (unAddUnmergedLeaf leaves)).nodeContent = none := by
        cases hc': (unAddP t (unAddUnmergedLeaf leaves)).nodeContent <;> simp_all
      grind
    | some c =>
      have := h t.nodeIndex (by simp [hc])
      exfalso
      grind [Tree.nodeIndex]

/-- Port of `un_add_myself` and `un_add_myself_aux`. -/
theorem filter_unAddUnmergedLeaf_self (l: List UInt32): l.filter (fun x => unAddUnmergedLeaf l x.toNat) = [] := by
  grind [List.filter_eq_nil_iff, unAddUnmergedLeaf, memUl_iff]

/-- Port of `is_subtree_with_blanks_between_d_p_aux`. -/
theorem isSubtreeWithBlanksBetween_unAdd {ld lc: Nat} (d: TreeSync Bytes tkt ld) (c: TreeSync Bytes tkt lc)
  (leaves: List UInt32) (li: Nat)
  (hsub: d.IsSubtreeOf c) (hres: ∀ x ∈ resolution c, x = d.nodeIndex ∨ x ∈ unmergedResolution leaves)
  (hok: unmergedLeavesOk c) (hli: d.containsLeafIndex li):
  IsSubtreeWithBlanksBetween (canonicalizeLeafSignature (unAdd d leaves) li)
    (canonicalizeLeafSignature (unAdd c leaves) li)
:= by
  induction hsub with
  | refl => exact .refl
  | @child lc c hsub ih =>
    have := unmergedLeavesOk_child_sibling c d.position hok
    have hu := unAddP_succ c li (unAddUnmergedLeaf leaves)
    have hcs := canonicalizeLeafSignature_succ (unAdd c leaves) li
    have hmem := mem_resolution_succ c li
    cases hc: c.nodeContent with
    | some content =>
      have := hres c.nodeIndex (by grind)
      exfalso
      grind [Tree.nodeIndex]
    | none =>
      apply IsSubtreeWithBlanksBetween.child
      · cases hc': (unAddP c (unAddUnmergedLeaf leaves)).nodeContent <;> simp_all [unAdd]
      · have := containsNodeIndex_of_mem_resolution (c.sibling li)
        have := isTreeEmpty_unAdd (c.sibling li) leaves (by grind [Tree.containsNodeIndex, Tree.nodeIndex])
        grind [unAdd]
      · grind [unAdd]

/--
Port of `is_subtree_with_blanks_between_d_p`.
This theorem can be viewed as a correctness theorem for `last_update_correct`,
that contains an ugly equation involving resolution.
A picture:
```
          P
         / \
       Cn   ...
       / \
     ...  Sn
     /
    C2
   / \
  C1  S2
 / \
D   S1
```
If D and P were updated at the same time according to the equation in `last_update_correct`,
then after canonicalizing P,
C1, C2, ..., Cn are blank nodes,
and S1, S2, ..., Sn are empty trees.
MLS* requires `node_not_blank p`, which is not needed.
-/
theorem isSubtreeWithBlanksBetween_of_lastUpdateCorrect {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt (lp+1)) (li: Nat)
  (hsub: d.IsSubtreeOf p) (hl: ld ≤ lp) (hlu: lastUpdateCorrect d p) (hok: unmergedLeavesOk p)
  (hli: d.containsLeafIndex li):
  IsSubtreeWithBlanksBetween (canonicalizeLeafSignature (unAdd d (unmergedLeavesOf p)) li)
    (canonicalizeLeafSignature (unAdd (p.child d.position) (unmergedLeavesOf p)) li)
:= by
  apply isSubtreeWithBlanksBetween_unAdd
  · exact hsub.child_of_le hl
  · grind [lastUpdateCorrect_iff]
  · exact (unmergedLeavesOk_child_sibling p d.position hok).1
  · exact hli

@[simp] theorem canonicalize_position {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat):
  (canonicalize t li).position = t.position
:= by
  simp [canonicalize, canonicalizeUnmergedLeaves, unAdd]

grind_pattern canonicalize_position => (canonicalize t li).position

/-- The canonicalization of a node, through the child / sibling view for `li`. -/
theorem canonicalize_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (li: Nat):
  (canonicalize t li).nodeContent.map (fun c => (c.content, c.parentHash)) =
    t.nodeContent.map (fun c => (c.content, c.parentHash)) ∧
  (canonicalize t li).nodeContent.map (·.unmergedLeaves.val) = t.nodeContent.map (fun _ => []) ∧
  (canonicalize t li).child li = canonicalizeLeafSignature (unAdd (t.child li) (unmergedLeavesOf t)) li ∧
  (canonicalize t li).sibling li = unAdd (t.sibling li) (unmergedLeavesOf t)
:= by
  have := canonicalizeLeafSignature_succ (canonicalizeUnmergedLeaves t) li
  have := unAddP_succ t li (unAddUnmergedLeaf (unmergedLeavesOf t))
  simp only [canonicalize, canonicalizeUnmergedLeaves, unAdd] at *
  cases hc: t.nodeContent <;> simp_all [unmergedLeavesOf_eq, filter_unAddUnmergedLeaf_self]

/--
The tree part of `parent_hash_guarantee_theorem_step`:
given two descendants `d1` and `d2` last updated at the same time as `p1` and `p2`,
if `d1` and `d2` are equivalent, and `p1` and `p2` have the same content and the same original sibling,
then `p1` and `p2` are equivalent.
-/
theorem equivalent_of_lastUpdateCorrect {ld1 ld2 lp1 lp2: Nat}
  (d1: TreeSync Bytes tkt ld1) (d2: TreeSync Bytes tkt ld2)
  (p1: TreeSync Bytes tkt (lp1+1)) (p2: TreeSync Bytes tkt (lp2+1)) (li: Nat)
  (heq: Equivalent d1 d2 li) (hl1: ld1 ≤ lp1) (hl2: ld2 ≤ lp2)
  (hph1: nodeHasParentHash d1) (hph2: nodeHasParentHash d2) (hsub1: d1.IsSubtreeOf p1) (hsub2: d2.IsSubtreeOf p2)
  (hlu1: lastUpdateCorrect d1 p1) (hlu2: lastUpdateCorrect d2 p2)
  (hok1: unmergedLeavesOk p1) (hok2: unmergedLeavesOk p2)
  (hc: p1.nodeContent.map (fun c => (c.content, c.parentHash)) = p2.nodeContent.map (fun c => (c.content, c.parentHash)))
  (hsib: (⟨lp1, unAdd (p1.sibling d1.position) (unmergedLeavesOf p1)⟩: (l: Nat) × TreeSync Bytes tkt l) =
    ⟨lp2, unAdd (p2.sibling d2.position) (unmergedLeavesOf p2)⟩):
  Equivalent p1 p2 li
:= by
  obtain ⟨hli, heq⟩ := heq
  obtain ⟨rfl, heq⟩ := Sigma.mk.inj heq
  obtain ⟨rfl, hsib⟩ := Sigma.mk.inj hsib
  rw [heq_eq_eq] at heq hsib
  have hdpos: d1.position = d2.position := by simpa using congrArg Tree.position heq
  have hli2: d2.containsLeafIndex li := by grind [Tree.containsLeafIndex]
  have hpp: p1.position = p2.position := by
    have := congrArg Tree.position hsib
    apply Tree.position_eq_of_sibling_position_eq p1 p2 d1.position <;> grind [unAdd]
  -- `p1` and `p2` have the same child, as both are `d1 = d2` with blanks between
  have hs1 := isSubtreeWithBlanksBetween_of_lastUpdateCorrect d1 p1 li hsub1 hl1 hlu1 hok1 hli
  have hs2 := isSubtreeWithBlanksBetween_of_lastUpdateCorrect d2 p2 li hsub2 hl2 hlu2 hok2 hli2
  rw [← canonicalize_eq_of_lastUpdateCorrect d1 p1 li hph1 hsub1 hl1 hlu1 hok1] at hs1
  rw [← canonicalize_eq_of_lastUpdateCorrect d2 p2 li hph2 hsub2 hl2 hlu2 hok2, ← heq] at hs2
  have := hs1.eq hs2 (by grind [unAdd])
  have := canonicalize_succ p1 li
  have := canonicalize_succ p2 li
  refine ⟨hsub1.mem hli, ?_⟩
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  apply Tree.ext_succ li
  · simp [hpp]
  · apply optionParentNode_ext
    · grind
    · cases hc1: p1.nodeContent <;> cases hc2: p2.nodeContent <;> grind
  · grind
  · grind

end BytesLike

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `parent_hash_guarantee_theorem_step`.
Induction step of the parent-hash integrity theorem.
Intuitively, it says that the parent-hash link lifts up in the tree the equivalence relation:
given two parent-hash links D1 ~> P1, and D2 ~> P2,
if D1 and D2 are equivalent then P1 and P2 are equivalent.
(modulo hash collision)

MLS* also takes `li`, which is not used.
This function computes the pair of bytes, its specification is `parentHashGuaranteeTheoremStep_spec`.
-/
def parentHashGuaranteeTheoremStep {ld1 ld2 lp1 lp2: Nat}
  (d1: TreeSync Bytes tkt ld1) (d2: TreeSync Bytes tkt ld2)
  (p1: TreeSync Bytes tkt (lp1+1)) (p2: TreeSync Bytes tkt (lp2+1))
  : Bytes × Bytes
:=
  match p1.nodeContent, p2.nodeContent with
  | some p1Content, some p2Content =>
    computeParentHashInj
      p1Content.content p1Content.parentHash.val (unAdd (p1.sibling d1.position) p1Content.unmergedLeaves.val)
      p2Content.content p2Content.parentHash.val (unAdd (p2.sibling d2.position) p2Content.unmergedLeaves.val)
  | _, _ => (BytesLike.empty, BytesLike.empty)

/--
Specification of `parentHashGuaranteeTheoremStep` (MLS*'s postcondition of `parent_hash_guarantee_theorem_step`).

The proof goes as follows:
Using parent-hash injectivity theorem `computeParentHashInj_spec`,
we get that the canonicalized siblings are equal and at the same position.
With the last-update equation, via `isSubtreeWithBlanksBetween_of_lastUpdateCorrect`,
we get that there are only blank nodes between D1 and P1 (resp. D2 and P2), after canonicalization.
Hence, with `IsSubtreeWithBlanksBetween.eq` we obtain that P1 and P2 are equal after canonicalization,
hence are equivalent.

MLS* also requires `node_has_parent_hash d1`, `node_has_parent_hash d2`, `node_not_blank p1` and `node_not_blank p2`,
which follow from the parent-hash links.
-/
theorem parentHashGuaranteeTheoremStep_spec {ld1 ld2 lp1 lp2: Nat}
  (d1: TreeSync Bytes tkt ld1) (d2: TreeSync Bytes tkt ld2)
  (p1: TreeSync Bytes tkt (lp1+1)) (p2: TreeSync Bytes tkt (lp2+1)) (li: Nat)
  (heq: Equivalent d1 d2 li) (hl1: ld1 ≤ lp1) (hl2: ld2 ≤ lp2)
  (hlink1: ParentHashLinkedP d1 p1) (hlink2: ParentHashLinkedP d2 p2)
  (hok1: unmergedLeavesOk p1) (hok2: unmergedLeavesOk p2):
  Equivalent p1 p2 li ∨ isHashCollision (parentHashGuaranteeTheoremStep d1 d2 p1 p2)
:= by
  obtain ⟨hsub1, hlinked1⟩ := hlink1
  obtain ⟨hsub2, hlinked2⟩ := hlink2
  simp only [parentHashLinked, Bool.and_eq_true] at hlinked1 hlinked2
  obtain ⟨pc1, ph1, hc1, hg1, hcomp1⟩ := (parentHashCorrect_iff d1 p1).mp hlinked1.1
  obtain ⟨pc2, ph2, hc2, hg2, hcomp2⟩ := (parentHashCorrect_iff d2 p2).mp hlinked2.1
  obtain rfl: ph1 = ph2 := by grind [getParentHashOf_eq_of_equivalent]
  rcases computeParentHashInj_spec _ _ _ _ _ _ _ hcomp1 hcomp2 with ⟨hcontent, hph, hsib⟩ | hcol
  · left
    apply equivalent_of_lastUpdateCorrect d1 d2 p1 p2 li heq <;> grind [unmergedLeavesOf_eq, nodeHasParentHash]
  · right
    simp [parentHashGuaranteeTheoremStep, hc1, hc2, hcol]

/-! ## Base case -/

/--
Port of `get_leaf_tree_tbs`.
MLS* requires `t.position < 2^32` and `node_not_blank t`; otherwise, the result is `none`.
-/
def getLeafTreeTbs (t: TreeSync Bytes tkt 0) (groupId: MlsBytes Bytes): Option Bytes :=
  match t.leafContent with
  | some ln => if t.position < 2^32 then some (getLeafTbs ln groupId t.position.toUInt32) else none
  | none => none

theorem leafContent_canonicalize (t: TreeSync Bytes tkt 0) (li: Nat):
  (canonicalize t li).leafContent = t.leafContent.map fun ln => { ln with signature := MlsBytes.empty }
:= by
  simp [canonicalize, canonicalizeUnmergedLeaves, unmergedLeavesOf_zero, unAdd_nil, leafContent_canonicalizeLeafSignature]

/--
Port of `equal_tbs_implies_equivalence`.
Base case of the parent-hash integrity theorem:
if the signature of two leaves covers the same content,
then their corresponding subtrees are equivalent.
MLS* requires `get_leaf_tree_tbs t1 group_id1 == get_leaf_tree_tbs t2 group_id2` (with their preconditions):
here, both are `some tbs`.
MLS* also requires `node_has_parent_hash t2`, which is not needed.
-/
theorem equivalent_of_getLeafTreeTbs (t1 t2: TreeSync Bytes tkt 0) (groupId1 groupId2: MlsBytes Bytes) (tbs: Bytes)
  (h1: getLeafTreeTbs t1 groupId1 = some tbs) (h2: getLeafTreeTbs t2 groupId2 = some tbs)
  (hph1: nodeHasParentHash t1):
  Equivalent t1 t2 t1.position ∧ groupId1 = groupId2
:= by
  unfold getLeafTreeTbs at h1 h2
  cases hln1: t1.leafContent with
  | none => simp [hln1] at h1
  | some ln1 =>
  cases hln2: t2.leafContent with
  | none => simp [hln2] at h2
  | some ln2 =>
  simp only [hln1, hln2, Option.ite_none_right_eq_some, Option.some.injEq] at h1 h2
  have hs1 := getParentHashOf_leaf t1 ln1 hln1
  obtain ⟨data1, sig1⟩ := ln1
  obtain ⟨data2, sig2⟩ := ln2
  have h := serializeNE_injective (LeafNodeTBS.mf tkt) (h1.2.trans h2.2.symm)
  simp only [LeafNodeTBS.mk.injEq] at h
  obtain ⟨rfl, hg, hi⟩ := h
  simp only [heq_eq_eq] at hg hi
  have hsrc: (data1.source == .update || data1.source == .commit) = true := by
    simp only [nodeHasParentHash] at hph1
    grind
  rw [StaticOption.mk_inj hsrc] at hg hi
  refine ⟨⟨t1.containsLeafIndex_position, ?_⟩, hg⟩
  rw [Tree.sigma_eq_zero]
  grind [leafContent_canonicalize]

/-! ## Induction -/

/-- Port of `one_tree`. -/
abbrev OneTree (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) := (l: Nat) × TreeSync Bytes tkt l

/-- Port of `tree_list`. -/
abbrev TreeList (Bytes: Type) [BytesLike Bytes] (tkt: TreeKEMTypes Bytes) := List (OneTree Bytes tkt)

/--
Port of `tree_parent_hash_linkedP`.
MLS*'s conditions `leaf_index_inside lp ip id`, `node_has_parent_hash d` and `node_not_blank p`
follow from `ParentHashLinkedP`.
-/
def TreeParentHashLinkedP: OneTree Bytes tkt → OneTree Bytes tkt → Prop
  | ⟨ld, d⟩, ⟨lp+1, p⟩ => ld ≤ lp ∧ ParentHashLinkedP d p ∧ unmergedLeavesOk p
  | _, ⟨0, _⟩ => False

/-- Port of `tree_list_is_parent_hash_linkedP`. -/
def TreeListIsParentHashLinkedP (tl: TreeList Bytes tkt): Prop :=
  ListChain TreeParentHashLinkedP tl

/--
Port of `tree_list_starts_with_tbs`.
MLS*'s condition `i < pow2 32` is in `getLeafTreeTbs`.
-/
def TreeListStartsWithTbs: TreeList Bytes tkt → Bytes → Prop
  | ⟨0, t⟩ :: _, tbs => nodeHasParentHash t ∧ ∃ groupId, getLeafTreeTbs t groupId = some tbs
  | _, _ => False

/-- Port of `tree_list_contains_leaf_index`. -/
def treeListContainsLeafIndex: TreeList Bytes tkt → Nat → Bool
  | [], _ => true
  | ⟨_, t⟩ :: _, li => t.containsLeafIndex li

/--
Port of `tree_list_ends_at_root`.
MLS* defines it by recursion on the list.
-/
def TreeListEndsAtRoot (tl: TreeList Bytes tkt): Prop :=
  ∃ x ∈ tl.getLast?, getParentHashOf x.2 = some rootParentHash

/--
Port of `get_leaf_index_from_tree_list`.
MLS* requires `Cons? tl`; otherwise, the result is `0`.
-/
def getLeafIndexFromTreeList: TreeList Bytes tkt → Nat
  | [] => 0
  | ⟨_, t⟩ :: _ => t.position

/-- Port of `first_tree_equivalent`. -/
def FirstTreeEquivalent: TreeList Bytes tkt → TreeList Bytes tkt → Nat → Prop
  | ⟨_, t1⟩ :: _, ⟨_, t2⟩ :: _, li => Equivalent t1 t2 li
  | _, _, _ => False

/-- Port of `tree_list_equivalent_subset`. -/
def TreeListEquivalentSubset: TreeList Bytes tkt → TreeList Bytes tkt → Nat → Prop
  | [], _, _ => True
  | _ :: _, [], _ => False
  | ⟨_, t1⟩ :: tail1, ⟨_, t2⟩ :: tail2, li => Equivalent t1 t2 li ∧ TreeListEquivalentSubset tail1 tail2 li

/-- Port of `tree_is_canonicalized`. -/
def TreeIsCanonicalized (li: Nat) (x: OneTree Bytes tkt): Prop :=
  x.2.containsLeafIndex li ∧ isCanonicalized x.2 li

/-- Port of `tree_list_is_canonicalized`. -/
def TreeListIsCanonicalized (li: Nat) (tl: TreeList Bytes tkt): Prop :=
  ∀ x ∈ tl, TreeIsCanonicalized li x

/--
Port of `parent_hash_guarantee_theorem_aux`.
Instead of testing whether `p1` and `p2` are equivalent (which needs decidable equality on trees),
the induction goes on when the step does not return a hash collision.
This function computes the pair of bytes, its specification is `parentHashGuaranteeTheoremAux_spec`.
-/
def parentHashGuaranteeTheoremAux: TreeList Bytes tkt → TreeList Bytes tkt → Nat → Bytes × Bytes
  | ⟨_, d1⟩ :: ⟨lp1+1, p1⟩ :: tail1, ⟨_, d2⟩ :: ⟨lp2+1, p2⟩ :: tail2, li =>
    let stepCollision := parentHashGuaranteeTheoremStep d1 d2 p1 p2
    if isHashCollision stepCollision then
      stepCollision
    else
      parentHashGuaranteeTheoremAux (⟨lp1+1, p1⟩ :: tail1) (⟨lp2+1, p2⟩ :: tail2) li
  | _, _, _ => (BytesLike.empty, BytesLike.empty)

/--
Specification of `parentHashGuaranteeTheoremAux` (MLS*'s postcondition of `parent_hash_guarantee_theorem_aux`).
MLS* also requires `tree_list_contains_leaf_index tl1 li`, which follows from `FirstTreeEquivalent tl1 tl2 li`.
-/
theorem parentHashGuaranteeTheoremAux_spec (tl1 tl2: TreeList Bytes tkt) (li: Nat)
  (h1: TreeListIsParentHashLinkedP tl1) (h2: TreeListIsParentHashLinkedP tl2)
  (hfirst: FirstTreeEquivalent tl1 tl2 li) (hroot: TreeListEndsAtRoot tl2):
  TreeListEquivalentSubset tl1 tl2 li ∨ isHashCollision (parentHashGuaranteeTheoremAux tl1 tl2 li)
:= by
  induction tl1 generalizing tl2 with
  | nil => simp [FirstTreeEquivalent] at hfirst
  | cons d1 tail1 ih =>
    obtain ⟨ld1, d1⟩ := d1
    rcases tl2 with _ | ⟨⟨ld2, d2⟩, tail2⟩
    · simp [FirstTreeEquivalent] at hfirst
    rcases tail1 with _ | ⟨⟨_ | lp1, p1⟩, tail1⟩
    · -- `tl1` has one tree: easy post-condition with `FirstTreeEquivalent tl1 tl2 li`
      left
      simp_all [FirstTreeEquivalent, TreeListEquivalentSubset]
    · simp [TreeListIsParentHashLinkedP, ListChain, TreeParentHashLinkedP] at h1
    obtain ⟨⟨hl1, hlink1, hok1⟩, h1⟩ := h1
    simp only [FirstTreeEquivalent] at hfirst
    rcases tail2 with _ | ⟨⟨_ | lp2, p2⟩, tail2⟩
    · -- Not possible with `TreeListEndsAtRoot tl2`: the parent hash of `d1` is a hash, hence not empty
      exfalso
      obtain ⟨pc, ph, -, hph, hcomp⟩ := (parentHashCorrect_iff d1 p1).mp (by grind [ParentHashLinkedP, parentHashLinked])
      have := getParentHashOf_eq_of_equivalent d1 d2 li hfirst
      obtain ⟨hashInput, -, h⟩ := (computeParentHash_eq_success _ _ _ _).mp hcomp
      have := CryptoBytes.hashHash_ne_empty (serializeNE (ParentHashInput.mf tkt) hashInput)
      grind [TreeListEndsAtRoot, rootParentHash]
    · simp [TreeListIsParentHashLinkedP, ListChain, TreeParentHashLinkedP] at h2
    obtain ⟨⟨hl2, hlink2, hok2⟩, h2⟩ := h2
    have hstep := parentHashGuaranteeTheoremStep_spec d1 d2 p1 p2 li hfirst hl1 hl2 hlink1 hlink2 hok1 hok2
    simp only [parentHashGuaranteeTheoremAux]
    split
    · grind
    · have := ih _ h1 h2 (by grind [FirstTreeEquivalent]) (by simpa [TreeListEndsAtRoot] using hroot)
      grind [TreeListEquivalentSubset]

/--
Port of `parent_hash_guarantee_theorem`.
The full parent-hash integrity theorem:
given two list of trees `tl1` and `tl2`, if:
- they are both parent-hash linked (i.e., a tree in a list in parent-hash linked to the next one in the list)
- their first trees are leaves with the same signature content
- one of them (`tl2`) ends at the root, i.e. the parent-hash stored in the root of the last tree is empty
Then their trees are pointwise equivalent.
(modulo hash collision)

From where do you obtain the tree lists?
- `tl1` comes from the parent hash invariant (via `exists_treeList_of_parentHashInvariant`),
- `tl2` comes from the signature predicate (via `pathToTreeList`).

MLS* also takes `tbs`, which is only used in the specification,
and uses the leaf index of `tl2` (equal to the one of `tl1`).
This function computes the pair of bytes, its specification is `parentHashGuaranteeTheorem_spec`.
-/
def parentHashGuaranteeTheorem (tl1 tl2: TreeList Bytes tkt): Bytes × Bytes :=
  parentHashGuaranteeTheoremAux tl1 tl2 (getLeafIndexFromTreeList tl1)

/-- Specification of `parentHashGuaranteeTheorem` (MLS*'s postcondition of `parent_hash_guarantee_theorem`). -/
theorem parentHashGuaranteeTheorem_spec (tl1 tl2: TreeList Bytes tkt) (tbs: Bytes)
  (h1: TreeListIsParentHashLinkedP tl1) (h2: TreeListIsParentHashLinkedP tl2)
  (hs1: TreeListStartsWithTbs tl1 tbs) (hs2: TreeListStartsWithTbs tl2 tbs) (hroot: TreeListEndsAtRoot tl2):
  TreeListEquivalentSubset tl1 tl2 (getLeafIndexFromTreeList tl1) ∨ isHashCollision (parentHashGuaranteeTheorem tl1 tl2)
:= by
  apply parentHashGuaranteeTheoremAux_spec tl1 tl2 _ h1 h2 _ hroot
  match tl1, tl2, hs1, hs2 with
  | ⟨0, t1⟩ :: _, ⟨0, t2⟩ :: _, ⟨hph1, groupId1, hg1⟩, ⟨_, groupId2, hg2⟩ =>
    exact (equivalent_of_getLeafTreeTbs t1 t2 groupId1 groupId2 tbs hg1 hg2 hph1).1

/-! ## Tree list from the parent hash invariant -/

/-- Port of `parent_hash_invariant_subtree`. -/
theorem parentHashInvariant_of_isSubtreeOf {ld lp: Nat} (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp)
  (hinv: parentHashInvariant p) (hsub: d.IsSubtreeOf p):
  parentHashInvariant d
:= by
  induction hsub <;> grind [parentHashInvariant_succ]

/--
Port of `parent_hash_invariant_to_tree_list` and `parent_hash_invariant_to_tree_list_rev`,
with `compute_parent_hash_link` and `compute_parent_hash_link_aux`:
these functions compute the witness of this existential
(the parent-hash link of a node is given by `ParentHashInvariantP`).
Given a tree that satisfy the parent-hash invariant,
there is a list of trees that are parent-hash linked, start at a leaf, and end at this tree.
-/
theorem exists_treeList_of_parentHashInvariant {l: Nat} (t: TreeSync Bytes tkt l)
  (hph: nodeHasParentHash t) (hok: unmergedLeavesOk t) (hinv: parentHashInvariant t):
  ∃ tl: TreeList Bytes tkt,
    TreeListIsParentHashLinkedP tl ∧ tl.getLast? = some ⟨l, t⟩ ∧ tl.head?.map (·.1) = some 0
:= by
  cases l with
  | zero =>
    refine ⟨[⟨0, t⟩], ?_⟩
    simp [TreeListIsParentHashLinkedP, ListChain]
  | succ l =>
    have hinvP := (parentHashInvariantP_succ t 0).mp (parentHashInvariantP_of_parentHashInvariant t hinv)
    obtain ⟨ld, d, hl, hphd, hlink⟩ := hinvP.1 (nodeNotBlank_of_nodeHasParentHash t hph)
    obtain ⟨tl, h1, h2, h3⟩ := exists_treeList_of_parentHashInvariant d hphd
      (unmergedLeavesOk_of_isSubtreeOf d t hok hlink.1) (parentHashInvariant_of_isSubtreeOf d t hinv hlink.1)
    refine ⟨tl ++ [⟨l+1, t⟩], ?_⟩
    refine ⟨ListChain.append_singleton h1 ?_, by simp, ?_⟩
    · grind [TreeParentHashLinkedP]
    · cases tl <;> simp_all
termination_by l
decreasing_by omega

/-! ## Path to tree list -/

/--
Port of `path_to_tree_list_aux`.
Given a tree and a path, compute the trees obtained by applying the path,
at each non-blank node of the path and at its leaf, from the root to the leaf.
MLS* jumps from one non-blank node of the path to the next one
with `find_node_and_path_parent_hash_link` and `find_node_and_path_parent_hash_link_aux`,
and starts at the first non-blank node (in `path_to_tree_list`).
This function goes through the path one node at a time (as MLS*'s `path_to_tree_list_pre_aux`),
and computes the same list.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`) and `Success? (apply_path_aux t p parent_parent_hash)`;
otherwise, the function follows the path to the leaf closest to `li`, or fails.
-/
def pathToTreeListAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  : Result (TreeList Bytes tkt)
:=
  match t.intoChildSiblingView li, p with
  | .leaf _ position, .leaf ln => pure [⟨0, (ChildSiblingView.leaf (some ln) position).pack⟩]
  | .node content child sibling, .node optExtContent pNext => do
    let (_, newParentParentHash) ← computeNewNpAndPh optExtContent sibling parentParentHash
    let tailTl ← pathToTreeListAux child li pNext newParentParentHash
    match optExtContent with
    | none => pure tailTl
    | some _ =>
      let t' ← applyPathAux (ChildSiblingView.node content child sibling).pack li (.node optExtContent pNext) parentParentHash
      pure (⟨_, t'⟩ :: tailTl)
termination_by l

/--
Port of `path_to_tree_list`.
Given a tree and a path,
compute a list of trees that are parent-hash linked,
start at the leaf of the path,
and end at the root.
(Proved by `pathToTreeList_spec`.)
MLS* requires `li: leaf_index l 0` and `Success? (apply_path t p)`;
otherwise, the function follows the path to the leaf closest to `li`, or fails.
-/
def pathToTreeList {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l): Result (TreeList Bytes tkt) :=
  List.reverse <$> pathToTreeListAux t li p rootParentHash.val

theorem pathToTreeListAux_zero (t: TreeSync Bytes tkt 0) (li: Nat) (ln: LeafNode Bytes tkt) (parentParentHash: Bytes):
  pathToTreeListAux t li (.leaf ln) parentParentHash = pure [⟨0, (ChildSiblingView.leaf (some ln) t.position).pack⟩]
:= by
  rw [pathToTreeListAux.eq_def]
  obtain ⟨_, ⟨_⟩⟩ := t
  rfl

theorem pathToTreeListAux_node {l: Nat}
  (t: TreeSync Bytes tkt (l+1)) (li: Nat) (optExtContent: Option tkt.NodeContent) (pNext: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (tl: TreeList Bytes tkt)
  (h: pathToTreeListAux t li (.node optExtContent pNext) parentParentHash = .success tl):
  ∃ newOptContent newParentParentHash tailTl,
    computeNewNpAndPh optExtContent (t.sibling li) parentParentHash = .success (newOptContent, newParentParentHash) ∧
    pathToTreeListAux (t.child li) li pNext newParentParentHash = .success tailTl ∧
    match optExtContent with
    | none => tl = tailTl
    | some _ =>
      ∃ t', applyPathAux t li (.node optExtContent pNext) parentParentHash = .success t' ∧ tl = ⟨_, t'⟩ :: tailTl
:= by
  unfold pathToTreeListAux at h
  simp at h
  cases optExtContent <;> grind [Result.pure_eq_success, Result.map_eq_success]

/--
Port of `is_canonicalized_apply_path_aux`.
MLS* requires `li: leaf_index l i`: here, `t.containsLeafIndex li`.
-/
theorem isCanonicalized_applyPathAux {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (t': TreeSync Bytes tkt l) (h: applyPathAux t li p parentParentHash = .success t')
  (hli: t.containsLeafIndex li) (hsig: p.getPathLeaf.signature = MlsBytes.empty):
  isCanonicalized t' li
:= by
  have := leafAt_applyPathAux t li p parentParentHash li t' h hli hli
  have hul: unmergedLeavesOf t' = [] := by
    cases l with
    | zero => exact unmergedLeavesOf_zero t'
    | succ l =>
      obtain ⟨newOptContent, newChild, _, _, hchild, rfl, hul⟩ := applyPathAux_succ t li p parentParentHash t' h
      have := applyPathAux_position _ _ _ _ _ hchild
      cases newOptContent <;> simp_all [unmergedLeavesOf_eq]
  simp_all [isCanonicalized, isUnmergedLeavesCanonicalized, isLeafSignatureCanonicalized, MlsBytes.empty,
    BytesLike.recognizeEmpty_correct]

/--
Induction following successful computations of `pathToTreeListAux` and `applyPathAux`,
with one case per kind of node of the path.
-/
@[elab_as_elim]
theorem pathToTreeListAux_induction (li: Nat)
  {motive: (l: Nat) → (t: TreeSync Bytes tkt l) → (p: PathSync Bytes tkt l) → (parentParentHash: Bytes) →
    (tl: TreeList Bytes tkt) → (t': TreeSync Bytes tkt l) →
    pathToTreeListAux t li p parentParentHash = .success tl → applyPathAux t li p parentParentHash = .success t' → Prop}
  (leaf: ∀ (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt) (parentParentHash: Bytes) (h ht'),
    motive 0 t (.leaf ln) parentParentHash
      [⟨0, (ChildSiblingView.leaf (some ln) t.position).pack⟩] (ChildSiblingView.leaf (some ln) t.position).pack h ht')
  (blank: ∀ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (pNext: PathSync Bytes tkt l) (parentParentHash: Bytes)
    (tailTl: TreeList Bytes tkt) (newChild: TreeSync Bytes tkt l) (htail hchild h ht'),
    computeNewNpAndPh none (t.sibling li) parentParentHash = .success (none, parentParentHash) →
    motive l (t.child li) pNext parentParentHash tailTl newChild htail hchild →
    motive (l+1) t (.node none pNext) parentParentHash
      tailTl (ChildSiblingView.node none newChild (t.sibling li)).pack h ht')
  (nonBlank: ∀ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (extContent: tkt.NodeContent) (pNext: PathSync Bytes tkt l)
    (parentParentHash: Bytes) (newContent: ParentNode Bytes tkt) (newParentParentHash: Bytes)
    (tailTl: TreeList Bytes tkt) (newChild: TreeSync Bytes tkt l) (htail hchild h ht'),
    computeNewNpAndPh (some extContent) (t.sibling li) parentParentHash = .success (some newContent, newParentParentHash) →
    motive l (t.child li) pNext newParentParentHash tailTl newChild htail hchild →
    motive (l+1) t (.node (some extContent) pNext) parentParentHash
      (⟨l+1, (ChildSiblingView.node (some newContent) newChild (t.sibling li)).pack⟩ :: tailTl)
      (ChildSiblingView.node (some newContent) newChild (t.sibling li)).pack h ht'):
  ∀ {l: Nat} (t: TreeSync Bytes tkt l) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
    (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l) (h ht'), motive l t p parentParentHash tl t' h ht'
| 0, t, .leaf ln, parentParentHash, tl, t', h, ht' => by
  obtain rfl := applyPathAux_zero t li ln parentParentHash t' ht'
  have htl: [⟨0, (ChildSiblingView.leaf (some ln) t.position).pack⟩] = tl := by
    rwa [pathToTreeListAux_zero, Result.pure_eq_success] at h
  subst htl
  apply leaf
| _+1, t, .node optExtContent pNext, parentParentHash, tl, t', h, ht' => by
  obtain ⟨newOptContent, newParentParentHash, newChild, hcn, hchild, rfl⟩ :=
    applyPathAux_node t li optExtContent pNext parentParentHash t' ht'
  obtain ⟨_, _, tailTl, hcn', htail, htl⟩ := pathToTreeListAux_node t li optExtContent pNext parentParentHash tl h
  obtain ⟨rfl, rfl⟩: newOptContent = _ ∧ newParentParentHash = _ := by simpa [hcn] using hcn'
  have hspec := computeNewNpAndPh_spec _ _ _ _ _ hcn
  have ih := pathToTreeListAux_induction li leaf blank nonBlank (t.child li) pNext _ tailTl newChild htail hchild
  cases optExtContent with
  | none =>
    obtain ⟨rfl, rfl⟩ := hspec
    have htl: tailTl = tl := htl.symm
    subst htl
    exact blank t pNext _ tailTl newChild htail hchild h ht' hcn ih
  | some extContent =>
    obtain ⟨newContent, rfl, -⟩ := hspec
    obtain ⟨t'', ht'', rfl⟩ := htl
    have : (ChildSiblingView.node (some newContent) newChild (t.sibling li)).pack = t'' := by
      rw [ht''] at ht'; simpa using ht'.symm
    subst this
    exact nonBlank t extContent pNext _ newContent _ tailTl newChild htail hchild h ht' hcn ih

/--
Port of `find_node_and_path_parent_hash_link_aux_lemma`, `find_node_and_path_parent_hash_link_lemma`
and `find_parent_hash_link_misc_properties`:
the first tree `d` of the list is the one computed by `find_parent_hash_link` (see `exists_subtree_applyPathAux`).
MLS* requires `path_node_not_blank p`, which is not needed.
-/
theorem pathToTreeListAux_head {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: pathToTreeListAux t li p parentParentHash = .success tl) (ht': applyPathAux t li p parentParentHash = .success t')
  (hvalid: pathIsParentHashValidAux t li p parentParentHash) (hfilter: pathIsFilterValid t li p):
  ∃ (ld: Nat) (d: TreeSync Bytes tkt ld) (tail: TreeList Bytes tkt),
    tl = ⟨ld, d⟩ :: tail ∧ ld ≤ l ∧ d.IsSubtreeOf t' ∧
    (getParentHashOf d).map (·.val) = some parentParentHash ∧ resolution t' = [d.nodeIndex]
:= by
  induction t, p, parentParentHash, tl, t', h, ht' using pathToTreeListAux_induction li with
  | leaf t ln parentParentHash =>
    rw [pathIsParentHashValidAux_leaf] at hvalid
    have := getParentHashOf_leaf ((ChildSiblingView.leaf (some ln) t.position).pack: TreeSync Bytes tkt 0) ln (by simp)
    split at hvalid
    · refine ⟨0, (ChildSiblingView.leaf (some ln) t.position).pack, [], ?_⟩
      grind [resolution_zero]
    · exfalso
      grind
  | blank t pNext parentParentHash _ _ _ _ _ _ hcn ih =>
    -- the head is the one of the child
    rw [pathIsParentHashValidAux_node t li none pNext parentParentHash _ _ hcn] at hvalid
    rw [pathIsFilterValid_node, Bool.and_eq_true, Bool.or_eq_true] at hfilter
    obtain ⟨ld, d, tail, rfl, hl, hsub, hgph, hres⟩ := ih hvalid hfilter.2
    refine ⟨ld, d, tail, ?_⟩
    rw [resolution_succ_of_resolution_sibling _ li (by grind) (by grind [resolution_eq_nil_of_isTreeEmpty])]
    grind
  | nonBlank t _ _ _ newContent _ tailTl newChild _ _ _ _ hcn =>
    -- the head is the node itself
    have := computeNewNpAndPh_spec _ _ _ _ _ hcn
    refine ⟨_, (ChildSiblingView.node (some newContent) newChild (t.sibling li)).pack, tailTl, ?_⟩
    grind [getParentHashOf_succ, resolution_succ, unmergedResolution]

/--
Port of the first part of `path_to_tree_list_aux_lemma`:
consecutive trees of the list are parent-hash linked.
-/
theorem pathToTreeListAux_linked {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: pathToTreeListAux t li p parentParentHash = .success tl) (ht': applyPathAux t li p parentParentHash = .success t')
  (hvalid: pathIsParentHashValidAux t li p parentParentHash) (hfilter: pathIsFilterValid t li p)
  (hok: unmergedLeavesOk t):
  ListChain (flip TreeParentHashLinkedP) tl
:= by
  induction t, p, parentParentHash, tl, t', h, ht' using pathToTreeListAux_induction li with
  | leaf => trivial
  | blank t pNext parentParentHash _ _ _ _ _ _ hcn ih =>
    rw [pathIsParentHashValidAux_node t li none pNext parentParentHash _ _ hcn] at hvalid
    rw [pathIsFilterValid_node, Bool.and_eq_true] at hfilter
    exact ih hvalid hfilter.2 (unmergedLeavesOk_child_sibling t li hok).1
  | nonBlank t extContent pNext parentParentHash _ newParentParentHash tailTl newChild htail hchild _ ht' hcn ih =>
    -- the node is parent-hash linked to the head of the list of the child
    rw [pathIsParentHashValidAux_node t li _ pNext parentParentHash _ _ hcn] at hvalid
    rw [pathIsFilterValid_node, Bool.and_eq_true] at hfilter
    have hchain := ih hvalid hfilter.2 (unmergedLeavesOk_child_sibling t li hok).1
    obtain ⟨ld, d, tail, rfl, hl, hsub, hgph, hres⟩ :=
      pathToTreeListAux_head _ li pNext _ tailTl newChild htail hchild hvalid hfilter.2
    obtain ⟨ph, hph', rfl⟩: ∃ ph, getParentHashOf d = some ph ∧ ph.val = newParentParentHash := by
      cases hg: getParentHashOf d <;> simp_all
    have := computeNewNpAndPh_spec _ _ _ _ _ hcn
    refine ⟨⟨by omega, ?_, unmergedLeavesOk_applyPathAux t li _ parentParentHash _ ht' hok⟩, hchain⟩
    apply parentHashLinkedP_applyPathAux t li extContent pNext parentParentHash _ d ph ht' <;> grind

/--
Port of the second part of `path_to_tree_list_aux_lemma`.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`).
-/
theorem pathToTreeListAux_canonicalized {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: pathToTreeListAux t li p parentParentHash = .success tl) (ht': applyPathAux t li p parentParentHash = .success t')
  (hli: t.containsLeafIndex li) (hsig: p.getPathLeaf.signature = MlsBytes.empty):
  TreeListIsCanonicalized li tl
:= by
  induction t, p, parentParentHash, tl, t', h, ht' using pathToTreeListAux_induction li with
  | leaf t _ parentParentHash _ ht' =>
    have := isCanonicalized_applyPathAux t li _ parentParentHash _ ht' hli hsig
    grind [TreeListIsCanonicalized, TreeIsCanonicalized, Tree.containsLeafIndex]
  | blank t _ _ _ _ _ _ _ _ _ ih =>
    exact ih (t.mem_child_self hli) hsig
  | nonBlank t _ _ parentParentHash _ _ _ _ _ _ _ ht' _ ih =>
    have := ih (t.mem_child_self hli) hsig
    have := isCanonicalized_applyPathAux t li _ parentParentHash _ ht' hli hsig
    grind [TreeListIsCanonicalized, TreeIsCanonicalized, Tree.containsLeafIndex]

/--
Port of the last part of `path_to_tree_list_aux_lemma`: the list ends at the leaf of the path.
MLS* requires `li: leaf_index l i` (i.e. `t.containsLeafIndex li`).
-/
theorem pathToTreeListAux_getLast? {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: pathToTreeListAux t li p parentParentHash = .success tl) (ht': applyPathAux t li p parentParentHash = .success t')
  (hli: t.containsLeafIndex li):
  tl.getLast? = some ⟨0, (ChildSiblingView.leaf (some p.getPathLeaf) li).pack⟩
:= by
  induction t, p, parentParentHash, tl, t', h, ht' using pathToTreeListAux_induction li with
  | leaf t =>
    have := eq_of_containsLeafIndex_zero hli t.containsLeafIndex_position
    grind [Path.getPathLeaf]
  | blank =>
    grind [Path.getPathLeaf]
  | nonBlank t _ _ _ _ _ tailTl _ _ _ _ _ _ ih =>
    have := ih (t.mem_child_self hli)
    cases tailTl <;> simp_all [Path.getPathLeaf]

/--
Port of `path_to_tree_list_lemma` (with `path_to_tree_list_aux_lemma`).
MLS* requires `li: leaf_index l 0` (i.e. `t.containsLeafIndex li`) and `Success? (apply_path t p)`.
-/
theorem pathToTreeList_spec {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (tl: TreeList Bytes tkt) (t': TreeSync Bytes tkt l)
  (h: pathToTreeList t li p = .success tl) (ht': applyPath t li p = .success t')
  (hvalid: pathIsParentHashValid t li p) (hfilter: pathIsFilterValid t li p) (hok: unmergedLeavesOk t)
  (hli: t.containsLeafIndex li) (hsig: p.getPathLeaf.signature = MlsBytes.empty):
  TreeListIsParentHashLinkedP tl ∧ TreeListEndsAtRoot tl ∧ TreeListIsCanonicalized li tl ∧
    tl.head? = some ⟨0, (ChildSiblingView.leaf (some p.getPathLeaf) li).pack⟩
:= by
  obtain ⟨revTl, hrev, rfl⟩ := (Result.map_eq_success _ _ _).mp h
  obtain ⟨ld, d, tail, rfl, -, -, hgph, -⟩ := pathToTreeListAux_head t li p _ _ t' hrev ht' hvalid hfilter
  have hchain := pathToTreeListAux_linked t li p _ _ t' hrev ht' hvalid hfilter hok
  have hcanon := pathToTreeListAux_canonicalized t li p _ _ t' hrev ht' hli hsig
  have hlast := pathToTreeListAux_getLast? t li p _ _ t' hrev ht' hli
  refine ⟨hchain.reverse, ?_, fun x hx => hcanon x (List.mem_reverse.mp hx), by rw [List.head?_reverse]; exact hlast⟩
  refine ⟨⟨ld, d⟩, by simp, ?_⟩
  cases hg: getParentHashOf d <;> grind

/--
Port of `path_to_tree_list_pre_aux`.
The predicate `pre` holds on all the trees of `pathToTreeListAux t li p parentParentHash`.
MLS* defines it by recursion on the path, following `path_to_tree_list_aux`
(proofs by induction on the path go through `pathToTreeListAux_node` instead).
MLS* requires `li: leaf_index l i` and `Success? (apply_path_aux t p parent_parent_hash)`;
otherwise, the predicate holds when `pathToTreeListAux` fails.
-/
def PathToTreeListPreAux (pre: OneTree Bytes tkt → Prop) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes): Prop
:=
  ∀ tl, pathToTreeListAux t li p parentParentHash = .success tl → ∀ x ∈ tl, pre x

/-- Port of `path_to_tree_list_pre`. -/
def PathToTreeListPre (pre: OneTree Bytes tkt → Prop) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l): Prop
:=
  PathToTreeListPreAux pre t li p rootParentHash.val

/-- Port of `path_to_tree_list_pre_aux_lemma`. -/
theorem pathToTreeListPreAux_iff (pre: OneTree Bytes tkt → Prop) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes) (tl: TreeList Bytes tkt)
  (h: pathToTreeListAux t li p parentParentHash = .success tl):
  PathToTreeListPreAux pre t li p parentParentHash ↔ ∀ x ∈ tl, pre x
:= by
  grind [PathToTreeListPreAux]

/-- Port of `path_to_tree_list_pre_lemma`. -/
theorem pathToTreeListPre_iff (pre: OneTree Bytes tkt → Prop) {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (tl: TreeList Bytes tkt)
  (h: pathToTreeList t li p = .success tl):
  PathToTreeListPre pre t li p ↔ ∀ x ∈ tl, pre x
:= by
  obtain ⟨revTl, hrev, rfl⟩ := (Result.map_eq_success _ _ _).mp h
  simp [PathToTreeListPre, pathToTreeListPreAux_iff pre t li p _ revTl hrev]

/-- Port of `path_to_tree_list_pre_aux_weaken`. -/
theorem PathToTreeListPreAux.weaken {preStrong preWeak: OneTree Bytes tkt → Prop} {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes)
  (h: PathToTreeListPreAux preStrong t li p parentParentHash) (himp: ∀ x, preStrong x → preWeak x):
  PathToTreeListPreAux preWeak t li p parentParentHash
:= by
  grind [PathToTreeListPreAux]

/-- Port of `path_to_tree_list_pre_weaken`. -/
theorem PathToTreeListPre.weaken {preStrong preWeak: OneTree Bytes tkt → Prop} {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (h: PathToTreeListPre preStrong t li p) (himp: ∀ x, preStrong x → preWeak x):
  PathToTreeListPre preWeak t li p
:=
  PathToTreeListPreAux.weaken t li p _ h himp

end CryptoBytes

end Mls.TreeSync
