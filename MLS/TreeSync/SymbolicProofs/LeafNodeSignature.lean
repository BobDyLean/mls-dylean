module

public import MLS.TreeSync.SymbolicSpec.LeafNodeSignature
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.TreeSync.SymbolicProofs.IsWellFormed
public import MLS.TreeSync.Proofs.ParentHashGuarantees
public import MLS.TreeSync.Proofs.API
public import MLS.TreeSync.Proofs.Invariants.ValidLeaves
public import MLS.Common.SymbolicProofs.Crypto.Derived.SignWithLabel
import all MLS.TreeSync.SymbolicSpec.LeafNodeSignature

/-!
Port of the predicates and proofs of `MLS.TreeSync.Symbolic.LeafNodeSignature`:
the signature predicate of leaf nodes, the guarantees obtained when verifying the signatures of a tree,
and the proofs that the signatures computed by TreeSync satisfy the predicate.

Port-specific differences:
- The events of the predicate are on the erased trace (`tr.erase`), as in DyLean's examples.
- The cases of `leaf_node_sign_pred` on the source of the leaf use `if`s, as the group identifier and the leaf index
  (static options) are read with a proof that the source is `update` or `commit`.
- DY*'s `is_corrupt tr (signature_key_label …)` is `(signatureKeyLabel …).isCorrupt tr.erase`.
- MLS*'s `get_authentifier_index` is a proof-only function naming a witness: it is the predicate `IsAuthentifierIndex`,
  whose witnesses exist by `exists_isAuthentifierIndex`; the lemmas about the authentifier take its index as an argument.
- MLS* uses `Some?.v (leaf_at t li)` and `Some?.v (credential_to_principal …)`:
  the lemmas take the leaf node with a hypothesis `leafAt t li = some ln`,
  and conclude with the existence of the principal (`credentialToPrincipal … = some authentifier`).
- The trees and tokens of `state_implies_event` have positions related by a hypothesis
  (MLS* shares the index `i`), and the TreeSync invariants of the state (MLS*'s `treesync_valid`) are `st.TreeValid`.
-/

namespace MLS.TreeSync

open Comparse
open DY
open DySlop DySlop.Signature DySlop.SplitFunction
open MLS

theorem StaticOption.get_mk' {b: Bool} {a: Type} (x: a) (h: b = true):
  (StaticOption.mk x: StaticOption b a).get h = x
:= by
  subst h
  rfl

/-- The group identifier and leaf index of a `LeafNodeTBS` of a key package are empty (MLS*'s `()`). -/
theorem LeafNodeTBS.eq_of_keyPackage {Bytes: Type} [BytesLike Bytes] {tkt: TreeKEMTypes Bytes}
  (data: LeafNodeData Bytes tkt) (groupId1 groupId2: StaticOption (data.source == .update || data.source == .commit) (MlsBytes Bytes))
  (leafIndex1 leafIndex2: StaticOption (data.source == .update || data.source == .commit) UInt32)
  (h: data.source = .keyPackage):
  ({ data, groupId := groupId1, leafIndex := leafIndex1 }: LeafNodeTBS Bytes tkt) = { data, groupId := groupId2, leafIndex := leafIndex2 }
:= by
  obtain ⟨_, _, _, _, source, _, _, _⟩ := data
  simp only at h
  subst h
  rfl

/-! ## Predicates -/

section Predicates

variable [HasSymbolicBytes] [ExecTraceTypes] [ProofTraceTypes] (tkt: TreeKEMTypes Bytes)
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]

/--
The part of `leaf_node_sign_pred` depending on the source of the leaf node.
-/
@[expose]
public
def LeafNodeSignPredSource (prin: Participant) (tr: ExecTrace) (lnTbsBytes: Bytes) (lnTbs: LeafNodeTBS Bytes tkt): Prop :=
  if h: lnTbs.data.source = .commit then
    let groupId := lnTbs.groupId.get (by simp [h])
    let leafIndex := (lnTbs.leafIndex.get (by simp [h])).toNat
    ∃ tl: TreeSyncList Bytes tkt,
      TreeListStartsWithTbs tl lnTbsBytes ∧
      TreeListIsParentHashLinkedP tl ∧
      TreeListEndsAtRoot tl ∧
      TreeListIsCanonicalized leafIndex tl ∧
      TreeListHasEvent prin tr groupId leafIndex tl
  else if h: lnTbs.data.source = .update then
    let groupId := lnTbs.groupId.get (by simp [h])
    let leafIndex := (lnTbs.leafIndex.get (by simp [h])).toNat
    TreeHasEvent prin tr groupId leafIndex
      ⟨0, (ChildSiblingView.leaf (some { data := lnTbs.data, signature := MlsBytes.empty }) leafIndex).pack⟩
  else
    True

/--
The pred field of `leaf_node_sign_pred`.
When signing its leaf node for a Commit,
the leaf attests the existence of a tree list,
that is parent-hash linked and goes up to the root,
furthermore one event "GroupHasTreeEvent" was triggered for each of these trees.
-/
@[expose]
public
def LeafNodeTbsPred (skUsg: Usage) (lnTbsBytes: Bytes) (tr: ProofTrace): Prop :=
  match (LeafNodeTBS.mf tkt).toExtensible.parse lnTbsBytes with
  | none => False
  | some lnTbs =>
    ∃ prin,
      skUsg = mkMlsSigkeyUsage prin ∧
      LeafNodeHasEvent prin tr.erase lnTbs ∧
      LeafNodeSignPredSource tkt prin tr.erase lnTbsBytes lnTbs

/-- Port of `leaf_node_sign_pred` (with `leaf_node_tbs_tag_and_invariant`). -/
@[expose]
public
def leafNodeSignPred: SignWithLabelPred.Local ["LeafNodeTBS"] :=
  .single { pred skUsg _vk lnTbsBytes tr := LeafNodeTbsPred tkt skUsg lnTbsBytes tr }

omit [ProofTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))] in
theorem LeafNodeSignPredSource_le (prin: Participant) (tr1 tr2: ExecTrace) (lnTbsBytes: Bytes) (lnTbs: LeafNodeTBS Bytes tkt)
  : tr1 ≤ tr2 →
    LeafNodeSignPredSource tkt prin tr1 lnTbsBytes lnTbs →
    LeafNodeSignPredSource tkt prin tr2 lnTbsBytes lnTbs
:= by
  unfold LeafNodeSignPredSource TreeListHasEvent TreeHasEvent
  split <;> grind

grind_pattern LeafNodeSignPredSource_le => tr1 ≤ tr2, LeafNodeSignPredSource tkt prin tr1 lnTbsBytes lnTbs
grind_pattern [grind_later] LeafNodeSignPredSource_le => tr1 ≤ tr2, LeafNodeSignPredSource tkt prin tr1 lnTbsBytes lnTbs

/-- Port of the `pred_later` field of `leaf_node_sign_pred`. -/
public
theorem leafNodeSignPredProof [BytesInvariants]: SignWithLabelPred.LocalProof (leafNodeSignPred tkt) :=
  .single fun skUsg _vk lnTbsBytes tr1 tr2 _ _ hle h => by
    change LeafNodeTbsPred tkt skUsg lnTbsBytes tr1 at h
    change LeafNodeTbsPred tkt skUsg lnTbsBytes tr2
    unfold LeafNodeTbsPred LeafNodeHasEvent at *
    split at h <;> grind

/-- The leaf node signature predicate, on a serialized `LeafNodeTBS`. -/
theorem leafNodeTbsPred_serializeNE (skUsg: Usage) (lnTbs: LeafNodeTBS Bytes tkt) (tr: ProofTrace):
  LeafNodeTbsPred tkt skUsg (serializeNE (LeafNodeTBS.mf tkt) lnTbs) tr ↔
    ∃ prin,
      skUsg = mkMlsSigkeyUsage prin ∧
      LeafNodeHasEvent prin tr.erase lnTbs ∧
      LeafNodeSignPredSource tkt prin tr.erase (serializeNE (LeafNodeTBS.mf tkt) lnTbs) lnTbs
:= by
  have := ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv (LeafNodeTBS.mf tkt).toExtensible lnTbs
  simp [LeafNodeTbsPred, serializeNE, this]

/-- The leaf node signature predicate on the signed content of a leaf node. -/
theorem leafNodeTbsPred_getLeafTbs_iff (skUsg: Usage) (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat)
  (tr: ProofTrace) (hli: li < 2^32):
  LeafNodeTbsPred tkt skUsg (getLeafTbs ln groupId li.toUInt32) tr ↔
    ∃ prin,
      skUsg = mkMlsSigkeyUsage prin ∧
      LeafNodeHasEvent prin tr.erase { data := ln.data, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 } ∧
      (ln.data.source = .commit →
        ∃ tl: TreeSyncList Bytes tkt,
          TreeListStartsWithTbs tl (getLeafTbs ln groupId li.toUInt32) ∧
          TreeListIsParentHashLinkedP tl ∧
          TreeListEndsAtRoot tl ∧
          TreeListIsCanonicalized li tl ∧
          TreeListHasEvent prin tr.erase groupId li tl) ∧
      (ln.data.source = .update →
        TreeHasEvent prin tr.erase groupId li
          ⟨0, (ChildSiblingView.leaf (some { data := ln.data, signature := MlsBytes.empty }) li).pack⟩)
:= by
  have hli': li.toUInt32.toNat = li := by grind [UInt32.toNat_ofNat_of_lt]
  rw [getLeafTbs, leafNodeTbsPred_serializeNE]
  unfold LeafNodeSignPredSource
  apply exists_congr
  intro prin
  split <;> (try split) <;> simp_all [StaticOption.get_mk'] <;> grind

end Predicates

/-! ## Symbolic bytes -/

section SymbolicBytes

variable [HasSymbolicBytes]

/-- There is no hash collision on symbolic bytes. -/
public
theorem not_isHashCollision (x: Bytes × Bytes): ¬ isHashCollision x := by
  obtain ⟨b1, b2⟩ := x
  simp only [isHashCollision, CryptoBytes.hashHash, Bool.and_eq_true, bne_iff_ne, ne_eq]
  grind [DY.Hash.hash_inj, Result.pure_eq_success]

public
theorem mkMlsSigkeyUsage_injective: Function.Injective mkMlsSigkeyUsage := by
  intro p1 p2 h
  simp only [mkMlsSigkeyUsage, Usage.sigKey, Usage.mk.injEq, Option.some.injEq, true_and] at h
  have := congrArg DY.Literal.bytesToLiteral h
  simp only [DY.Literal.bytesToLiteral_literalToBytes, Option.some.injEq, String.toUTF8_eq_toByteArray,
    String.toByteArray_inj] at this
  grind

end SymbolicBytes

/-! ## Proof of verification, for a tree -/

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `last_tree_equivalent`. -/
theorem lastTreeEquivalent (tl1 tl2: TreeSyncList Bytes tkt) (li: Nat)
  (h: TreeListEquivalentSubset tl1 tl2 li) (hne: tl1 ≠ []):
  ∃ x1 x2, tl1.getLast? = some x1 ∧ tl2[tl1.length - 1]? = some x2 ∧ Equivalent x1.2 x2.2 li
:= by
  induction tl1 generalizing tl2 with
  | nil => contradiction
  | cons x1 tail1 ih =>
    obtain ⟨_, t1⟩ := x1
    rcases tl2 with _ | ⟨⟨_, t2⟩, tail2⟩
    · simp [TreeListEquivalentSubset] at h
    simp only [TreeListEquivalentSubset] at h
    rcases tail1 with _ | ⟨y, tail1⟩
    · exact ⟨_, _, rfl, rfl, h.1⟩
    · obtain ⟨x1, x2, h1, h2, h3⟩ := ih tail2 h.2 (by simp)
      grind

public
theorem TreeParentHashLinkedP.isSubtreeOf {x y: OneTreeSync Bytes tkt} (h: TreeParentHashLinkedP x y):
  x.2.IsSubtreeOf y.2
:= by
  obtain ⟨_, _⟩ := x
  obtain ⟨_ | _, _⟩ := y <;> simp_all [TreeParentHashLinkedP, ParentHashLinkedP]

public
theorem TreeParentHashLinkedP.nodeHasParentHash {x y: OneTreeSync Bytes tkt} (h: TreeParentHashLinkedP x y):
  nodeHasParentHash x.2
:= by
  obtain ⟨_, _⟩ := x
  obtain ⟨_ | _, _⟩ := y <;> grind [TreeParentHashLinkedP, ParentHashLinkedP, parentHashLinked, nodeHasParentHash_of_parentHashCorrect]

/-- Port of `tree_list_head_subtree_tail`. -/
public
theorem treeListIsParentHashLinkedP_head_isSubtreeOf_last (tl: TreeSyncList Bytes tkt) (x y: OneTreeSync Bytes tkt)
  (h: TreeListIsParentHashLinkedP tl) (hx: tl.head? = some x) (hy: tl.getLast? = some y):
  x.2.IsSubtreeOf y.2
:= by
  induction tl generalizing x with
  | nil => simp at hx
  | cons a tail ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    rcases tail with _ | ⟨b, tail⟩
    · grind
    · simp only [TreeListIsParentHashLinkedP, ListChain] at h
      exact h.1.isSubtreeOf.trans (ih b h.2 rfl (by simpa using hy))

/-- The first tree of a parent-hash linked list ending with a tree with a parent hash has a parent hash. -/
public
theorem treeListIsParentHashLinkedP_head_nodeHasParentHash (tl: TreeSyncList Bytes tkt) (x y: OneTreeSync Bytes tkt)
  (h: TreeListIsParentHashLinkedP tl) (hx: tl.head? = some x) (hy: tl.getLast? = some y) (hph: nodeHasParentHash y.2):
  nodeHasParentHash x.2
:= by
  rcases tl with _ | ⟨a, _ | ⟨b, tail⟩⟩ <;>
    grind [TreeListIsParentHashLinkedP, ListChain, TreeParentHashLinkedP.nodeHasParentHash]

/--
MLS*'s `get_authentifier_index t = li`, as a predicate:
`li` is the leaf index of the leaf starting a parent-hash linked list of trees ending with `t`.
-/
@[expose]
public
def IsAuthentifierIndex {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat): Prop :=
  ∃ (tl: TreeSyncList Bytes tkt) (leaf: TreeSync Bytes tkt 0),
    TreeListIsParentHashLinkedP tl ∧ tl.getLast? = some ⟨l, t⟩ ∧ tl.head? = some ⟨0, leaf⟩ ∧ leaf.position = li

/--
Port of `get_authentifier_index` (the authentifier exists).
MLS* requires `node_not_blank t` (here, `nodeHasParentHash t`, as in `parent_hash_invariant_to_tree_list`).
-/
public
theorem exists_isAuthentifierIndex {l: Nat} (t: TreeSync Bytes tkt l)
  (hok: unmergedLeavesOk t) (hinv: parentHashInvariant t) (hph: nodeHasParentHash t):
  ∃ li, IsAuthentifierIndex t li
:= by
  obtain ⟨tl, h1, h2, h3⟩ := exists_treeList_of_parentHashInvariant t hph hok hinv
  rcases tl with _ | ⟨⟨_, leaf⟩, tail⟩
  · simp at h2
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq] at h3
    subst h3
    exact ⟨leaf.position, _, leaf, h1, h2, rfl, rfl⟩

/-- Port of the postcondition of `get_authentifier_index`: the authentifier is a non-blank leaf of the tree. -/
public
theorem IsAuthentifierIndex.leafAt {l: Nat} {t: TreeSync Bytes tkt l} {li: Nat} (h: IsAuthentifierIndex t li)
  (hph: nodeHasParentHash t):
  t.containsLeafIndex li ∧ (MLS.leafAt t li).isSome
:= by
  obtain ⟨tl, leaf, h1, h2, h3, rfl⟩ := h
  have hsub := treeListIsParentHashLinkedP_head_isSubtreeOf_last tl _ _ h1 h3 h2
  have hph' := treeListIsParentHashLinkedP_head_nodeHasParentHash tl _ _ h1 h3 h2 hph
  have := leafAt_of_isSubtreeOf_zero leaf t hsub
  have := nodeNotBlank_of_nodeHasParentHash leaf hph'
  grind [nodeNotBlank_zero]

/-- Port of `leaf_at_valid_leaves`. MLS* requires `li: leaf_index l i` (here `hli`). -/
theorem leafIsValid_leafAt (groupId: MlsBytes Bytes) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (ln: LeafNode Bytes tkt)
  (hinv: validLeavesInvariant groupId t) (hli: t.containsLeafIndex li) (hln: MLS.leafAt t li = some ln):
  leafIsValid ln groupId li
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    have := eq_of_containsLeafIndex_zero t.containsLeafIndex_position hli
    rw [validLeavesInvariant_zero] at hinv
    grind [MLS.leafAt.eq_def]
  | node t ih =>
    rw [validLeavesInvariant_succ groupId t li] at hinv
    grind [MLS.leafAt.eq_def, Tree.mem_child_self]

theorem canonicalize_leaf (ln: LeafNode Bytes tkt) (li: Nat):
  canonicalize ((ChildSiblingView.leaf (some ln) li).pack: TreeSync Bytes tkt 0) li =
    (ChildSiblingView.leaf (some { data := ln.data, signature := MlsBytes.empty }) li).pack
:= by
  apply Tree.ext_zero <;> simp [leafContent_canonicalize]

/-! ## Proof of verification, for a state -/

/-- Port of `valid_leaves_invariant_subtree`. -/
public
theorem validLeavesInvariant_of_isSubtreeOf (groupId: MlsBytes Bytes) {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp)
  (hinv: validLeavesInvariant groupId p) (hsub: d.IsSubtreeOf p):
  validLeavesInvariant groupId d
:= by
  induction hsub <;> grind [validLeavesInvariant_succ]

/-- Port of `is_well_formed_treesync_subtree`. -/
public
theorem wf_of_isSubtreeOf (pred: Bytes → Prop) [BytesCompatiblePred pred] {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp)
  (hwf: (TreeSync.mf tkt lp).wf pred p) (hsub: d.IsSubtreeOf p):
  (TreeSync.mf tkt ld).wf pred d
:= by
  induction hsub with
  | refl => grind
  | child p _ ih => grind [Tree.mf.wf_child_sibling]

/--
Port of `all_credentials_ok_subtree`.
The positions of the trees and of the tokens are related by hypotheses (MLS* shares the index `i`).
-/
public
theorem allCredentialsOk_of_isSubtreeOf {TokenT: Type} {asp: ASParameters Bytes TokenT} {ld lp: Nat}
  (d: TreeSync Bytes tkt ld) (p: TreeSync Bytes tkt lp) (astD: ASTokens TokenT ld) (astP: ASTokens TokenT lp)
  (h: allCredentialsOk asp p astP) (hsub: d.IsSubtreeOf p) (hsubAst: astD.IsSubtreeOf astP)
  (hposP: p.position = astP.position) (hposD: d.position = astD.position):
  allCredentialsOk asp d astD
:= by
  induction hsub with
  | refl =>
    cases hsubAst with
    | refl => grind
    | child _ h' => exfalso; grind
  | child p hsub ih =>
    rw [allCredentialsOk_succ p astP d.position hposP] at h
    apply ih (astP.child d.position) h.1 <;> grind

end CryptoBytes

/-! ## Verification of leaf signatures -/

section Symbolic

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]

variable [SignWithLabelPred.Has (leafNodeSignPred tkt)]

/--
Verifying the signature of a leaf node validated by the AS gives the leaf node signature predicate,
unless the signature key of its principal is corrupt.
This is the common part of `parent_hash_implies_event`, `leaf_node_source_update_implies_event`
and `leaf_node_source_key_package_implies_event`.
-/
theorem leafNodeTbsPred_of_leafIsValid (tr: ProofTrace)
  (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat) (token: DyAsToken)
  (hvalid: leafIsValid ln groupId li) (hcred: (dyAsp tr).credentialOk (leafNodeToAsInput ln) token)
  (hwf: (LeafNode.mf tkt).wf (Bytes.Invariant · tr) ln) (hgroupId: groupId.val.Invariant tr):
  ∃ authentifier, credentialToPrincipal ln.data.credential = some authentifier ∧ (
    LeafNodeTbsPred tkt (mkMlsSigkeyUsage authentifier) (getLeafTbs ln groupId li.toUInt32) tr ∨
    (signatureKeyLabel authentifier ln.data.signatureKey.val).isCorrupt tr.erase
  )
:= by
  obtain ⟨authentifier, hcp, hvk⟩ := isSignatureKeyVk_of_credentialOk tr _ _ token hcred
  refine ⟨authentifier, hcp, ?_⟩
  simp only [leafIsValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rw [LeafNode.mf.wf_eq] at hwf
  have htbs: (getLeafTbs ln groupId li.toUInt32).Invariant tr := by
    rw [getLeafTbs, pred_serializeNE_iff (LeafNodeTBS.mf tkt) (Bytes.Invariant · tr), LeafNodeTBS.mf.wf_eq]
    grind [StaticOption.get_mk']
  have := verifyWithLabel.Invariant (leafNodeSignPred tkt) tr authentifier _ "LeafNodeTBS" _ _
    hvk.1.1 htbs hwf.2 hvk.2.2 hvalid.2.2 (by simp)
  rw [canFlowPubEqIsCorrupt, ← hvk.2.1]
  exact this

/--
Port of `parent_hash_implies_event`.
When a tree satisfy all the invariants,
then there exists a leaf inside that authenticates it:
- either the principal at the leaf triggered an event saying it saw the tree in the group,
- or the principal at the leaf is corrupt.
The proof works by obtaining a tree list `tl` from the parent-hash invariant (in `IsAuthentifierIndex`),
obtaining another tree list `leafTl` from the signature predicate.
Then, using the parent-hash integrity theorem `parentHashGuaranteeTheorem_spec`,
we conclude.
MLS* also requires `unmerged_leaves_ok t` and `parent_hash_invariant t`, which are only needed
for the existence of the authentifier (`exists_isAuthentifierIndex`).
-/
public
theorem parentHashImpliesEvent {l: Nat} (tr: ProofTrace) (groupId: MlsBytes Bytes) (t: TreeSync Bytes tkt l)
  (authentifierLi: Nat) (authentifierLn: LeafNode Bytes tkt) (token: DyAsToken)
  (hvalid: validLeavesInvariant groupId t) (hph: nodeHasParentHash t) (hauth: IsAuthentifierIndex t authentifierLi)
  (hln: leafAt t authentifierLi = some authentifierLn)
  (hcred: (dyAsp tr).credentialOk (leafNodeToAsInput authentifierLn) token)
  (hwf: (LeafNode.mf tkt).wf (Bytes.Invariant · tr) authentifierLn) (hgroupId: groupId.val.Invariant tr):
  ∃ authentifier, credentialToPrincipal authentifierLn.data.credential = some authentifier ∧ (
    TreeHasEvent authentifier tr.erase groupId authentifierLi ⟨l, canonicalize t authentifierLi⟩ ∨
    (signatureKeyLabel authentifier authentifierLn.data.signatureKey.val).isCorrupt tr.erase
  )
:= by
  obtain ⟨tl, leaf, hlinked, hlast, hhead, rfl⟩ := hauth
  have hsub := treeListIsParentHashLinkedP_head_isSubtreeOf_last tl _ _ hlinked hhead hlast
  have hphLeaf := treeListIsParentHashLinkedP_head_nodeHasParentHash tl _ _ hlinked hhead hlast hph
  have hleaf := leafAt_of_isSubtreeOf_zero leaf t hsub
  have hli: leafIsValid authentifierLn groupId leaf.position :=
    leafIsValid_leafAt groupId t _ _ hvalid hsub.containsLeafIndex hln
  have hli32: leaf.position < 2^32 := by grind [leafIsValid]
  have hsrc: authentifierLn.data.source = .commit := by
    grind [nodeHasParentHash, getParentHashOf_leaf]
  obtain ⟨authentifier, hcp, hor⟩ := leafNodeTbsPred_of_leafIsValid tr _ _ _ token hli hcred hwf hgroupId
  refine ⟨authentifier, hcp, hor.imp_left fun hpred => ?_⟩
  obtain ⟨prin, hprin, -, hcommit, -⟩ := (leafNodeTbsPred_getLeafTbs_iff _ _ _ _ _ _ hli32).mp hpred
  obtain rfl := mkMlsSigkeyUsage_injective hprin
  obtain ⟨leafTl, hstarts, hlinked', hroot, hcanon, hevent⟩ := hcommit hsrc
  obtain ⟨tail, rfl⟩: ∃ tail, tl = ⟨0, leaf⟩ :: tail := by
    rcases tl with _ | ⟨x, tail⟩ <;> simp_all
  have hstarts': TreeListStartsWithTbs (⟨0, leaf⟩ :: tail) (getLeafTbs authentifierLn groupId leaf.position.toUInt32) := by
    refine ⟨hphLeaf, groupId, ?_⟩
    simp [getLeafTreeTbs, ← hleaf, hln, hli32]
  have hequiv := (parentHashGuaranteeTheorem_spec _ leafTl _ hlinked hlinked' hstarts' hstarts hroot).resolve_right
    (not_isHashCollision _)
  obtain ⟨x1, x2, h1, h2, h3⟩ := lastTreeEquivalent _ _ _ hequiv (by simp)
  have hmem := List.mem_of_getElem? h2
  have := canonicalize_eq_self x2.2 _ (hcanon x2 hmem).2
  have := hevent x2 hmem
  grind [Equivalent, getLeafIndexFromTreeList]

/--
Port of `leaf_node_source_update_implies_event`.
MLS*'s tree `TLeaf (Some ln)` (at position `li`) is `(ChildSiblingView.leaf (some ln) li).pack`.
-/
public
theorem leafNodeSourceUpdateImpliesEvent (tr: ProofTrace)
  (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat) (token: DyAsToken)
  (hsrc: ln.data.source = .update) (hvalid: leafIsValid ln groupId li)
  (hcred: (dyAsp tr).credentialOk (leafNodeToAsInput ln) token)
  (hwf: (LeafNode.mf tkt).wf (Bytes.Invariant · tr) ln) (hgroupId: groupId.val.Invariant tr):
  ∃ prin, credentialToPrincipal ln.data.credential = some prin ∧ (
    TreeHasEvent prin tr.erase groupId li ⟨0, canonicalize (ChildSiblingView.leaf (some ln) li).pack li⟩ ∨
    (signatureKeyLabel prin ln.data.signatureKey.val).isCorrupt tr.erase
  )
:= by
  have hli32: li < 2^32 := by grind [leafIsValid]
  obtain ⟨prin, hcp, hor⟩ := leafNodeTbsPred_of_leafIsValid tr _ _ _ token hvalid hcred hwf hgroupId
  refine ⟨prin, hcp, hor.imp_left fun hpred => ?_⟩
  obtain ⟨prin', hprin, -, -, hupdate⟩ := (leafNodeTbsPred_getLeafTbs_iff _ _ _ _ _ _ hli32).mp hpred
  obtain rfl := mkMlsSigkeyUsage_injective hprin
  rw [canonicalize_leaf]
  grind

/--
Port of `leaf_node_source_key_package_implies_event`.
MLS*'s `group_id = ()` and `leaf_index = ()` are `StaticOption.mk MlsBytes.empty` and `StaticOption.mk 0`
(as in `MLS.TreeKEM.Symbolic.API.generateKeyPackage`).
-/
public
theorem leafNodeSourceKeyPackageImpliesEvent (tr: ProofTrace)
  (ln: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (li: Nat) (token: DyAsToken)
  (hsrc: ln.data.source = .keyPackage) (hvalid: leafIsValid ln groupId li)
  (hcred: (dyAsp tr).credentialOk (leafNodeToAsInput ln) token)
  (hwf: (LeafNode.mf tkt).wf (Bytes.Invariant · tr) ln) (hgroupId: groupId.val.Invariant tr):
  ∃ prin, credentialToPrincipal ln.data.credential = some prin ∧ (
    LeafNodeHasEvent prin tr.erase { data := ln.data, groupId := StaticOption.mk MlsBytes.empty, leafIndex := StaticOption.mk 0 } ∨
    (signatureKeyLabel prin ln.data.signatureKey.val).isCorrupt tr.erase
  )
:= by
  have hli32: li < 2^32 := by grind [leafIsValid]
  obtain ⟨prin, hcp, hor⟩ := leafNodeTbsPred_of_leafIsValid tr _ _ _ token hvalid hcred hwf hgroupId
  refine ⟨prin, hcp, hor.imp_left fun hpred => ?_⟩
  obtain ⟨prin', hprin, hev, -⟩ := (leafNodeTbsPred_getLeafTbs_iff _ _ _ _ _ _ hli32).mp hpred
  obtain rfl := mkMlsSigkeyUsage_injective hprin
  grind [LeafNodeTBS.eq_of_keyPackage]

/--
Port of `state_implies_event`.
If a TreeSync state contains a subtree,
then there exists a leaf inside that authenticates it:
- either the principal at the leaf triggered an event saying it saw the subtree in the group,
- or the principal at the leaf is corrupt.
This theorem is mostly a wrapper around `parentHashImpliesEvent`.
The TreeSync invariants of the state (MLS*'s refinement `treesync_valid`) are `hvalid`,
and the positions of the subtree and its tokens are related by `hpos` (MLS* shares the index `i`).
The authentifier is any leaf index satisfying `IsAuthentifierIndex` (MLS*'s `get_authentifier_index t`),
which exists by `exists_isAuthentifierIndex`.
-/
public
theorem stateImpliesEvent {groupId: MlsBytes Bytes} {l: Nat} (tr: ProofTrace)
  (st: TreeSyncState Bytes tkt DyAsToken groupId) (t: TreeSync Bytes tkt l) (ast: ASTokens DyAsToken l)
  (hph: nodeHasParentHash t) (hwf: (TreeSync.mf tkt st.levels).wf (Bytes.Invariant · tr) st.tree)
  (hgroupId: groupId.val.Invariant tr)
  (hsub: t.IsSubtreeOf st.tree) (hsubAst: ast.IsSubtreeOf st.tokens) (hpos: t.position = ast.position)
  (hst: treesyncStateValid (dyAsp tr) st) (hvalid: st.TreeValid):
  unmergedLeavesOk t ∧ parentHashInvariant t ∧ allCredentialsOk (dyAsp tr) t ast ∧
  ∀ authentifierLi, IsAuthentifierIndex t authentifierLi →
    ∃ authentifierLn authentifier,
      leafAt t authentifierLi = some authentifierLn ∧
      credentialToPrincipal authentifierLn.data.credential = some authentifier ∧ (
        TreeHasEvent authentifier tr.erase groupId authentifierLi ⟨l, canonicalize t authentifierLi⟩ ∨
        (signatureKeyLabel authentifier authentifierLn.data.signatureKey.val).isCorrupt tr.erase
      )
:= by
  obtain ⟨hok, hinv, hvl⟩ := hvalid
  have hok' := unmergedLeavesOk_of_isSubtreeOf t st.tree hok hsub
  have hinv' := parentHashInvariant_of_isSubtreeOf t st.tree hinv hsub
  have hvl' := validLeavesInvariant_of_isSubtreeOf groupId t st.tree hvl hsub
  have hwf' := wf_of_isSubtreeOf _ t st.tree hwf hsub
  have hcreds := allCredentialsOk_of_isSubtreeOf t st.tree ast st.tokens hst.2 hsub hsubAst hst.1 hpos
  refine ⟨hok', hinv', hcreds, fun li hauth => ?_⟩
  obtain ⟨ln, hln⟩ := Option.isSome_iff_exists.mp (hauth.leafAt hph).2
  obtain ⟨token, htoken⟩: ∃ token, (dyAsp tr).credentialOk (leafNodeToAsInput ln) token := by
    have := allCredentialsOk_elim t ast li hpos hcreds
    unfold oneCredentialOk at this
    split at this <;> grind
  have hwfln := leafAt_wf _ t li hwf'
  rw [hln, MlsOption.mf.wf_eq] at hwfln
  have := parentHashImpliesEvent tr groupId t li ln token hvl' hph hauth hln htoken hwfln hgroupId
  grind

end Symbolic

/-! ## Proof of path signature -/

section CryptoBytes

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/-- Port of `get_path_leaf_set_path_leaf`. -/
@[simp]
theorem getPathLeaf_setPathLeaf' {Leaf Leaf' Node: Type} {l: Nat} (p: Path Leaf Node l) (x: Leaf'):
  (p.setPathLeaf x).getPathLeaf = x
:= by
  induction p <;> simp_all [Path.setPathLeaf, Path.getPathLeaf]

/-- Port of `compute_leaf_parent_hash_from_path_set_path_leaf`. -/
theorem computeLeafParentHashFromPath_setPathLeaf {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (ln: LeafNode Bytes tkt) (parentParentHash: Bytes):
  computeLeafParentHashFromPath t li (p.setPathLeaf ln) parentParentHash = computeLeafParentHashFromPath t li p parentParentHash
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p
    simp only [Path.setPathLeaf, computeLeafParentHashFromPath_zero]
  | node t ih =>
    cases p
    simp only [Path.setPathLeaf, computeLeafParentHashFromPath_node_eq, ih]

/-- The data of the leaf node computed by `externalPathToPathAux` and `externalPathToPathAuxNosig`. -/
abbrev commitLeafNodeData (lp: LeafNodeData Bytes tkt) (parentHash: MlsBytes Bytes): LeafNodeData Bytes tkt :=
  { lp with source := .commit, lifetime := (), parentHash := parentHash }

theorem externalPathToPathNosig_eq_success {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (authP: PathSync Bytes tkt l)
  (h: externalPathToPathNosig t li p = .success authP):
  ∃ ph: MlsBytes Bytes,
    computeLeafParentHashFromPath t li p rootParentHash.val = .success ph.val ∧
    authP = p.setPathLeaf ({ data := commitLeafNodeData p.getPathLeaf ph, signature := MlsBytes.empty }: LeafNode Bytes tkt)
:= by
  simp only [externalPathToPathNosig, externalPathToPathAuxNosig, Result.bind_eq_success, mkMlsBytes_eq_success,
    Result.pure_eq_success] at h
  grind

theorem externalPathToPath_eq_success {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (signKey nonce: Bytes) (authP: PathSync Bytes tkt l)
  (h: externalPathToPath t li p groupId signKey nonce = .success authP):
  ∃ ph signature: MlsBytes Bytes,
    computeLeafParentHashFromPath t li p rootParentHash.val = .success ph.val ∧
    li < 2^32 ∧
    signWithLabel signKey "LeafNodeTBS"
      (serializeNE (LeafNodeTBS.mf tkt)
        { data := commitLeafNodeData p.getPathLeaf ph, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 })
      nonce = .success signature.val ∧
    authP = p.setPathLeaf ({ data := commitLeafNodeData p.getPathLeaf ph, signature }: LeafNode Bytes tkt)
:= by
  simp only [externalPathToPath, externalPathToPathAux, Result.bind_eq_success, mkMlsBytes_eq_success,
    mkUInt32_eq_success, Result.pure_eq_success] at h
  obtain ⟨_, ⟨_, hph, ph, rfl, _, ⟨hli, rfl⟩, _, rfl, _, hsig, sig, rfl, rfl⟩, rfl⟩ := h
  exact ⟨ph, sig, hph, hli, hsig, rfl⟩

/--
Port of `path_is_parent_hash_valid_external_path_to_path_nosig`.
MLS* requires `(get_path_leaf p).source == LNS_update` and `li: leaf_index l 0`, which are not needed.
-/
theorem pathIsParentHashValid_externalPathToPathNosig {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (authP: PathSync Bytes tkt l)
  (h: externalPathToPathNosig t li p = .success authP):
  pathIsParentHashValid t li authP
:= by
  obtain ⟨ph, hph, rfl⟩ := externalPathToPathNosig_eq_success t li p authP h
  unfold pathIsParentHashValid
  rw [getPathLeaf_setPathLeaf']
  simp [computeLeafParentHashFromPath_setPathLeaf, hph]
  rfl

/-- Port of `path_is_filter_valid_set_path_leaf`. -/
theorem pathIsFilterValid_setPathLeaf {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (ln: LeafNode Bytes tkt):
  pathIsFilterValid t li (p.setPathLeaf ln) = pathIsFilterValid t li p
:= by
  induction t using Tree.childInduction li with
  | leaf t =>
    cases p
    unfold pathIsFilterValid
    simp [Path.setPathLeaf, Tree.intoChildSiblingView_zero]
  | node t ih =>
    cases p
    simp only [Path.setPathLeaf, pathIsFilterValid_node, ih]

/-- Port of `path_is_filter_valid_external_path_to_path_nosig`. -/
theorem pathIsFilterValid_externalPathToPathNosig {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (authP: PathSync Bytes tkt l)
  (h: externalPathToPathNosig t li p = .success authP) (hfilter: pathIsFilterValid t li p):
  pathIsFilterValid t li authP
:= by
  obtain ⟨ph, -, rfl⟩ := externalPathToPathNosig_eq_success t li p authP h
  grind [pathIsFilterValid_setPathLeaf]

/-- Port of `apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed`. -/
theorem exists_applyPathAux_iff {l: Nat}
  (t: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l) (parentParentHash: Bytes):
  (∃ t', applyPathAux t li p parentParentHash = .success t') ↔
    (∃ ph, computeLeafParentHashFromPath t li p parentParentHash = .success ph)
:= by
  induction t using Tree.childInduction li generalizing parentParentHash with
  | leaf t =>
    cases p
    unfold applyPathAux
    simp [computeLeafParentHashFromPath_zero, Tree.intoChildSiblingView_zero]
  | node t ih =>
    cases p with | node optExtContent pNext =>
    rw [applyPathAux_node_eq, computeLeafParentHashFromPath_node_eq]
    cases computeNewNpAndPh optExtContent (t.sibling li) parentParentHash with
    | success x =>
      simp only [Result.bind_eq_success, Result.pure_eq_success]
      have := ih pNext x.2
      grind
    | _ => simp [Bind.bind, Result.bind]

end CryptoBytes

section Symbolic

variable [HasSymbolicInvariants] {tkt: TreeKEMTypes Bytes}
variable [ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeSyncSignatureKeyState)]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeSignedEvent tkt))]
variable [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (GroupHasTreeEvent tkt))]
variable [SignWithLabelPred.Has (leafNodeSignPred tkt)]

/--
The signature of a leaf node is knowable by `label` when the signed content is,
and when the signed content satisfies the leaf node signature predicate.
This is the common part of `is_msg_external_path_to_path`, `is_msg_sign_leaf_node_data_key_package`
and `is_msg_sign_leaf_node_data_update`.
-/
theorem leafNode_wf_of_signWithLabel (prin: Participant) (label: Label) (tr: ProofTrace)
  (lnTbs: LeafNodeTBS Bytes tkt) (sk nonce: Bytes) (sig: MlsBytes Bytes)
  (hsign: signWithLabel sk "LeafNodeTBS" (serializeNE (LeafNodeTBS.mf tkt) lnTbs) nonce = .success sig.val)
  (hpred: LeafNodeTbsPred tkt (mkMlsSigkeyUsage prin) (serializeNE (LeafNodeTBS.mf tkt) lnTbs) tr)
  (htbs: (LeafNodeTBS.mf tkt).wf (Bytes.KnowableBy label · tr) lnTbs) (hsk: IsSignatureKeySk tr prin sk)
  (hnonce: nonce.Invariant tr) (hnonceUsg: nonce.HasUsage Usage.sigNonce tr)
  (hflow: (sk.label tr).canFlow (nonce.label tr) tr.erase):
  (LeafNode.mf tkt).wf (Bytes.KnowableBy label · tr) { data := lnTbs.data, signature := sig }
:= by
  have htbs' := (pred_serializeNE_iff (LeafNodeTBS.mf tkt) (Bytes.KnowableBy label · tr) lnTbs).2 htbs
  have hs := signWithLabel.Invariant (leafNodeSignPred tkt) tr prin sk "LeafNodeTBS" _ nonce sig.val hsign
    hsk.1 hnonce htbs'.1 hsk.2.2 hnonceUsg hflow (by simp) (Or.inl hpred)
  rw [LeafNodeTBS.mf.wf_eq] at htbs
  rw [LeafNode.mf.wf_eq]
  grind [canFlowTrans]

/--
Port of `is_msg_external_path_to_path`.
Proof that the path generated by `externalPathToPath`
(the function in charge of computing the path leaf signature)
satisfies the signature predicate.

This theorem can be instantiated with various labels to prove more specific theorems.
With `label = Label.pub`, we get a version with `Bytes.Publishable`.
MLS* requires `li: leaf_index l 0` (here `hli`); MLS*'s `Success? (external_path_to_path …)` is `h`.
MLS* also requires `(get_path_leaf p).source == LNS_update`, which follows from `hev`.
-/
public
theorem externalPathToPath_wf {l: Nat} (prin: Participant) (label: Label) (tr: ProofTrace)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (sk nonce: Bytes) (authP: PathSync Bytes tkt l)
  (h: externalPathToPath t li p groupId sk nonce = .success authP) (hli: t.containsLeafIndex li)
  (hfilter: pathIsFilterValid t li p) (hok: unmergedLeavesOk t)
  (hev: ExternalPathHasEvent prin tr.erase t li p groupId)
  (ht: (TreeSync.mf tkt l).wf (Bytes.KnowableBy label · tr) t)
  (hp: (ExternalPathSync.mf tkt l).wf (Bytes.KnowableBy label · tr) p)
  (hgroupId: groupId.val.KnowableBy label tr) (hsk: IsSignatureKeySk tr prin sk)
  (hnonce: nonce.Invariant tr) (hnonceUsg: nonce.HasUsage Usage.sigNonce tr)
  (hflow: (sk.label tr).canFlow (nonce.label tr) tr.erase):
  (PathSync.mf tkt l).wf (Bytes.KnowableBy label · tr) authP
:= by
  obtain ⟨ph, sig, hph, hli32, hsign, rfl⟩ := externalPathToPath_eq_success t li p groupId sk nonce authP h
  -- the events, on the path without signature
  unfold ExternalPathHasEvent at hev
  obtain ⟨-, -, unsignedP, hnosig, hevLn, tl, htl, hevTl⟩ := hev
  obtain ⟨ph', hph', rfl⟩ := externalPathToPathNosig_eq_success t li p _ hnosig
  obtain rfl: ph = ph' := Subtype.ext (by grind)
  -- the tree list of the path without signature
  have hvalid := pathIsParentHashValid_externalPathToPathNosig t li p _ hnosig
  have hfilter' := pathIsFilterValid_externalPathToPathNosig t li p _ hnosig hfilter
  obtain ⟨t', ht'⟩ := (exists_applyPathAux_iff t li
      (p.setPathLeaf { data := commitLeafNodeData p.getPathLeaf ph, signature := MlsBytes.empty }) rootParentHash.val).mpr
    ⟨ph.val, by grind [computeLeafParentHashFromPath_setPathLeaf]⟩
  obtain ⟨hlinked, hroot, hcanon, hhead⟩ :=
    pathToTreeList_spec t li _ tl t' htl ht' hvalid hfilter' hok hli (by simp)
  rw [getPathLeaf_setPathLeaf'] at hhead hevLn
  -- the signature predicate
  have hpred: LeafNodeTbsPred tkt (mkMlsSigkeyUsage prin)
    (getLeafTbs { data := commitLeafNodeData p.getPathLeaf ph, signature := MlsBytes.empty } groupId li.toUInt32) tr
  := by
    rw [leafNodeTbsPred_getLeafTbs_iff _ _ _ _ _ _ hli32]
    refine ⟨prin, rfl, hevLn, fun _ => ⟨tl, ?_, hlinked, hroot, hcanon, hevTl⟩, fun h => nomatch h⟩
    rcases tl with _ | ⟨x, tail⟩
    · simp at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    refine ⟨?_, groupId, ?_⟩
    · rw [nodeHasParentHash, getParentHashOf_leaf _ { data := commitLeafNodeData p.getPathLeaf ph, signature := MlsBytes.empty }
        (by simp)]
      rfl
    · simp [getLeafTreeTbs, hli32]
  -- well-formedness
  have hdata: (LeafNodeData.mf tkt).wf (Bytes.KnowableBy label · tr) (commitLeafNodeData p.getPathLeaf ph) := by
    have := getPathLeaf_wf _ p hp
    have := pred_computeLeafParentHashFromPath (Bytes.KnowableBy label · tr) t li p _ _ hph
      (preIsHashCompatible_knowableBy label tr) ht hp
      (by simpa [rootParentHash] using BytesCompatiblePred.pred_empty (pred := (Bytes.KnowableBy label · tr)))
    simp only [LeafNodeData.mf.wf_eq] at *
    exact ⟨this.1, this.2.1, this.2.2.1, fun _ => by assumption, this.2.2.2.2⟩
  apply setPathLeaf_wf _ p _ hp
  exact leafNode_wf_of_signWithLabel prin label tr
    { data := commitLeafNodeData p.getPathLeaf ph, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk li.toUInt32 }
    sk nonce sig hsign hpred (by simp [StaticOption.get_mk', hdata, hgroupId]) hsk hnonce hnonceUsg hflow

/-! ## Proof of individual leaf signature -/

/--
Port of `is_msg_sign_leaf_node_data_key_package`.
MLS*'s `group_id = ()` and `leaf_index = ()` are `StaticOption.mk MlsBytes.empty` and `StaticOption.mk 0`
(as in `MLS.TreeKEM.Symbolic.API.generateKeyPackage`).
MLS* also requires `ln_data.source == LNS_key_package`, which follows from `h`.
-/
public
theorem signLeafNodeDataKeyPackage_wf (prin: Participant) (label: Label) (tr: ProofTrace)
  (lnData: LeafNodeData Bytes tkt) (sk nonce: Bytes) (ln: LeafNode Bytes tkt)
  (h: signLeafNodeDataKeyPackage lnData sk nonce = .success ln)
  (hev: LeafNodeHasEvent prin tr.erase { data := lnData, groupId := StaticOption.mk MlsBytes.empty, leafIndex := StaticOption.mk 0 })
  (hdata: (LeafNodeData.mf tkt).wf (Bytes.KnowableBy label · tr) lnData) (hsk: IsSignatureKeySk tr prin sk)
  (hnonce: nonce.Invariant tr) (hnonceUsg: nonce.HasUsage Usage.sigNonce tr)
  (hflow: (sk.label tr).canFlow (nonce.label tr) tr.erase):
  (LeafNode.mf tkt).wf (Bytes.KnowableBy label · tr) ln
:= by
  unfold signLeafNodeDataKeyPackage at h
  split at h
  · simp [Result.internalFailure] at h
  rename_i hsrc
  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hsrc
  simp only [Result.bind_eq_success, mkMlsBytes_eq_success, Result.pure_eq_success] at h
  obtain ⟨_, hsign, sig, rfl, rfl⟩ := h
  apply leafNode_wf_of_signWithLabel prin label tr _ sk nonce sig hsign _ (by simp [hdata, hsrc]) hsk hnonce hnonceUsg hflow
  rw [leafNodeTbsPred_serializeNE]
  refine ⟨prin, rfl, LeafNodeTBS.eq_of_keyPackage lnData _ _ _ _ hsrc ▸ hev, ?_⟩
  simp [LeafNodeSignPredSource, hsrc]

/--
Port of `is_msg_sign_leaf_node_data_update`.
MLS* also requires `ln_data.source == LNS_update`, which follows from `h`.
-/
public
theorem signLeafNodeDataUpdate_wf (prin: Participant) (label: Label) (tr: ProofTrace)
  (lnData: LeafNodeData Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: UInt32) (sk nonce: Bytes) (ln: LeafNode Bytes tkt)
  (h: signLeafNodeDataUpdate lnData groupId leafIndex sk nonce = .success ln)
  (hev: LeafNodeHasEvent prin tr.erase { data := lnData, groupId := StaticOption.mk groupId, leafIndex := StaticOption.mk leafIndex })
  (htree: TreeHasEvent prin tr.erase groupId leafIndex.toNat
    ⟨0, (ChildSiblingView.leaf (some { data := lnData, signature := MlsBytes.empty }) leafIndex.toNat).pack⟩)
  (hdata: (LeafNodeData.mf tkt).wf (Bytes.KnowableBy label · tr) lnData) (hgroupId: groupId.val.KnowableBy label tr)
  (hsk: IsSignatureKeySk tr prin sk)
  (hnonce: nonce.Invariant tr) (hnonceUsg: nonce.HasUsage Usage.sigNonce tr)
  (hflow: (sk.label tr).canFlow (nonce.label tr) tr.erase):
  (LeafNode.mf tkt).wf (Bytes.KnowableBy label · tr) ln
:= by
  unfold signLeafNodeDataUpdate at h
  split at h
  · simp [Result.internalFailure] at h
  rename_i hsrc
  simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hsrc
  simp only [Result.bind_eq_success, mkMlsBytes_eq_success, Result.pure_eq_success] at h
  obtain ⟨_, hsign, sig, rfl, rfl⟩ := h
  apply leafNode_wf_of_signWithLabel prin label tr _ sk nonce sig hsign _
    (by simp [StaticOption.get_mk', hdata, hgroupId]) hsk hnonce hnonceUsg hflow
  rw [leafNodeTbsPred_serializeNE]
  refine ⟨prin, rfl, hev, ?_⟩
  simp [LeafNodeSignPredSource, hsrc, StaticOption.get_mk', htree]

end Symbolic

end MLS.TreeSync
