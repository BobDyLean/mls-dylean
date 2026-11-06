module

public import MLS.TreeKEM.SymbolicProofs.Tree.Operations
public import MLS.TreeSync.SymbolicProofs.AuthService
public import MLS.TreeSync.SymbolicProofs.API
import all MLS.TreeSync.SymbolicSpec.LeafNodeSignature
import all MLS.TreeSync.Code.Operations
import all MLS.TreeSync.Code.API
import all MLS.TreeKEM.Code.API.Tree

/-!
Port of `MLS.TreeKEM.Symbolic.API.Tree` (except its traceful function, see `MLS.TreeKEM.SymbolicSpec.API.Tree`):
the invariant of the TreeKEM tree states, and the proofs that the functions of `MLS.TreeKEM.API.Tree` preserve it.

Port-specific differences:
- The namespace is MLS*'s module name `MLS.TreeKEM.Symbolic.API.Tree`, as its names (`create_proof`, …)
  are reused by other modules.
- Lemmas about functions returning a `Result` take the result and the success hypothesis
  (MLS*'s `match … with | Success … -> … | _ -> True`).
- The refinements of the states (`treekem_tree_state`, the tree of `treesync_state`, `pending_commit`)
  are hypotheses (`stTk.Valid`, `stTs.TreeValid`, `pend.Valid`), only taken when the proof needs them.
- MLS*'s sparse update path `p` of `process_commit_proof` is given by its TreeSync and TreeKEM versions,
  related by `pathsyncPathkemRel` (MLS*'s `pathsync_pathkem_rel_update_path_to_treeX`), as in `processCommit_stateRel`.
-/

namespace MLS.TreeKEM.Symbolic.API.Tree

open Comparse
open DY DY.Comparse
open DySlop.HPKE
open MLS MLS.TreeSync MLS.TreeKEM MLS.TreeKEM.API.Tree

/-! ## Invariants -/

section Invariants

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]

/-- Port of `treekem_tree_state_invariant`. -/
@[expose]
public
def TreekemTreeStateInvariant {leafInd: Nat} (tr: ProofTrace) (me: Participant) (st: TreeKEMTreeState Bytes leafInd): Prop :=
  TreekemPrivStatePred tr me st.priv

/-- Port of `treekem_tree_state_invariant_later`. -/
public
theorem TreekemTreeStateInvariant_later {leafInd: Nat} (tr1 tr2: ProofTrace) (me: Participant)
  (st: TreeKEMTreeState Bytes leafInd):
  tr1 ≤ tr2 →
  TreekemTreeStateInvariant tr1 me st →
  TreekemTreeStateInvariant tr2 me st
:= by
  grind [TreekemTreeStateInvariant]

grind_pattern TreekemTreeStateInvariant_later => tr1 ≤ tr2, TreekemTreeStateInvariant tr1 me st
grind_pattern [grind_later] TreekemTreeStateInvariant_later => tr1 ≤ tr2, TreekemTreeStateInvariant tr1 me st

end Invariants

section ExtendedTreesyncInvariant

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/--
Port of `extended_treesync_invariant`.
MLS*'s refinement `treesync_valid` of the tree of the state is not included (see `TreeSyncState.TreeValid`).
-/
@[expose]
public
def ExtendedTreesyncInvariant {groupId: MlsBytes Bytes} (tr: ProofTrace) (me: Participant)
  (st: TreeSyncState Bytes tkt DyAsToken groupId): Prop :=
  treesyncStateValid (dyAsp tr) st ∧
  IHaveVerifiedEveryLeafNode tr.erase me st.tree groupId ∧
  (TreeSync.mf tkt st.levels).wf (Bytes.Invariant · tr) st.tree

end ExtendedTreesyncInvariant

section Proofs

variable [HasSymbolicInvariants] [HasTreeKEMExecTrace]

/-! ## Create -/

/-- Port of `create_proof`. -/
public
theorem create_proof (tr: ProofTrace) (me: Participant) (leafPrivateKey leafPublicKey: Bytes)
  (h: IsNodeSkForLeafPk tr me (hpkePk leafPrivateKey) leafPrivateKey):
  TreekemTreeStateInvariant tr me (create leafPrivateKey leafPublicKey)
:=
  h

/-! ## Welcome -/

/--
Port of `welcome_proof`.
MLS*'s `match opt_path_secret_and_inviter_ind` in the hypotheses is `hps`.
MLS* requires `leaf_ind < pow2 l` (here `_hli`), `Some? (leaf_at tk leaf_ind)` and `treekem_invariant tk`.
-/
public
theorem welcome_proof [HasTreeSyncExecTrace tkt] [HasMlsTreekemInvariants] (tr: ProofTrace) (me: Participant) {l: Nat}
  (tk: TreeKEM Bytes l) (leafDecryptionKey: Bytes) (optPathSecretAndInviterInd: Option (Bytes × Nat)) (leafInd: Nat)
  (res: TreeKEMTreeState Bytes leafInd)
  (h: welcome tk leafDecryptionKey optPathSecretAndInviterInd leafInd = .success res)
  (hsk: IsNodeSkForLeafPk tr me (hpkePk leafDecryptionKey) leafDecryptionKey)
  (hps: ∀ x ∈ optPathSecretAndInviterInd, DecodedPathSecretGood me (hpkePk leafDecryptionKey) x.1 tr)
  (_hli: tk.containsLeafIndex leafInd) (_hleaf: (leafAt tk leafInd).isSome) (_hinv: treekemInvariant tk):
  TreekemTreeStateInvariant tr me res ∧
  (⟨res.levels, res.tree⟩: (l: Nat) × TreeKEM Bytes l) = ⟨l, tk⟩
:= by
  obtain ⟨hpriv, hleaf⟩ := createEmptyPriv_proof tr me l leafDecryptionKey hsk
  unfold welcome at h
  split at h
  · simp only [Result.bind_eq_success, Result.pure_eq_success] at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨hpriv, rfl⟩
  · rename_i pathSecret inviterInd
    split at h
    · simp [Result.error] at h
    split at h
    · simp [Result.error] at h
    simp only [Result.bind_eq_success, Result.pure_eq_success] at h
    obtain ⟨⟨priv, _⟩, h1, _, rfl, rfl⟩ := h
    have := pathApplyPath_proof me tk leafInd _ pathSecret _ tr priv _ h1 hpriv
      (by rw [hleaf]; exact hps _ rfl)
    exact ⟨this.1, rfl⟩

/-! ## Add -/

/-- Port of `add_proof`. -/
public
theorem add_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (lnK: TreeKEMLeaf Bytes)
  (h: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me (add st lnK).1
:= by
  unfold add
  split <;> simp_all [TreekemTreeStateInvariant, TreekemPrivStatePred_pathExtend]

/-! ## Update -/

/-- Port of `update_myself_proof`. -/
public
theorem updateMyself_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (lnK: TreeKEMLeaf Bytes) (leafDecryptionKey: Bytes)
  (hsk: IsNodeSkForLeafPk tr me (hpkePk leafDecryptionKey) leafDecryptionKey)
  (_h: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me (updateMyself st lnK leafDecryptionKey)
:=
  (createEmptyPriv_proof tr me st.levels leafDecryptionKey hsk).1

/-- Port of `update_other_proof`. MLS* requires `i < pow2 st.levels` (here `_hi`) and `i <> leaf_ind`. -/
public
theorem updateOther_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (lnK: TreeKEMLeaf Bytes) (i: Nat)
  (_hi: st.tree.containsLeafIndex i) (_hne: i ≠ leafInd)
  (h: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me (updateOther st lnK i)
:=
  pathBlank_proof tr me st.tree leafInd st.priv i h

/-! ## Remove -/

theorem truncateOne_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (st': {res: TreeKEMTreeState Bytes leafInd // res.levels + 1 = st.levels})
  (h: truncateOne st = some st') (hst: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me st'.val
:= by
  unfold truncateOne at h
  split at h
  · simp at h
  split at h
  · obtain rfl := Option.some.inj h
    exact TreekemPrivStatePred_pathTruncate tr me _ hst
  · simp at h

/-- Port of `fully_truncate_proof`. -/
public
theorem fullyTruncate_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd)
  (h: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me (fullyTruncate st)
:= by
  rw [fullyTruncate]
  split
  · rename_i st' hst' h'
    exact fullyTruncate_proof tr me st' (truncateOne_proof tr me st ⟨st', hst'⟩ h' h)
  · exact h
termination_by st.levels
decreasing_by grind

/-- Port of `remove_proof`. MLS* requires `i < pow2 st.levels` (here `_hi`) and `i <> leaf_ind`. -/
public
theorem remove_proof (tr: ProofTrace) (me: Participant) {leafInd: Nat} (st: TreeKEMTreeState Bytes leafInd) (i: Nat)
  (_hi: st.tree.containsLeafIndex i) (_hne: i ≠ leafInd)
  (h: TreekemTreeStateInvariant tr me st):
  TreekemTreeStateInvariant tr me (remove st i)
:=
  fullyTruncate_proof tr me _ (pathBlank_proof tr me st.tree leafInd st.priv i h)

end Proofs

/-! ## Commit -/

section Commit

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasMlsTreekemInvariants] [HasTreesyncTreekemLinkInvariants]

/--
Port of `process_commit_proof`.
MLS*'s sparse update path `p` is given by `pTs` and `pTk`, related by `pathsyncPathkemRel`
(MLS*'s `update_path_to_treesync p` and `update_path_to_treekem p`).
MLS* requires `li < pow2 st_tk.levels` (here `hli`), `li <> leaf_ind`, `path_filtering_ok st_ts.tree p` (here `hfilter`),
`~(List.Tot.memP leaf_ind excluded_leaves)` and `bytes_invariant tr group_id`.
The refinements of the states (`hstTk`, `hstTs`, `hpend`) give the TreeSync invariants of the new tree.
-/
public
theorem processCommit_proof {groupId: MlsBytes Bytes} {leafInd: Nat} (tr: ProofTrace) (me: Participant)
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd)
  (li: Nat) (pTs: PathSync Bytes tkt stTs.levels) (pTk: PathKEM Bytes stTk.levels)
  (excludedLeaves: List Nat) (groupContext: GroupContext Bytes)
  (pend: TreeSync.API.PendingCommit stTs li pTs) (token: DyAsToken)
  (newStTs: TreeSyncState Bytes tkt DyAsToken groupId) (newStTk: TreeKEMTreeState Bytes leafInd) (commitSecret: Bytes)
  (hTs: TreeSync.API.finalizeCommit pend token = .success newStTs)
  (hTk: commit stTk li pTk excludedLeaves groupContext = .success (newStTk, commitSecret))
  (hli: stTk.tree.containsLeafIndex li) (_hne: li ≠ leafInd) (hfilter: pathFilteringOk stTs.tree li pTs)
  (_hexcluded: leafInd ∉ excludedLeaves)
  (hrel: treesyncTreekemStateRel stTs stTk) (hp: pathsyncPathkemRel pTs pTk)
  (hstTk: stTk.Valid) (hstTs: stTs.TreeValid) (hpend: pend.Valid)
  (hst: TreekemTreeStateInvariant tr me stTk)
  (hext: ExtendedTreesyncInvariant tr me newStTs)
  (hpk: PathkemGoodWeak pTk tr) (hgc: GroupContext.mf.wf (Bytes.Invariant · tr) groupContext)
  (_hgroupId: groupId.val.Invariant tr) (hinv: tr.Invariant):
  TreekemTreeStateInvariant tr me newStTk ∧
  commitSecret.Invariant tr ∧
  (nodeSkLabel newStTs.tree groupId).canFlow (commitSecret.label tr) tr.erase
:= by
  have hvalid := TreeSync.API.finalizeCommit_treeValid pend token newStTs hTs hpend hstTs
  obtain ⟨newTree, h1, rfl⟩ := TreeSync.API.finalizeCommit_success pend token newStTs hTs
  simp only [commit] at hTk
  split at hTk
  · simp [Result.error] at hTk
  simp only [Result.bind_eq_success, Result.pure_eq_success] at hTk
  obtain ⟨⟨pathSecret, level⟩, h2, ⟨newPriv, rootSecret⟩, h3, hres⟩ := hTk
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hres
  simp only [API.stateUpdateTree] at hvalid hext ⊢
  obtain ⟨-, hverif, hwf⟩ := hext
  obtain ⟨hok, hph, hvl⟩ := hvalid
  obtain ⟨-, -, hliTk, -⟩ := hstTk
  induction stTs, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  -- the decrypted path secret, and the new private path
  have hps := getPathSecret_proof me _ leafInd li priv pTk groupContext tr pathSecret level h2 hgc hst hpk
  obtain ⟨hnewPriv, hcs, -⟩ := pathApplyPath_proof me _ leafInd priv pathSecret level tr newPriv _ h3 hst hps
  refine ⟨hnewPriv, hcs.1, ?_⟩
  -- the path secret is decrypted at the least common ancestor of the committer and of `leafInd`
  have hlevel := getPathSecret_findLca_eq _ leafInd li priv pTk groupContext pathSecret level h2
    (by simpa [Tree.containsLeafIndex] using hliTk)
    (by simpa [Tree.containsLeafIndex] using hli)
  rw [findLca_eq_of_position_eq (unAdd (treesyncToTreekem tsTree) excludedLeaves)
    (treeApplyPath (treesyncToTreekem tsTree) li pTk) _ _ (by simp [treeApplyPath_position])]
    at hlevel
  subst hlevel
  -- the new trees are related, and their node keys are good
  have hrelNew := applyPath_treesyncTreekemRel tsTree _ li pTs pTk newTree h1 rfl hp
  have hpos := applyPathAux_position _ _ _ _ _ h1
  apply pathApplyPath_commitSecret_proof me newTree _ leafInd priv pathSecret li groupId tr newPriv _ h3 hst hps
  · exact isAboveTreesyncRoot_applyPathAux tsTree li pTs newTree h1 hfilter
  · simp [leafAt_treeApplyPath_self _ _ _ hli]
  · exact hrelNew
  · exact proveAllTreeKeysGood tr me newTree groupId hverif hok hph hvl hwf hinv
  all_goals simp_all [Tree.containsLeafIndex]

end Commit

/-! ## Create commit -/

section Labels

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/--
Port of `node_sk_label_apply_path_aux_eq`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem nodeSkLabel_applyPathAux_eq {l: Nat} (tBefore tAfter: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (parentParentHash: Bytes) (me: Participant) (groupId: MlsBytes Bytes)
  (hsrc: p.getPathLeaf.data.source = .commit)
  (hcred: credentialToPrincipal p.getPathLeaf.data.credential = some me)
  (h: applyPathAux tBefore li p parentParentHash = .success tAfter) (hli: tBefore.containsLeafIndex li):
  (nodeKeyLabel me p.getPathLeaf.data.content.val).join (nodeSkLabelNocommitter tBefore groupId li) =
    nodeSkLabelNosig tAfter groupId li
:= by
  have hpos := applyPathAux_position _ _ _ _ _ h
  have hleaf := fun i hi => leafAt_applyPathAux tBefore li p parentParentHash i tAfter h hli hi
  have hcommitter: nodeSkLabelAuxLeaf p.getPathLeaf groupId (.noCommitterSignature li) li =
      nodeKeyLabel me p.getPathLeaf.data.content.val := by
    simp [nodeSkLabelAuxLeaf, hcred, hsrc, Label.join_secret_left]
  apply Label.ext
  intro tr
  simp only [Label.joinIsCorrupt, nodeSkLabelNocommitter, nodeSkLabelNosig, nodeSkLabelAux_isCorrupt]
  grind [nodeSkLabelAuxLeaf_of_ne, nodeSkLabelAuxLeaf_noCommitter_self, Tree.containsLeafIndex]

/--
Port of `node_sk_label_apply_path_eq`.
MLS* requires `li: leaf_index l 0` (here `hli`).
-/
theorem nodeSkLabel_applyPath_eq {l: Nat} (tBefore tAfter: TreeSync Bytes tkt l) (li: Nat) (p: PathSync Bytes tkt l)
  (me: Participant) (groupId: MlsBytes Bytes)
  (hsrc: p.getPathLeaf.data.source = .commit)
  (hcred: credentialToPrincipal p.getPathLeaf.data.credential = some me)
  (h: applyPath tBefore li p = .success tAfter) (hli: tBefore.containsLeafIndex li):
  (nodeKeyLabel me p.getPathLeaf.data.content.val).join (nodeSkLabelNocommitter tBefore groupId li) =
    nodeSkLabelNosig tAfter groupId li
:=
  nodeSkLabel_applyPathAux_eq tBefore tAfter li p _ me groupId hsrc hcred h hli

end Labels

section PathToTreeList

variable {Bytes: Type} [CryptoBytes Bytes] {tkt: TreeKEMTypes Bytes}

/--
Port of `pre_pathkem_correct_implies_treesync_invariants_aux`:
the parent hash given to the child is the root parent hash only when the node is blank and the parent hash is the root one.
-/
theorem computeNewNpAndPh_eq_rootParentHash_iff {l: Nat}
  (optExtContent: Option tkt.NodeContent) (sibling: TreeSync Bytes tkt l) (parentParentHash: Bytes)
  (newOptContent: Option (ParentNode Bytes tkt)) (newParentParentHash: Bytes)
  (h: computeNewNpAndPh optExtContent sibling parentParentHash = .success (newOptContent, newParentParentHash)):
  newParentParentHash = rootParentHash.val ↔ (parentParentHash = rootParentHash.val ∧ optExtContent = none)
:= by
  have hspec := computeNewNpAndPh_spec _ _ _ _ _ h
  cases optExtContent with
  | none => grind
  | some extContent =>
    obtain ⟨content, -, -, -, -, hph⟩ := hspec
    obtain ⟨hashInput, -, hhash⟩ := (computeParentHash_eq_success _ _ _ _).mp hph
    have := CryptoBytes.hashHash_ne_empty (serializeNE (ParentHashInput.mf tkt) hashInput)
    grind [rootParentHash]

end PathToTreeList

section Events

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

open MLS.TreeSync.Symbolic.API (TreeEventPre)

/-- `pre_pathkem_correct_implies_treesync_invariants` on the leaf of the path. -/
theorem prePathkemCorrect_implies_treesyncInvariants_leaf (tr: ProofTrace) (me: Participant)
  (ts: TreeSync Bytes tkt 0) (li: Nat) (ln: LeafNode Bytes tkt) (lnK: TreeKEMLeaf Bytes) (groupId: MlsBytes Bytes)
  (hrel: ln.data.content.val = lnK.publicKey) (hcorrect: LeafPkIsCorrect lnK.publicKey me groupId tr)
  (hcred: credentialToPrincipal ln.data.credential = some me) (hsrc: ln.data.source = .commit)
  (hli: ts.containsLeafIndex li):
  TreeEventPre tr groupHasTreeEventPred me groupId li ⟨0, (ChildSiblingView.leaf (some ln) ts.position).pack⟩
:= by
  have := eq_of_containsLeafIndex_zero ts.containsLeafIndex_position hli
  subst this
  intro tr' hle
  have hlabel: nodeSkLabelAuxLeaf ln groupId (.noCommitterSignature ts.position) ts.position = nodeKeyLabel me ln.data.content.val := by
    simp [nodeSkLabelAuxLeaf, hcred, hsrc, Label.join_secret_left]
  obtain ⟨hpub, hlab, husg⟩ := hcorrect
  simp only [groupHasTreeEventPred, mkGroupHasTreeEvent, nodeSkLabelCanonNosig, canonicalizeUnmergedLeaves_zero,
    nodeSkLabelAux_zero, nodeNotBlank_zero, getNodeContent_zero]
  simp [hlabel, hrel]
  grind

/--
Port of `pre_pathkem_correct_implies_treesync_invariants_aux_one_tree`.
MLS*'s `Some? (PNode?.data pre_path)` is the node content `extContent`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem prePathkemCorrect_implies_treesyncInvariants_aux_oneTree (tr: ProofTrace) (me: Participant) {l: Nat}
  (ts: TreeSync Bytes tkt (l+1)) (li: Nat) (extContent: tkt.NodeContent) (psNext: PathSync Bytes tkt l)
  (preNext: PrePathKEM Bytes l) (groupId: MlsBytes Bytes) (parentParentHash: Bytes) (tAfter: TreeSync Bytes tkt (l+1))
  (h: applyPathAux ts li (.node (some extContent) psNext) parentParentHash = .success tAfter)
  (hrel: pathsyncPrePathkemRel psNext preNext)
  (hcorrect: NodePkIsCorrect me preNext.getPathLeaf.publicKey (decide (parentParentHash = rootParentHash.val))
    extContent.val ts groupId li tr)
  (hcred: credentialToPrincipal psNext.getPathLeaf.data.credential = some me)
  (hsrc: psNext.getPathLeaf.data.source = .commit)
  (hli: ts.containsLeafIndex li):
  TreeEventPre tr groupHasTreeEventPred me groupId li ⟨l+1, tAfter⟩
:= by
  have hlabel := nodeSkLabel_applyPathAux_eq ts tAfter li (.node (some extContent) psNext) parentParentHash me groupId
    hsrc hcred h hli
  rw [Path.getPathLeaf, getPathLeaf_pathsyncPrePathkemRel _ _ hrel] at hlabel
  obtain ⟨newOptContent, newParentParentHash, newChild, h1, h2, rfl⟩ := applyPathAux_node _ _ _ _ _ _ h
  obtain ⟨content, rfl, hc, hph, hul, -⟩ := computeNewNpAndPh_spec _ _ _ _ _ h1
  have hnc := Tree.nodeContent_pack_replaceChild ts li (some content) newChild (applyPathAux_position _ _ _ _ _ h2)
  have hcanon: canonicalizeUnmergedLeaves (ChildSiblingView.node (some content) newChild (ts.sibling li)).pack =
      (ChildSiblingView.node (some content) newChild (ts.sibling li)).pack := by
    apply canonicalizeUnmergedLeaves_eq_self
    simp [isUnmergedLeavesCanonicalized, unmergedLeavesOf_eq, hnc, hul]
  obtain ⟨hpub, hflow, husg, hroot⟩ := hcorrect
  rw [nodeSkLabelNosig] at hlabel
  intro tr' hle
  simp only [groupHasTreeEventPred, mkGroupHasTreeEvent, nodeSkLabelCanonNosig, hcanon, nodeNotBlank_succ,
    getNodeContent_succ, getParentHashOf_succ, ← hlabel, hnc, Option.map_some, Option.getD_some, Option.isSome_some, hc,
    true_and]
  grind

/--
Port of `pre_pathkem_correct_implies_treesync_invariants`.
MLS* requires `li: leaf_index l i` (here `hli`).
-/
theorem prePathkemCorrect_implies_treesyncInvariants (tr: ProofTrace) (me: Participant) {l: Nat}
  (ts: TreeSync Bytes tkt l) (li: Nat) (ps: PathSync Bytes tkt l) (prePath: PrePathKEM Bytes l) (groupId: MlsBytes Bytes)
  (parentParentHash: Bytes)
  (hrel: pathsyncPrePathkemRel ps prePath)
  (hcorrect: PrePathkemCorrect me (decide (parentParentHash = rootParentHash.val)) ts li prePath groupId tr)
  (happly: ∃ t', applyPathAux ts li ps parentParentHash = .success t')
  (hcred: credentialToPrincipal ps.getPathLeaf.data.credential = some me)
  (hsrc: ps.getPathLeaf.data.source = .commit)
  (hli: ts.containsLeafIndex li):
  PathToTreeListPreAux (TreeEventPre tr groupHasTreeEventPred me groupId li) ts li ps parentParentHash
:= by
  intro tl htl
  obtain ⟨t', ht'⟩ := happly
  induction ts, ps, parentParentHash, tl, t', htl, ht' using pathToTreeListAux_induction (Bytes := Bytes) (tkt := tkt) li with
  | leaf ts ln parentParentHash =>
    cases prePath with | leaf lnK =>
    intro x hx
    obtain rfl := List.mem_singleton.mp hx
    exact prePathkemCorrect_implies_treesyncInvariants_leaf tr me ts li ln lnK groupId hrel hcorrect hcred hsrc hli
  | blank t pNext parentParentHash _ _ _ _ _ _ _ ih =>
    cases prePath with | node opk preNext =>
    obtain ⟨hrelNext, rfl⟩ := hrel
    exact ih preNext hrelNext hcorrect.2 hcred hsrc (Tree.mem_child_self t hli)
  | nonBlank t extContent pNext parentParentHash _ newParentParentHash _ _ _ _ _ ht' hcn ih =>
    cases prePath with | node opk preNext =>
    obtain ⟨hrelNext, rfl⟩ := hrel
    obtain ⟨hnode, hcorrectNext⟩ := hcorrect
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact prePathkemCorrect_implies_treesyncInvariants_aux_oneTree tr me t li extContent pNext preNext groupId _ _ ht'
        hrelNext hnode hcred hsrc hli
    · have: decide (newParentParentHash = rootParentHash.val) = false := by
        simp [computeNewNpAndPh_eq_rootParentHash_iff _ _ _ _ _ hcn]
      rw [← this] at hcorrectNext
      exact ih preNext hrelNext hcorrectNext hcred hsrc (Tree.mem_child_self t hli) x hx

end Events

section ExternalPath

variable [HasSymbolicBytes]

/--
Port of `pathsync_pre_pathkem_rel_external_path_to_path_nosig`.
MLS*'s `match external_path_to_path_nosig t ps` is the success hypothesis `h`.
-/
theorem pathsyncPrePathkemRel_externalPathToPathNosig {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (ps: ExternalPathSync Bytes tkt l) (pk: PrePathKEM Bytes l) (res: PathSync Bytes tkt l)
  (h: externalPathToPathNosig t li ps = .success res)
  (hsource: ps.getPathLeaf.source = .update) (hrel: externalPathsyncPrePathkemRel ps pk):
  pathsyncPrePathkemRel res pk
:= by
  obtain ⟨ph, -, rfl⟩ := externalPathToPathNosig_eq_success t li ps res h
  apply pathsyncPrePathkemRel_externalPathToPathAux _ ps pk hsource _ hrel
  exact getPathLeaf_externalPathsyncPrePathkemRel ps pk hrel

/--
Port of `credential_get_path_leaf_external_path_to_path_nosig`.
It also gives the source of the leaf (`LNS_commit`), which MLS* gets from the specification of `external_path_to_path_nosig`.
-/
theorem credential_getPathLeaf_externalPathToPathNosig {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (p: ExternalPathSync Bytes tkt l) (res: PathSync Bytes tkt l)
  (h: externalPathToPathNosig t li p = .success res):
  res.getPathLeaf.data.credential = p.getPathLeaf.credential ∧ res.getPathLeaf.data.source = .commit
:= by
  obtain ⟨ph, -, rfl⟩ := externalPathToPathNosig_eq_success t li p res h
  simp

/-- Port of `external_path_to_path_succeeds_implies`. -/
public
theorem externalPathToPath_succeeds_implies {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l)
  (groupId: MlsBytes Bytes) (signKey nonce: Bytes) (res: PathSync Bytes tkt l)
  (h: externalPathToPath t li p groupId signKey nonce = .success res):
  (∃ authP, externalPathToPathNosig t li p = .success authP) ∧ li < 2^32
:= by
  obtain ⟨ph, -, hph, hli, -, -⟩ := externalPathToPath_eq_success t li p groupId signKey nonce res h
  refine ⟨?_, hli⟩
  simp [externalPathToPathNosig, externalPathToPathAuxNosig, hph, mkMlsBytes_eq_success]
  exact ⟨_, ph.property, rfl⟩

end ExternalPath

section Filter

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/--
Port of `treekem_to_treesync_lemmas_bis`.
MLS*'s `is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) ln_data` is `hwf`.
-/
theorem treekemToTreesync_lemmas_bis (me: Participant) (isAtRoot: Bool) {l: Nat} (t: TreeSync Bytes tkt l) (li: Nat)
  (lnData: LeafNodeData Bytes tkt) (p: PrePathKEM Bytes l) (groupId: MlsBytes Bytes) (tr: ProofTrace)
  (res: ExternalPathSync Bytes tkt l) (h: treekemToTreesync lnData p = .success res)
  (hwf: (LeafNodeData.mf tkt).wf (Bytes.Publishable · tr) lnData)
  (hcorrect: PrePathkemCorrect me isAtRoot t li p groupId tr):
  pathIsFilterValid t li res ∧ (ExternalPathSync.mf tkt l).wf (Bytes.Publishable · tr) res
:= by
  induction p generalizing isAtRoot with
  | leaf mi =>
    simp only [treekemToTreesync, Result.bind_eq_success, Result.pure_eq_success, mkMlsBytes_eq_success] at h
    obtain ⟨content, hc, rfl⟩ := h
    obtain ⟨hpub, -, -⟩ := hcorrect
    refine ⟨?_, ?_⟩
    · unfold pathIsFilterValid
      simp [Tree.intoChildSiblingView_zero]
    · simp only [Path.mf.wf_leaf, LeafNodeData.mf.wf_eq] at hwf ⊢
      grind [TreeKEM.tkt.mfLeafContent.wf_eq]
  | node okp pNext ih =>
    simp only [treekemToTreesync, Result.bind_eq_success, Result.pure_eq_success] at h
    obtain ⟨next, h1, rfl⟩ := h
    cases okp with
    | none =>
      obtain ⟨hsib, hnext⟩ := hcorrect
      have := ih (t := t.child li) _ next h1 hnext
      erw [pathIsFilterValid_node, Path.mf.wf_node]
      grind [MlsOption.mf.wf_eq]
    | some nodePk =>
      obtain ⟨⟨hpub, -⟩, hnext⟩ := hcorrect
      have := ih (t := t.child li) _ next h1 hnext
      have hw: (MlsOption.mf (TreeKEM.tkt (Bytes := Bytes)).mfNodeContent).wf (Bytes.Publishable · tr) (some nodePk) := by
        rw [MlsOption.mf.wf_eq]
        exact (TreeKEM.tkt.mfNodeContent.wf_eq (Bytes.Publishable · tr) nodePk).mpr hpub
      erw [pathIsFilterValid_node, Path.mf.wf_node]
      refine ⟨?_, hw, this.2⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inl rfl, this.1⟩

end Filter

section PrepareCreateCommit

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

open MLS.TreeSync.Symbolic.API (TreeEventPre ExternalPathHasEventPre)

/--
Port of `prepare_create_commit_rand_good`.
MLS*'s `dest_randomness` always succeeds on its typed randomness: here, the properties are stated on its results.
MLS*'s `if Cons? path_usages then … else …` are `PathSecretUsage.headLabel` and `List.tail`.
-/
@[expose]
public
def PrepareCreateCommitRandGood (tr: ProofTrace) (me: Participant) (randPrepare: Randomness Bytes)
  (pathUsages: PathSecretUsage): Prop :=
  ∀ leafSk rand1, destRandomness randPrepare = .success (leafSk, rand1) →
  ∀ pathSecret0 rand2, destRandomness rand1 = .success (pathSecret0, rand2) →
    leafSk.Invariant tr ∧
    (leafSk.label tr).equivalent (nodeKeyLabel me (hpkePk leafSk)) tr.erase ∧
    leafSk.HasUsage nodeKeyUsage tr ∧
    pathSecret0.Invariant tr ∧
    (pathSecret0.label tr).equivalent ((nodeKeyLabel me (hpkePk leafSk)).join pathUsages.headLabel) tr.erase ∧
    pathSecret0.HasUsage (PathSecretUsage.toUsage pathUsages.tail) tr

/-- `prepare_create_commit_rand_good` stays true when the trace grows (MLS* uses SMT patterns). -/
public
theorem PrepareCreateCommitRandGood_later (tr1 tr2: ProofTrace) (me: Participant) (randPrepare: Randomness Bytes)
  (pathUsages: PathSecretUsage)
  : tr1 ≤ tr2 →
    PrepareCreateCommitRandGood tr1 me randPrepare pathUsages →
    PrepareCreateCommitRandGood tr2 me randPrepare pathUsages
:= by
  intro hle h leafSk rand1 h1 pathSecret0 rand2 h2
  have := h leafSk rand1 h1 pathSecret0 rand2 h2
  grind

grind_pattern PrepareCreateCommitRandGood_later => tr1 ≤ tr2, PrepareCreateCommitRandGood tr1 me randPrepare pathUsages
grind_pattern [grind_later] PrepareCreateCommitRandGood_later =>
  tr1 ≤ tr2,
  PrepareCreateCommitRandGood tr1 me randPrepare pathUsages

/--
Port of `pending_commit_good`.
MLS*'s conjunct `st_ts.levels == st_tk.levels` is the equality `h`, used to cast the path secrets.
-/
public
def PendingCommitGood {groupId: MlsBytes Bytes} {leafInd: Nat} (tr: ProofTrace) (me: Participant)
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd) (tkPend: PendingCommit stTk): Prop :=
  ∃ h: stTk.levels = stTs.levels,
    PathSecretsAreCorrect me true stTs.tree leafInd groupId (h ▸ tkPend.pathSecrets) tr ∧
    tkPend.commitSecret.Invariant tr ∧
    (tkPend.commitSecret.label tr).equivalent
      ((nodeKeyLabel me (hpkePk tkPend.pathSecrets.getPathLeaf)).join (nodeSkLabelNocommitter stTs.tree groupId leafInd))
      tr.erase

/-- `pending_commit_good` stays true when the trace grows (MLS* uses SMT patterns). -/
public
theorem PendingCommitGood_later {groupId: MlsBytes Bytes} {leafInd: Nat} (tr1 tr2: ProofTrace) (me: Participant)
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd) (tkPend: PendingCommit stTk)
  : tr1 ≤ tr2 →
    PendingCommitGood tr1 me stTs stTk tkPend →
    PendingCommitGood tr2 me stTs stTk tkPend
:= by
  intro hle ⟨h, h1, h2, h3⟩
  exact ⟨h, PathSecretsAreCorrect_later _ _ _ _ _ _ tr1 tr2 hle h1, by grind, by grind⟩

grind_pattern PendingCommitGood_later => tr1 ≤ tr2, PendingCommitGood tr1 me stTs stTk tkPend
grind_pattern [grind_later] PendingCommitGood_later => tr1 ≤ tr2, PendingCommitGood tr1 me stTs stTk tkPend

variable [TraceInvariant] [HasMlsTreekemInvariants]

/--
Port of `prepare_create_commit_proof`.
MLS*'s refinement `st_ts.levels == st_tk.levels` is `hl`, used to cast the external path.
MLS*'s `match treekem_to_treesync ln_data pre_path` is an implication.
The refinement `stTk.Valid` gives `leaf_ind < pow2 st_tk.levels`.
-/
public
theorem prepareCreateCommit_proof {groupId: MlsBytes Bytes} {leafInd: Nat} (tr: ProofTrace) (me: Participant)
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd) (hl: stTs.levels = stTk.levels)
  (randPrepare: Randomness Bytes) (lnData: LeafNodeData Bytes tkt)
  (pend: PendingCommit stTk) (prePath: PrePathKEM Bytes stTk.levels)
  (h: prepareCreateCommit stTk randPrepare = .success (pend, prePath))
  (_hsrc: lnData.source = .update) (hcred: credentialToPrincipal lnData.credential = some me)
  (hwf: (LeafNodeData.mf tkt).wf (Bytes.Publishable · tr) lnData)
  (hrel: treesyncTreekemStateRel stTs stTk) (_hst: TreekemTreeStateInvariant tr me stTk) (hstTk: stTk.Valid)
  (hrand: PrepareCreateCommitRandGood tr me randPrepare (computePathSecretUsage stTs.tree groupId leafInd []))
  (_hinv: tr.Invariant):
  PendingCommitGood tr me stTs stTk pend ∧
  ∀ externalPath, treekemToTreesync lnData prePath = .success externalPath →
    externalPath.getPathLeaf = { lnData with content := externalPath.getPathLeaf.content } ∧
    ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr me stTs.tree leafInd (hl ▸ externalPath) groupId ∧
    pathIsFilterValid stTs.tree leafInd (hl ▸ externalPath) ∧
    (ExternalPathSync.mf tkt stTk.levels).wf (Bytes.Publishable · tr) externalPath ∧
    externalPathsyncPathSecretsRel externalPath pend.pathSecrets
:= by
  obtain ⟨-, -, hliTk, -⟩ := hstTk
  simp only [prepareCreateCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at h
  obtain ⟨⟨leafSk, rand1⟩, hd1, ⟨pathSecret0, rand2⟩, hd2, ⟨pathSecrets, commitSecret⟩, hgen, preUpdPath, hpre, rfl, rfl⟩ := h
  obtain ⟨hlsInv, hlsLabel, hlsUsg, hps0Inv, hps0Label, hps0Usg⟩ := hrand leafSk rand1 hd1 pathSecret0 rand2 hd2
  induction stTs, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  have hli: tsTree.containsLeafIndex leafInd := by simpa [Tree.containsLeafIndex] using hliTk
  obtain ⟨hp, hcsInv, -, hcsLabel, hleaf⟩ := generatePathSecrets_proof me tsTree _ leafSk pathSecret0 leafInd groupId tr []
    pathSecrets commitSecret hgen rfl hli ⟨hlsInv, hlsLabel, hlsUsg⟩ hps0Inv hps0Label hps0Usg
  obtain ⟨hpreCorrect, -⟩ := pathSecretsToPrePathkem_proof me true tsTree leafInd pathSecrets groupId tr preUpdPath hpre hp
  refine ⟨⟨rfl, hp, hcsInv, ?_⟩, ?_⟩
  · simpa [hleaf, PathSecretUsage.headLabel, Label.join_secret_right] using hcsLabel
  intro externalPath hext
  obtain ⟨⟨content, -, hleafEq⟩, hrelExt⟩ := treekemToTreesync_lemmas lnData preUpdPath externalPath hext
  obtain ⟨hfilter, hwfExt⟩ := treekemToTreesync_lemmas_bis me true tsTree leafInd lnData preUpdPath groupId tr
    externalPath hext hwf hpreCorrect
  refine ⟨by rw [hleafEq], ?_, hfilter, hwfExt, ⟨preUpdPath, hpre, hrelExt⟩⟩
  intro hsource _ authP hauth
  obtain ⟨hcredAuth, hsrcAuth⟩ := credential_getPathLeaf_externalPathToPathNosig tsTree leafInd externalPath authP hauth
  refine ⟨by simp [leafNodeSignedEventPred, hsrcAuth], ?_⟩
  apply prePathkemCorrect_implies_treesyncInvariants tr me tsTree leafInd authP preUpdPath groupId rootParentHash.val
  · exact pathsyncPrePathkemRel_externalPathToPathNosig tsTree leafInd externalPath preUpdPath authP hauth hsource hrelExt
  · simpa using hpreCorrect
  · obtain ⟨ph, hph, rfl⟩ := externalPathToPathNosig_eq_success tsTree leafInd externalPath authP hauth
    rw [exists_applyPathAux_iff, computeLeafParentHashFromPath_setPathLeaf]
    exact ⟨_, hph⟩
  all_goals simp_all

/--
Port of `create_commit_proof`.
MLS*'s refinement `st_ts.levels == st_tk.levels` is `hl`, used to cast the arguments of the ghost data of the randomness;
the leaf index of `auth_path` (implicit in MLS*) is `leafInd`.
MLS*'s `excluded_pre added_leaves` and `forget_path_secrets` are inlined in the TreeKEM tree given to
`encryptPathSecretsEntropyGhostData` (see `MLS.TreeKEM.SymbolicProofs.Tree.Operations`).
The refinements of the states (`hstTs`, `hstTk`) give the TreeSync invariants and `leaf_ind < pow2 st_tk.levels`.
-/
public
theorem createCommit_proof [HasTreesyncTreekemLinkInvariants] {groupId: MlsBytes Bytes} {leafInd: Nat}
  (tr: ProofTrace) (me: Participant)
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd) (hl: stTs.levels = stTk.levels)
  (tkPend: PendingCommit stTk) (addedLeaves: List Nat) (groupContext: GroupContext Bytes) (randFinalize: Randomness Bytes)
  (authPath: PathSync Bytes tkt stTs.levels) (tsPend: TreeSync.API.PendingCommit stTs leafInd authPath) (token: DyAsToken)
  (tsRes: TreeSyncState Bytes tkt DyAsToken groupId) (tkRes: CreateCommitResult stTk)
  (hTs: TreeSync.API.finalizeCommit tsPend token = .success tsRes)
  (hTk: finalizeCreateCommit tkPend addedLeaves groupContext randFinalize = .success tkRes)
  (hsrc: authPath.getPathLeaf.data.source = .commit)
  (hcred: credentialToPrincipal authPath.getPathLeaf.data.credential = some me)
  (hpend: PendingCommitGood tr me stTs stTk tkPend)
  (hleafPk: hpkePk tkPend.pathSecrets.getPathLeaf = authPath.getPathLeaf.data.content.val)
  (hext: ExtendedTreesyncInvariant tr me stTs) (hrel: treesyncTreekemStateRel stTs stTk)
  (hstTs: stTs.TreeValid) (hstTk: stTk.Valid)
  (hgc: GroupContext.mf.wf (Bytes.Invariant · tr) groupContext) (_hgroupId: groupId.val.Invariant tr)
  (hrand: RandomnessHasGhostData tr randFinalize
    (encryptPathSecretsEntropyGhostData stTs.tree (hl ▸ unAdd stTk.tree addedLeaves) leafInd (hl ▸ tkPend.pathSecrets) groupId))
  (hinv: tr.Invariant):
  PathkemGood tkRes.updatePath tr ∧
  TreekemTreeStateInvariant tr me tkRes.newState ∧
  tkRes.commitSecret.Invariant tr ∧
  (tkRes.commitSecret.label tr).equivalent (nodeSkLabelNosig tsRes.tree groupId leafInd) tr.erase ∧
  PathSecretsGoodForJoiners tr stTs.tree groupId addedLeaves tkRes.addedLeavesPathSecrets
:= by
  obtain ⟨newTree, h1, rfl⟩ := TreeSync.API.finalizeCommit_success tsPend token tsRes hTs
  simp only [finalizeCreateCommit, Result.bind_eq_success, Result.pure_eq_success] at hTk
  obtain ⟨⟨updatePath, newPriv⟩, h2, addedLeavesPathSecrets, h3, rfl⟩ := hTk
  obtain ⟨-, -, hliTk, -⟩ := hstTk
  obtain ⟨-, hverif, hwf⟩ := hext
  obtain ⟨hok, hph, hvl⟩ := hstTs
  obtain ⟨_, hp, hcsInv, hcsLabel⟩ := hpend
  induction stTs, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  have hli: tsTree.containsLeafIndex leafInd := by simpa [Tree.containsLeafIndex] using hliTk
  have hgood := proveAllTreeKeysGood tr me tsTree groupId hverif hok hph hvl hwf hinv
  have hpub := encryptPathSecrets_pub_proof me true tsTree _ leafInd tkPend.pathSecrets groupContext groupId
    addedLeaves randFinalize tr updatePath newPriv h2 rfl hp hgood hgc hrand
  obtain ⟨hpriv, -⟩ := encryptPathSecrets_priv_proof me true tsTree _ leafInd tkPend.pathSecrets groupContext groupId
    randFinalize tr updatePath newPriv h2 hp
  have hlabel := nodeSkLabel_applyPath_eq tsTree newTree leafInd authPath me groupId hsrc hcred h1 hli
  rw [← hleafPk] at hlabel
  refine ⟨hpub, hpriv, hcsInv, hlabel ▸ hcsLabel, ?_⟩
  exact getPathSecretOfAddedLeaves_proof me true tsTree _ leafInd tkPend.pathSecrets addedLeaves groupId tr _ h3 rfl hli hp

end PrepareCreateCommit

end MLS.TreeKEM.Symbolic.API.Tree
