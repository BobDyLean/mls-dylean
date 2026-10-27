module

public import MLS.TreeKEM.SymbolicSpec.Traceful.GenerateCommitWelcome
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessCommit
public import MLS.TreeKEM.SymbolicSpecProofs.API.Tree
public import MLS.Bootstrap.SymbolicProofs.GroupInfo
public import MLS.Symbolic.SymbolicProofs.Randomness
import all MLS.TreeKEM.SymbolicSpec.Traceful.GenerateCommitWelcome
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.Bootstrap.SymbolicSpec.KeyPackage
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.GenerateCommitWelcome.Proof`.

Port-specific differences:
- The proofs are DyLean Hoare triples, assuming the invariants of
  `MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants` (MLS*'s `has_treesync_and_treekem_invariants`).
  The Hoare triples mentioning a principal that is not an argument of the function are not instances
  (see `MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessCommit`).
-/

-- The proofs assume the bundles of MLS*'s `has_treesync_and_treekem_invariants` as section variables;
-- each proof only uses some of them.
set_option linter.unusedSectionVars false

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap MLS.TreeKEM.Symbolic.API.KeySchedule MLS.TreeKEM.Symbolic.API.Tree

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasTreesyncInvariants tkt] [HasTreeKEMProofTrace]
variable [HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant]
variable [HasBootstrapCryptoInvariants] [HasMlsTreekemInvariants] [HasMlsPskInvariants]
variable [SignWithLabelPred.Has groupInfoSignPred]

/-! ## Welcome and Commit generation, proofs -/

/-- Port of `_create_group_info_proof`. -/
@[instance]
public
theorem createGroupInfo'.proof (me: Participant) (st: TreeSyncTreeKEMState) (params: CreateGroupInfoParameters):
  HoareTriple
    (createGroupInfo' me st params)
    (fun tr =>
      (∀ e ∈ params.groupInfoExtensions.val, Extension.mf.wf (Bytes.Publishable · tr) e) ∧
      GroupInfoSignPredAux tr.erase me st.groupContext st.treekem.keyscheduleState.epochKeys.confirmationTag ∧
      TreesyncTreekemStateAllInvariants tr me st
    )
    (fun groupInfo tr => GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo)
:= by
  unfold createGroupInfo'
  step
  step
  step_intro
  step
  step with ⟨ fun _ => Label.secret, Usage.sigNonce ⟩
  step
  step
  obtain ⟨hext, hpred, hinv⟩ := ‹(∀ e ∈ params.groupInfoExtensions.val, _) ∧ _›
  have hct := (mkMlsBytes_eq_success _ _ _ _).1 ‹mkMlsBytes _ "_create_group_info" "confirmation_tag" = _›
  apply signWelcomeGroupInfo_proof tr me signatureKey groupInfoTbs signatureNonce _ ‹_› (by simpa [groupInfoTbs, ← hct] using hpred)
    ‹_› _ ‹_› ‹_› (by grind)
  simp only [groupInfoTbs, GroupInfoTBS.mf.wf_eq]
  grind [TreesyncTreekemStateAllInvariants, TreesyncTreekemStateInvariant, TreesyncTreekemStateInvariantAux,
    TreesyncTreekemStateCoarseInvariant, TreekemKeyscheduleStateGood]

/-- The key packages of a list are publishable (stated with a definition, so that `step` can monotonize it). -/
@[expose]
public
def KeyPackagesArePublishable (tr: ProofTrace) (l: List (KeyPackage Bytes tkt)): Prop :=
  ∀ kp ∈ l, (KeyPackage.mf tkt).wf (Bytes.Publishable · tr) kp

public
theorem KeyPackagesArePublishable_later (tr1 tr2: ProofTrace) (l: List (KeyPackage Bytes tkt))
  : tr1 ≤ tr2 →
    KeyPackagesArePublishable tr1 l →
    KeyPackagesArePublishable tr2 l
:= by
  grind [KeyPackagesArePublishable]

grind_pattern KeyPackagesArePublishable_later => tr1 ≤ tr2, KeyPackagesArePublishable tr1 l
grind_pattern [grind_later] KeyPackagesArePublishable_later => tr1 ≤ tr2, KeyPackagesArePublishable tr1 l

/-- The ghost data and the lengths of the randomness of `encrypt_welcome` have the same length. -/
theorem encryptGroupSecretsEntropyGhostData_length (l: List (KeyPackage Bytes tkt × Option Bytes)):
  (encryptGroupSecretsEntropyGhostData l).length = (encryptWelcomeEntropyLength l).length
:= by
  induction l with
  | nil => rfl
  | cons h t ih => simp [encryptGroupSecretsEntropyGhostData, encryptWelcomeEntropyLength, ih]

public
instance (st: TreeSyncTreeKEMState) (groupInfo: GroupInfo Bytes) (params: CreateWelcomeParameters):
  HasGhostArgumentType (createWelcome' st groupInfo params) Participant
where
  dummy := ()

/--
Port of `_create_welcome_proof`.
MLS*'s `for_allP (is_well_formed _ (is_publishable tr))` is `KeyPackagesArePublishable`.
The principal `me` (not an argument of the function) is the ghost argument.
-/
@[instance]
public
theorem createWelcome'.proof (me: Participant) (st: TreeSyncTreeKEMState) (groupInfo: GroupInfo Bytes)
  (params: CreateWelcomeParameters):
  HoareTripleGhost
    (createWelcome' st groupInfo params)
    me
    (fun tr =>
      params.joinerSecret.Invariant tr ∧
      GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo ∧
      KeyPackagesArePublishable tr (params.joinersAndPathSecrets.map (·.1)) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (params.joinersAndPathSecrets.map (·.1)) ∧
      AllOptPathSecretGood tr params.joinersAndPathSecrets ∧
      params.joinerSecret.KnowableBy
        (((params.joinersAndPathSecrets.map (·.1)).map keyPackageToInitLabel).foldr Label.join Label.secret) tr ∧
      PsksBytesInvariant tr params.psks
    )
    (fun optWelcome tr => ∀ welcome ∈ optWelcome, Welcome.mf.wf (Bytes.Publishable · tr) welcome)
:= by
  apply HoareTripleGhost.mk
  unfold createWelcome'
  split
  · step
    subst x
    simp
  · step
    step with ⟨ encryptGroupSecretsEntropyGhostData params.joinersAndPathSecrets ⟩ by
      exact encryptGroupSecretsEntropyGhostData_length _
    step
    step
    subst x
    intro welcome hw
    obtain rfl := Option.mem_some_iff.mp hw
    obtain ⟨hjs, hgi, hkps, hver, hps, hlab, hpsks⟩ := ‹params.joinerSecret.Invariant tr ∧ _›
    exact encryptWelcome_proof tr me groupInfo params.joinerSecret params.psks params.joinersAndPathSecrets
      encryptWelcomeRand welcomeMsg ‹_› hjs hgi hkps hver hps hlab hpsks ‹_› ‹_›

/-- The event predicate of leaf node signatures stays true when the trace grows. -/
theorem leafNodeSignedEventPred_later (tr1 tr2: ProofTrace) (ev: LeafNodeSignedEvent tkt)
  : tr1 ≤ tr2 →
    leafNodeSignedEventPred tr1 ev →
    leafNodeSignedEventPred tr2 ev
:= by
  unfold leafNodeSignedEventPred
  split <;> grind

grind_pattern leafNodeSignedEventPred_later => tr1 ≤ tr2, leafNodeSignedEventPred tr1 ev
grind_pattern [grind_later] leafNodeSignedEventPred_later => tr1 ≤ tr2, leafNodeSignedEventPred tr1 ev

/-- `external_path_has_event_pre` (with the event predicates of TreeKEM) stays true when the trace grows. -/
theorem ExternalPathHasEventPre_later {l: Nat} (tr1 tr2: ProofTrace) (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes)
  : tr1 ≤ tr2 →
    Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr1 prin t li p groupId →
    Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr2 prin t li p groupId
:= by
  intro hle h hsrc hli authP hauth
  obtain ⟨h1, h2⟩ := h hsrc hli authP hauth
  exact ⟨leafNodeSignedEventPred_later _ _ _ hle h1,
    PathToTreeListPre.weaken _ _ _ h2 (fun _ hx => Symbolic.API.TreeEventPre_later _ _ _ _ _ _ _ hle hx)⟩

grind_pattern ExternalPathHasEventPre_later =>
  tr1 ≤ tr2,
  Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr1 prin t li p groupId
grind_pattern [grind_later] ExternalPathHasEventPre_later =>
  tr1 ≤ tr2,
  Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr1 prin t li p groupId

/-- The precondition of `triggerExternalPathEvents.proof`, from `external_path_has_event_pre`. -/
theorem ExternalPathHasEventPreLater_of {l: Nat} (tr: ProofTrace) (prin: Participant)
  (t: TreeSync Bytes tkt l) (li: Nat) (p: ExternalPathSync Bytes tkt l) (groupId: MlsBytes Bytes)
  (h: Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr prin t li p groupId):
  Symbolic.API.ExternalPathHasEventPreLater tr prin t li p groupId
:= by
  intro tr' hle
  rw [ProtocolEvent.EventInv.Has.invariant_eq_fun (pred := leafNodeSignedEventPred),
    ProtocolEvent.EventInv.Has.invariant_eq_fun (pred := groupHasTreeEventPred)]
  exact ExternalPathHasEventPre_later _ _ _ _ _ _ _ hle h

/--
Port of `_update_path_external_pathsync_to_pathsync_proof`.
MLS*'s refinement `st.treesync.levels == l` is the equality `hl` of the precondition, used to cast the external path.
-/
@[instance]
public
theorem updatePathExternalPathsyncToPathsync'.proof {l: Nat} (me: Participant) (st: TreeSyncTreeKEMState) (li: Nat)
  (externalPath: ExternalPathSync Bytes tkt l):
  HoareTriple
    (updatePathExternalPathsyncToPathsync' me st li externalPath)
    (fun tr =>
      ∃ hl: st.treesync.levels = l,
        credentialToPrincipal externalPath.getPathLeaf.credential = some me ∧
        externalPath.getPathLeaf.source = .update ∧
        Symbolic.API.ExternalPathHasEventPre leafNodeSignedEventPred groupHasTreeEventPred tr me st.treesync.tree li
          (hl ▸ externalPath) st.groupContext.groupId ∧
        pathIsFilterValid st.treesync.tree li (hl ▸ externalPath) ∧
        (ExternalPathSync.mf tkt l).wf (Bytes.Publishable · tr) externalPath ∧
        TreesyncTreekemStateInvariant tr me st
    )
    (fun pathsync tr =>
      (PathSync.mf tkt l).wf (Bytes.Publishable · tr) pathsync ∧
      externalPathsyncPathsyncRel externalPath pathsync ∧
      pathsync.getPathLeaf.data.source = .commit ∧
      credentialToPrincipal pathsync.getPathLeaf.data.credential = some me
    )
:= by
  unfold updatePathExternalPathsyncToPathsync'
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr ⟨hl, _⟩ _
    exact absurd hl ‹_›
  rename_i hl
  subst hl
  apply HoareTriple.mk
  intro tr ⟨_, hpre⟩ hinv
  step
  step
  step_intro
  step by
    obtain ⟨-, -, hev, -⟩ := ‹credentialToPrincipal _ = some me ∧ _›
    exact ExternalPathHasEventPreLater_of _ _ _ _ _ _ hev
  step
  step with ⟨ fun _ => Label.secret, Usage.sigNonce ⟩
  step
  step
  step
  step
  subst x
  obtain ⟨hcred, hsrc, -, hfilter, hp, hinv⟩ := ‹credentialToPrincipal _ = some me ∧ _›
  have hli := (TreesyncTreekemStateInvariant.containsLeafIndex_iff tr me st hinv li).2
  obtain ⟨⟨hok, -⟩, -, -, -, hgc, hts, -⟩ := hinv
  rw [GroupContext.mf.wf_eq] at hgc
  obtain ⟨hrel, ph, hdata⟩ := authenticateExternalPath_externalPathsyncPathsyncRel st.treesync li _ _ _ _
    ‹TreeSync.API.authenticateExternalPath _ _ _ _ _ = _› ‹_›
  refine ⟨?_, hrel, by rw [hdata], by rw [hdata]; exact hcred⟩
  exact externalPathToPath_wf me Label.pub tr st.treesync.tree li _ st.groupContext.groupId signatureKey signatureNonce _
    ‹TreeSync.API.authenticateExternalPath _ _ _ _ _ = _› (by grind) hfilter hok ‹_› hts hp hgc.1 ‹_› ‹_› ‹_›
    (by grind)

/--
Port of `_generate_update_path_path_proof`.
It also states the refinement of MLS*'s `pending_create_commit` (`PendingCreateCommit.Valid`).
-/
@[instance]
public
theorem generateUpdatePathPath'.proof (me: Participant) (st: TreeSyncTreeKEMState):
  HoareTriple
    (generateUpdatePathPath' me st)
    (fun tr => TreesyncTreekemStateInvariant tr me st)
    (fun (pathsync, pendingCreateCommit) tr =>
      (PathSync.mf tkt st.treekem.treeState.levels).wf (Bytes.Publishable · tr) pathsync ∧
      PendingCommitGood tr me st.treesync st.treekem.treeState pendingCreateCommit.pend ∧
      pendingCreateCommit.Valid ∧
      pathsyncPathSecretsRel pathsync pendingCreateCommit.pend.pathSecrets ∧
      pathsync.getPathLeaf.data.source = .commit ∧
      credentialToPrincipal pathsync.getPathLeaf.data.credential = some me
    )
:= by
  unfold generateUpdatePathPath'
  step
  split
  · rename_i myOldLeafNode hold
    step_intro
    step with ⟨ computePathSecretUsage st.treesync.tree st.groupContext.groupId st.leafIndex [] ⟩
    step
    split
    rename_i pendingCreateCommit preUpdatePath _
    step
    have hl := ‹st.treesync.levels = st.treekem.treeState.levels›
    have hinv := ‹TreesyncTreekemStateInvariant tr me st›
    obtain ⟨-, htk, hrel, hme, -, hts, -, -, hpriv⟩ := hinv
    have hcred: credentialToPrincipal myOldLeafNode.data.credential = some me := by
      obtain ⟨ln, hln, hcred⟩ := hme
      grind
    have hwf: (LeafNodeData.mf tkt).wf (Bytes.Publishable · tr) myNewLeafPackageData := by
      have := leafAt_wf _ _ st.leafIndex hts
      simp only [hold, MlsOption.mf.wf_eq, LeafNode.mf.wf_eq, LeafNodeData.mf.wf_eq] at this
      simp only [myNewLeafPackageData, LeafNodeData.mf.wf_eq]
      refine ⟨?_, this.1.2.1, this.1.2.2.1, by simp, this.1.2.2.2.2⟩
      have := BytesCompatiblePred.pred_empty (pred := (Bytes.Publishable · tr))
      grind [tkt.mfLeafContent.wf_eq, MlsBytes.empty]
    have hpcc: TreeKEM.API.Tree.prepareCreateCommit st.treekem.treeState prepareCreateCommitRand =
        .success (pendingCreateCommit.pend, preUpdatePath) := by
      have := ‹API.prepareCreateCommit st.treekem prepareCreateCommitRand = _›
      simp only [API.prepareCreateCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at this
      obtain ⟨⟨pend, path⟩, h1, h2, rfl⟩ := this
      subst h2
      exact h1
    obtain ⟨hgood, hext⟩ := prepareCreateCommit_proof tr me st.treesync st.treekem.treeState hl prepareCreateCommitRand
      myNewLeafPackageData _ _ hpcc rfl hcred hwf hrel hpriv htk ‹_› ‹_›
    obtain ⟨hleafEq, hev, hfilter, hwfExt, hsecrets⟩ := hext externalPath ‹_›
    step by
      exact ⟨hl, by rw [hleafEq]; exact hcred, by rw [hleafEq], hev, hfilter, hwfExt, ‹_›⟩
    step
    subst x
    refine ⟨‹_›, ‹_›, API.prepareCreateCommit_valid _ _ _ _ ‹API.prepareCreateCommit _ _ = _›,
      pathsyncExternalPathsyncPathSecretsRel_lemma _ _ _ ‹externalPathsyncPathSecretsRel externalPath _› ‹_›,
      ‹_›, ‹_›⟩
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

/-- A verified key package has the source `key_package` and a principal (from the event predicate of its verification). -/
theorem IHaveVerifiedKeyPackage.facts (tr: ProofTrace) (me: Participant) (kp: KeyPackage Bytes tkt)
  (h: IHaveVerifiedKeyPackage tr.erase me kp) (hinv: tr.Invariant):
  kp.tbs.leafNode.data.source = .keyPackage ∧ ∃ prin, keyPackageToPrincipal kp = some prin
:= by
  obtain ⟨i, hsrc, -, ⟨token, htoken⟩, -⟩ :=
    ProtocolEvent.EventInv.Has.pred_of_eventLogged keyPackageHasBeenVerifiedPred tr _ hinv h
  refine ⟨hsrc, ?_⟩
  simp only [dyAsp, leafNodeToAsInput] at htoken
  split at htoken
  · exact absurd htoken id
  · exact ⟨_, ‹_›⟩

/-- Port of `joiner_in_tree_is_stale_participants`. -/
theorem JoinerIsInTree.joinerIsStaleParticipant (tr: ProofTrace) (me: Participant) {groupId: MlsBytes Bytes}
  (st: TreeSyncState Bytes tkt DyAsToken groupId) (joiner: KeyPackage Bytes tkt × Nat)
  (hin: JoinerIsInTree st joiner) (hver: IHaveVerifiedKeyPackage tr.erase me joiner.1) (hinv: tr.Invariant):
  JoinerIsStaleParticipant st.tree joiner.1
:=
  ⟨joiner.2, hin.2, (IHaveVerifiedKeyPackage.facts tr me _ hver hinv).1⟩

/-- Port of `joiners_in_tree_are_stale_participants`. -/
theorem JoinersAreInTree.joinersAreStaleParticipants (tr: ProofTrace) (me: Participant) {groupId: MlsBytes Bytes}
  (st: TreeSyncState Bytes tkt DyAsToken groupId) (joiners: List (KeyPackage Bytes tkt × Nat))
  (hin: JoinersAreInTree st joiners) (hver: IHaveVerifiedEveryKeyPackage tr.erase me (joiners.map (·.1)))
  (hinv: tr.Invariant):
  JoinersAreStaleParticipants st.tree (joiners.map (·.1))
:= by
  intro kp hkp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hkp
  exact JoinerIsInTree.joinerIsStaleParticipant tr me st j (hin j hj) (hver _ hkp) hinv

/-- Port of `joiner_is_in_tree_and_path_secret_good_for_joiner_implies_one_opt_path_secret_good`. -/
theorem OneOptPathSecretGood_of_pathSecretGoodForJoiner (tr: ProofTrace) (me: Participant) {groupId: MlsBytes Bytes}
  (st: TreeSyncState Bytes tkt DyAsToken groupId) (joiner: KeyPackage Bytes tkt × Nat) (pathSecret: Bytes)
  (hin: JoinerIsInTree st joiner) (hver: IHaveVerifiedKeyPackage tr.erase me joiner.1)
  (hgood: PathSecretGoodForJoiner tr st.tree groupId joiner.2 pathSecret) (hinv: tr.Invariant):
  OneOptPathSecretGood tr (joiner.1, some pathSecret)
:= by
  obtain ⟨kp, li⟩ := joiner
  obtain ⟨hsrc, prin, hprin⟩ := IHaveVerifiedKeyPackage.facts tr me kp hver hinv
  obtain ⟨-, hknow, husg⟩ := hgood
  intro ps hps
  obtain rfl := Option.mem_some_iff.mp hps
  simp only [hin.2, Option.map_some, Option.getD_some, nodeSkLabelAuxLeaf, reduceCtorEq, ite_false, hsrc] at hknow
  simp only [keyPackageToPrincipal] at hprin
  have hassoc: (initKeyAssociatedWith kp.tbs.leafNode).canFlow (keyPackageToInitLabel kp) tr.erase := by
    apply canFlowTrans _ _ _ _ (Label.bigJoin_canFlow _ kp _)
    intro trL hle hc
    simp only [initKeyAssociatedWithAux, Label.meetIsCorrupt, Label.ofProp_isCorrupt, KeyPackageHasLeafNode,
      keyPackageHasBeenVerifiedLabel_isCorrupt]
    exact ⟨⟨trivial, me, Trace.EventLogged_le _ _ _ hle hver⟩, hc⟩
  refine ⟨prin, hprin, ⟨hknow.1, ?_⟩, ?_, husg⟩ <;> grind [canFlowTrans]

/-- Port of `joiners_are_in_tree_and_path_secrets_good_for_joiners_implies_all_opt_path_secret_good`. -/
theorem AllOptPathSecretGood_of_pathSecretsGoodForJoiners (tr: ProofTrace) (me: Participant) {groupId: MlsBytes Bytes}
  (st: TreeSyncState Bytes tkt DyAsToken groupId) (joiners: List (KeyPackage Bytes tkt × Nat)) (pathSecrets: List Bytes)
  (hin: JoinersAreInTree st joiners) (hver: IHaveVerifiedEveryKeyPackage tr.erase me (joiners.map (·.1)))
  (hgood: PathSecretsGoodForJoiners tr st.tree groupId (joiners.map (·.2)) pathSecrets) (hinv: tr.Invariant):
  AllOptPathSecretGood tr ((joiners.map (·.1)).zip (pathSecrets.map some))
:= by
  induction joiners generalizing pathSecrets with
  | nil => simp [AllOptPathSecretGood]
  | cons j t ih =>
    cases pathSecrets with
    | nil => simp [PathSecretsGoodForJoiners] at hgood
    | cons ps pss =>
      simp only [AllOptPathSecretGood, List.map_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨OneOptPathSecretGood_of_pathSecretGoodForJoiner tr me st j ps (hin j (List.mem_cons_self ..))
        (hver _ (List.mem_cons_self ..)) hgood.1 hinv, ?_⟩
      exact ih pss (fun j hj => hin j (List.mem_cons_of_mem _ hj))
        (fun kp hkp => hver kp (List.mem_cons_of_mem _ hkp)) hgood.2

/--
Port of `_generate_update_path_tree_proof`.
MLS*'s `Some? pending_commit.commit_secret` and the facts on `Some?.v pending_commit.commit_secret` are an `∃`.
The precondition also states the refinement of MLS*'s `pending_create_commit` (`PendingCreateCommit.Valid`).
-/
@[instance]
public
theorem generateUpdatePathTree'.proof (me: Participant) (authServiceSid: Nat) (st: TreeSyncTreeKEMState)
  (updatePathsync: PathSync Bytes tkt st.treekem.treeState.levels) (treekemPendingCreateCommit: API.PendingCreateCommit st.treekem)
  (joiners: List (KeyPackage Bytes tkt × Nat)):
  HoareTriple
    (generateUpdatePathTree' me authServiceSid st updatePathsync treekemPendingCreateCommit joiners)
    (fun tr =>
      JoinersAreInTree st.treesync joiners ∧
      IAmNotAJoiner st.leafIndex (joiners.map (·.2)) ∧
      updatePathsync.getPathLeaf.data.source = .commit ∧
      credentialToPrincipal updatePathsync.getPathLeaf.data.credential = some me ∧
      (PathSync.mf tkt st.treekem.treeState.levels).wf (Bytes.Publishable · tr) updatePathsync ∧
      PendingCommitGood tr me st.treesync st.treekem.treeState treekemPendingCreateCommit.pend ∧
      treekemPendingCreateCommit.Valid ∧
      pathsyncPathSecretsRel updatePathsync treekemPendingCreateCommit.pend.pathSecrets ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun res tr =>
      TreesyncTreekemStateInvariantAux tr me res.provisionalGroupContext res.newTreesync res.pendingCommit.newState.treeState ∧
      res.pendingCommit.newState.keyscheduleState = st.treekem.keyscheduleState ∧
      res.provisionalGroupContext.groupId = st.groupContext.groupId ∧
      res.provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      TreeHasHash res.newTreesync.tree res.provisionalGroupContext.treeHash.val ∧
      PathkemGood res.commitResult.updatePath tr ∧
      (∃ commitSecret, res.pendingCommit.commitSecret = some commitSecret ∧
        commitSecret.Invariant tr ∧
        (nodeSkLabelNosig res.newTreesync.tree res.provisionalGroupContext.groupId st.leafIndex).canFlow
          (commitSecret.label tr) tr.erase) ∧
      PathSecretsGoodForJoiners tr st.treesync.tree st.groupContext.groupId (joiners.map (·.2))
        res.commitResult.addedLeavesPathSecrets ∧
      JoinersAreInTree res.newTreesync joiners
    )
:= by
  obtain ⟨updatePathsync0, rfl⟩: ∃ p, p = updatePathsync := ⟨_, rfl⟩
  unfold generateUpdatePathTree'
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i hl
  step
  step_intro
  step
  step
  step
  have htsPend := TreeSync.API.prepareCommit_valid _ _ _ _ ‹TreeSync.API.prepareCommit _ _ _ = _›
  have hheq: HEq updatePathsync updatePathsync0 := by
    first | exact eqRec_heq _ _ | exact cast_heq _ _ | (subst updatePathsync; grind)
  have hleaf: updatePathsync.getPathLeaf = updatePathsync0.getPathLeaf := Path.getPathLeaf_of_heq _ _ hl hheq
  step by
    obtain ⟨-, -, -, -, hwfP, -, -, -, hinv⟩ := ‹JoinersAreInTree _ _ ∧ _›
    have := hinv.2.2.2.2.1
    rw [GroupContext.mf.wf_eq] at this
    refine ⟨by grind [Bytes.Publishable], ?_, ⟨token, htsPend.2.2 ▸ ‹_›⟩, ?_⟩
    · rw [hleaf]
      exact wf_invariant_of_publishable _ _ _ (MLS.getPathLeaf_wf _ _ _ _ hwfP)
    · have := htsPend.1.1
      simp only [pathIsValid, pathLeafIsValid, Bool.and_eq_true] at this
      exact this.1.1.1
  step by
    obtain ⟨-, -, -, -, hwfP, -, -, -, hinv⟩ := ‹JoinersAreInTree _ _ ∧ _›
    refine ⟨hinv.2.2.2.2.1, ?_⟩
    apply TreeSync.API.finalizeCommit_wf _ _ _ _ ‹_› (preIsHashCompatible_publishable tr) hinv.2.2.2.2.2.1
    exact Path.heq_transport _ _ hl hheq (fun l p => (PathSync.mf tkt l).wf (Bytes.Publishable · tr) p) hwfP
  step_intro
  step with ⟨ encryptPathSecretsEntropyGhostData st.treesync.tree (hl ▸ unAdd st.treekem.treeState.tree addedLeaves)
    st.leafIndex (hl ▸ treekemPendingCreateCommit.pend.pathSecrets) st.groupContext.groupId ⟩ by
    obtain ⟨-, -, -, -, -, -, hv, -⟩ := ‹JoinersAreInTree _ _ ∧ _›
    exact encryptPathSecretsEntropyGhostData_length_cast _ _ _ _ _ _ hl hv
  step
  split
  rename_i pendingCommit commitResult _
  step
  subst x
  obtain ⟨hjoin, hnot, hsrc, hcred, hwfP, hpendGood, hpccValid, hps, hinv⟩ := ‹JoinersAreInTree _ _ ∧ _›
  have hmy := TreesyncTreekemStateInvariant.leafIndex_lt tr me st hinv
  have hpos := TreesyncTreekemStateInvariant.position tr me st hinv
  have hli := (TreesyncTreekemStateInvariant.containsLeafIndex_iff tr me st hinv st.leafIndex).2.2 hmy
  obtain ⟨hvalid, htk, hrel, hme, hgc, hwf, hasp, hverif, hpriv⟩ := hinv
  -- the TreeKEM commit
  have hcc := ‹API.continueCreateCommit _ _ _ _ = .success (pendingCommit, commitResult)›
  simp only [API.continueCreateCommit, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at hcc
  obtain ⟨tcr, hTk, rfl, rfl⟩ := hcc
  have hTs := ‹TreeSync.API.finalizeCommit treesyncPendingCommit token = .success newTreesync›
  have hps' := Path.heq_transport _ _ hl hheq (fun _ p => pathsyncPathSecretsRel p treekemPendingCreateCommit.pend.pathSecrets) hps
  have hleafPk: DySlop.HPKE.hpkePk treekemPendingCreateCommit.pend.pathSecrets.getPathLeaf = updatePathsync.getPathLeaf.data.content.val := by
    obtain ⟨sk, hsk⟩ := getPathLeaf_pathsyncPathSecretsRel _ _ hps
    rw [hleaf]
    exact (hpkeGenKeypair_eq_success _ _ _ hsk).2.symm
  have hgcInv := wf_invariant_of_publishable _ _ _ ‹GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext.val›
  have hgcSt := hgc
  rw [GroupContext.mf.wf_eq] at hgcSt
  obtain ⟨hpath, hpriv', hcsInv, hcsLabel, hjoiners⟩ := MLS.TreeKEM.Symbolic.API.Tree.createCommit_proof tr me st.treesync
    st.treekem.treeState hl treekemPendingCreateCommit.pend addedLeaves provisionalGroupContext.val continueCreateCommitRand
    updatePathsync treesyncPendingCommit token newTreesync tcr hTs hTk (by rw [hleaf]; exact hsrc) (by rw [hleaf]; exact hcred)
    hpendGood hleafPk ⟨hasp, hverif, wf_invariant_of_publishable _ _ _ hwf⟩ hrel hvalid htk hgcInv
    (by grind [Bytes.Publishable]) ‹_› h
  have hleaves := fun li => TreeSync.API.leafAtNat_finalizeCommit treesyncPendingCommit token li newTreesync hTs (by grind)
  have hposNew: newTreesync.tree.position = 0 := by
    obtain ⟨newTree, h1, rfl⟩ := TreeSync.API.finalizeCommit_success treesyncPendingCommit token newTreesync hTs
    simp [TreeSync.API.stateUpdateTree, applyPathAux_position _ _ _ _ _ h1, hpos]
  have hgid := ‹provisionalGroupContext.val.groupId = st.groupContext.groupId›
  -- the invariant of the new state, with the old group context
  have hAux: TreesyncTreekemStateInvariantAux tr me st.groupContext newTreesync tcr.newState := by
    refine ⟨TreeSync.API.finalizeCommit_treeValid _ _ _ hTs htsPend hvalid,
      (API.Tree.finalizeCreateCommit_valid _ _ _ _ _ hTk hpccValid htk).1,
      createCommit_stateRel treesyncPendingCommit token _ _ _ _ _ _ _ hTs hTk rfl hrel hps', ?_, hgc,
      TreeSync.API.finalizeCommit_wf _ _ _ _ hTs (preIsHashCompatible_publishable tr) hwf
        (Path.heq_transport _ _ hl hheq (fun l p => (PathSync.mf tkt l).wf (Bytes.Publishable · tr) p) hwfP),
      TreeSync.API.finalizeCommit_valid _ _ _ hTs htsPend ‹_› hasp,
      IHaveVerifiedEveryLeafNode_finalizeCommit _ _ treesyncPendingCommit token newTreesync hTs (by grind) hverif ‹_›,
      hpriv'⟩
    apply IAmInTreeAt.of_leafAtNat
    refine ⟨updatePathsync.getPathLeaf, by grind, by rw [hleaf]; exact hcred⟩
  refine ⟨TreesyncTreekemStateInvariantAux_changeGroupContext tr me _ _ hgid _ _ hAux ‹_›, rfl, hgid, ‹_›,
    (TreeSyncState.mpr_iff hgid newTreesync (fun _ ts => TreeHasHash ts.tree provisionalGroupContext.val.treeHash.val)).2 ‹_›,
    hpath, ⟨tcr.commitSecret, rfl, hcsInv, ?_⟩, hjoiners, ?_⟩
  · apply (TreeSyncState.mpr_iff hgid newTreesync
      (fun _ ts => (nodeSkLabelNosig ts.tree provisionalGroupContext.val.groupId st.leafIndex).canFlow
        (tcr.commitSecret.label tr) tr.erase)).2
    rw [hgid]
    exact hcsLabel.2
  · apply (TreeSyncState.mpr_iff hgid newTreesync (fun _ ts => JoinersAreInTree ts joiners)).2
    intro j hj
    have hj' := (JoinerIsInTree_iff _ _ hpos).mp (hjoin j hj)
    rw [JoinerIsInTree_iff _ _ hposNew, hleaves]
    have: st.leafIndex ≠ j.2 := fun h => hnot (h ▸ List.mem_map_of_mem hj)
    simp [this, hj']

/--
Port of `_generate_update_path_proof`.
MLS*'s `Some? res.pending_commit.commit_secret` and the facts on its value are an `∃`.
-/
@[instance]
public
theorem generateUpdatePath'.proof (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender):
  HoareTriple
    (generateUpdatePath' me authServiceSid updateCacheSid st proposals)
    (fun tr =>
      (∀ p ∈ proposals.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun res tr =>
      res.optUpdatePath.isSome ∧
      (∃ commitSecret, res.pendingCommit.commitSecret = some commitSecret ∧
        commitSecret.Invariant tr ∧
        (nodeSkLabelNosig res.newTreesync.tree res.provisionalGroupContext.groupId st.leafIndex).canFlow
          (commitSecret.label tr) tr.erase) ∧
      TreesyncTreekemStateInvariantAux tr me res.provisionalGroupContext res.newTreesync res.pendingCommit.newState.treeState ∧
      res.provisionalGroupContext.groupId = st.groupContext.groupId ∧
      res.provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      res.pendingCommit.newState.keyscheduleState = st.treekem.keyscheduleState ∧
      (MlsOption.mf TreeKEM.UpdatePath.mf).wf (Bytes.Publishable · tr) res.optUpdatePath ∧
      res.joinersAndPathSecrets.map (·.1) = proposalsToKeyPackages (proposals.map (·.proposal)) ∧
      JoinersAreStaleParticipants res.newTreesync.tree (res.joinersAndPathSecrets.map (·.1)) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (res.joinersAndPathSecrets.map (·.1)) ∧
      AllOptPathSecretGood tr res.joinersAndPathSecrets ∧
      TreeHasHash res.newTreesync.tree res.provisionalGroupContext.treeHash.val ∧
      PskIdsGood tr res.pskIds
    )
:= by
  unfold generateUpdatePath'
  step_intro
  step
  split
  rename_i st joiners pskIds _ _ _
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i hli
  step
  split
  rename_i updatePathsync treekemPendingCreateCommit _
  dsimp only at *
  step by
    obtain ⟨hinvSt, -, -, -, hjoin, hnot, -⟩ := ‹TreesyncTreekemStateInvariant tr me st ∧ _›
    obtain ⟨hwfP, hgood, hvalid, hps, hsrc, hcred⟩ := ‹(PathSync.mf tkt _).wf _ updatePathsync ∧ _›
    exact ⟨hjoin, hnot, hsrc, hcred, hwfP, hgood, hvalid, hps, hinvSt⟩
  step
  step
  step
  step
  subst x
  obtain ⟨hinvSt, hkps, hver, hks0, hjoin, hnot, hpsk, hgc0, -⟩ := ‹TreesyncTreekemStateInvariant tr me st ∧ _›
  obtain ⟨hwfP, -⟩ := ‹(PathSync.mf tkt _).wf _ updatePathsync ∧ _›
  have hlen := ‹(List.map (fun x => x.fst) joiners).length = _›
  have hgid0: st.groupContext.groupId = st0.groupContext.groupId := by rw [hgc0]
  have hepoch0: st.groupContext.epoch = st0.groupContext.epoch := by rw [hgc0]
  dsimp only
  rw [List.map_fst_zip (by simp [hlen])]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, hkps.symm, ?_, hver, ?_, ‹_›, ‹_›⟩
  · obtain ⟨cs, hcsEq, hcsInv, hcsLab⟩ := ‹∃ cs, _ = some cs ∧ _›
    refine ⟨cs, cast_transport (F := API.PendingCreateCommit2 Bytes) hli _ (fun _ x => x.commitSecret = some cs) hcsEq,
      hcsInv, ?_⟩
    rw [show st0.leafIndex = st.leafIndex from hli.symm] at *
    exact hcsLab
  · exact cast_transport (F := API.PendingCreateCommit2 Bytes) hli _
      (fun _ x => TreesyncTreekemStateInvariantAux tr me _ _ x.newState.treeState) ‹_›
  · grind
  · grind
  · exact cast_transport (F := API.PendingCreateCommit2 Bytes) hli _
      (fun _ x => x.newState.keyscheduleState = st0.treekem.keyscheduleState) (‹_ = st.treekem.keyscheduleState›.trans hks0)
  · rw [MlsOption.mf.wf_eq]
    exact compressUpdatePath_wf _ _ _ (mlsStarPathsToUpdatePath_wf _ _ _ hwfP ‹PathkemGood _ tr›) ‹_›
  · exact JoinersAreInTree.joinersAreStaleParticipants tr me _ joiners ‹JoinersAreInTree _ joiners› hver h
  · exact AllOptPathSecretGood_of_pathSecretsGoodForJoiners tr me st.treesync joiners _ hjoin hver ‹_› h

/-- Port of `_generate_no_update_path_proof`. -/
@[instance]
public
theorem generateNoUpdatePath'.proof (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender):
  HoareTriple
    (generateNoUpdatePath' me authServiceSid updateCacheSid st proposals)
    (fun tr =>
      (∀ p ∈ proposals.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun res tr =>
      res.optUpdatePath = none ∧
      res.pendingCommit.commitSecret = none ∧
      TreesyncTreekemStateInvariantAux tr me res.provisionalGroupContext res.newTreesync res.pendingCommit.newState.treeState ∧
      res.provisionalGroupContext.groupId = st.groupContext.groupId ∧
      res.provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      TreeSync.API.treeAddOnlyRel st.treesync.tree res.newTreesync.tree ∧
      res.pendingCommit.newState.keyscheduleState = st.treekem.keyscheduleState ∧
      res.joinersAndPathSecrets.map (·.1) = proposalsToKeyPackages (proposals.map (·.proposal)) ∧
      JoinersAreStaleParticipants res.newTreesync.tree (res.joinersAndPathSecrets.map (·.1)) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (res.joinersAndPathSecrets.map (·.1)) ∧
      AllOptPathSecretGood tr res.joinersAndPathSecrets ∧
      TreeHasHash res.newTreesync.tree res.provisionalGroupContext.treeHash.val ∧
      PskIdsGood tr res.pskIds
    )
:= by
  unfold generateNoUpdatePath'
  step_intro
  step
  split
  rename_i st joiners pskIds _ canAddOnly _
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i hli
  dsimp only at *
  step
  step
  step by
    obtain ⟨hinvSt, -⟩ := ‹TreesyncTreekemStateInvariant tr me st ∧ _›
    exact ⟨hinvSt.2.2.2.2.1, hinvSt.2.2.2.2.2.1⟩
  step
  subst x
  obtain ⟨hinvSt, hkps, hver, hks0, hjoin, hnot, hpsk, hgc0, hrel⟩ := ‹TreesyncTreekemStateInvariant tr me st ∧ _›
  have hpend := ‹API.prepareCreateAddOnlyCommit st.treekem = _›
  simp only [API.prepareCreateAddOnlyCommit, Result.pure_eq_success] at hpend
  subst hpend
  have hgid0: st.groupContext.groupId = st0.groupContext.groupId := by rw [hgc0]
  have hepoch0: st.groupContext.epoch = st0.groupContext.epoch := by rw [hgc0]
  have hmap: ((joiners.map (·.1)).map mkJoinerWithoutPathSecret).map (·.1) = joiners.map (·.1) := by
    simp [mkJoinerWithoutPathSecret]
  dsimp only
  rw [hmap]
  refine ⟨rfl, cast_transport (F := API.PendingCreateCommit2 Bytes) hli _ (fun _ x => x.commitSecret = none) rfl, ?_, ?_,
    ?_, ?_, ?_, hkps.symm, ?_, hver, ?_, ?_, ‹_›⟩
  · exact cast_transport (F := API.PendingCreateCommit2 Bytes) hli _
      (fun _ x => TreesyncTreekemStateInvariantAux tr me _ _ x.newState.treeState)
      (TreesyncTreekemStateInvariantAux_changeGroupContext tr me _ _ provisionalGroupContext.property st.treesync
        st.treekem.treeState hinvSt ‹_›)
  · grind
  · grind
  · exact (TreeSyncState.mpr_iff provisionalGroupContext.property st.treesync (fun _ ts => TreeSync.API.treeAddOnlyRel st0.treesync.tree ts.tree)).2
      (hrel ‹_›)
  · exact cast_transport (F := API.PendingCreateCommit2 Bytes) hli _
      (fun _ x => x.newState.keyscheduleState = st0.treekem.keyscheduleState) hks0
  · exact (TreeSyncState.mpr_iff provisionalGroupContext.property st.treesync (fun _ ts => JoinersAreStaleParticipants ts.tree (joiners.map (·.1)))).2
      (JoinersAreInTree.joinersAreStaleParticipants tr me _ joiners hjoin hver h)
  · intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    intro ps hps
    simp [mkJoinerWithoutPathSecret] at hps
  · exact (TreeSyncState.mpr_iff provisionalGroupContext.property st.treesync
      (fun _ ts => TreeHasHash ts.tree (Subtype.val ‹{p: GroupContext Bytes // _}›).treeHash.val)).2 ‹_›

/--
Port of `_generate_opt_update_path_proof`.
MLS*'s `full_commit ==> (bytes_invariant … (Some?.v res.pending_commit.commit_secret) /\ …)` is an `∃`.
-/
@[instance]
public
theorem generateOptUpdatePath'.proof (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposals: List ProposalAndSender) (fullCommit: Bool):
  HoareTriple
    (generateOptUpdatePath' me authServiceSid updateCacheSid st proposals fullCommit)
    (fun tr =>
      (∀ p ∈ proposals.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun res tr =>
      res.optUpdatePath.isSome = fullCommit ∧
      res.pendingCommit.commitSecret.isSome = fullCommit ∧
      TreesyncTreekemStateInvariantAux tr me res.provisionalGroupContext res.newTreesync res.pendingCommit.newState.treeState ∧
      res.provisionalGroupContext.groupId = st.groupContext.groupId ∧
      res.provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      (res.optUpdatePath = none → TreeSync.API.treeAddOnlyRel st.treesync.tree res.newTreesync.tree) ∧
      res.pendingCommit.newState.keyscheduleState = st.treekem.keyscheduleState ∧
      (MlsOption.mf TreeKEM.UpdatePath.mf).wf (Bytes.Publishable · tr) res.optUpdatePath ∧
      res.joinersAndPathSecrets.map (·.1) = proposalsToKeyPackages (proposals.map (·.proposal)) ∧
      JoinersAreStaleParticipants res.newTreesync.tree (res.joinersAndPathSecrets.map (·.1)) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (res.joinersAndPathSecrets.map (·.1)) ∧
      AllOptPathSecretGood tr res.joinersAndPathSecrets ∧
      TreeHasHash res.newTreesync.tree res.provisionalGroupContext.treeHash.val ∧
      PskIdsGood tr res.pskIds ∧
      (fullCommit → ∃ commitSecret, res.pendingCommit.commitSecret = some commitSecret ∧
        commitSecret.Invariant tr ∧
        (nodeSkLabelNosig res.newTreesync.tree res.provisionalGroupContext.groupId st.leafIndex).canFlow
          (commitSecret.label tr) tr.erase)
    )
:= by
  unfold generateOptUpdatePath'
  split
  · step
    grind
  · step
    grind [MlsOption.mf.wf_eq]

/-- Port of `key_packages_are_publishable_lemma`. -/
theorem KeyPackagesArePublishable_proposalsToKeyPackages (tr: ProofTrace) (proposals: List (Proposal Bytes))
  (h: ∀ p ∈ proposals, Proposal.mf.wf (Bytes.Publishable · tr) p):
  KeyPackagesArePublishable tr (proposalsToKeyPackages proposals)
:= by
  induction proposals with
  | nil => simp [KeyPackagesArePublishable, proposalsToKeyPackages]
  | cons p t ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (List.mem_cons_self ..)
    cases p with
    | add a =>
      simp only [Proposal.mf.wf_eq, Add.mf.wf_eq] at hp
      intro kp hkp
      simp only [proposalsToKeyPackages, List.mem_cons] at hkp
      rcases hkp with rfl | hkp
      · exact hp
      · exact ih kp hkp
    | _ => simpa only [proposalsToKeyPackages] using ih

/-- The confirmed transcript hash input built by `_create_commit` is well-formed. -/
theorem createCommit'_txHashInput_wf (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (txHashInputSkeleton: ConfirmedTranscriptHashInput Bytes) (commitSkeleton: Commit Bytes)
  (groupId: MlsBytes Bytes) (epoch: UInt64) (sender: Sender) (optUpdatePath: Option (UpdatePath Bytes))
  (hcontent: txHashInputSkeleton.content.content = { contentType := .commit, content := commitSkeleton })
  (hskel: ConfirmedTranscriptHashInput.mf.wf pred txHashInputSkeleton) (hgid: pred groupId.val)
  (hpath: (MlsOption.mf UpdatePath.mf).wf pred optUpdatePath):
  ConfirmedTranscriptHashInput.mf.wf pred { txHashInputSkeleton with
    content := { txHashInputSkeleton.content with
      groupId, epoch, sender
      content := { contentType := .commit, content := { commitSkeleton with path := optUpdatePath } } } }
:= by
  have hcommit := commit_wf_of_txHashInput pred _ _ hcontent hskel
  simp only [ConfirmedTranscriptHashInput.mf.wf_eq, FramedContent.mf.wf_eq, MlsTaggedContent.mf.wf_eq,
    Commit.mf.wf_eq] at hskel hcommit ⊢
  refine ⟨⟨hgid, hskel.1.2.1, ?_⟩, hskel.2⟩
  exact (MlsUntaggedContent.mf.wf_commit _ _).mpr
    ((Commit.mf.wf_eq _ { commitSkeleton with path := optUpdatePath }).mpr ⟨hcommit.1, hpath⟩)

/--
The new state of `_create_commit`, after `finalize_create_commit`: its invariants and its key schedule
(the second and third `pf` of MLS*'s `_create_commit_proof`).
-/
theorem createCommit'_finalize (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  (provisionalGroupContext: GroupContext Bytes)
  (newTreesync: TreeSyncState Bytes tkt DyAsToken provisionalGroupContext.groupId)
  (pendingCommit: API.PendingCreateCommit2 Bytes st.leafIndex) (isFullCommit: Bool)
  (joiners: List (KeyPackage Bytes tkt)) (psks: List (PreSharedKeyId Bytes × Bytes))
  (confirmedTranscriptHash: MlsBytes Bytes) (commitResult: API.CreateCommitResult Bytes st.leafIndex)
  (hfin: API.finalizeCreateCommit pendingCommit { provisionalGroupContext with confirmedTranscriptHash } psks =
    .success commitResult)
  (hAux: TreesyncTreekemStateInvariantAux tr me provisionalGroupContext newTreesync pendingCommit.newState.treeState)
  (hth: TreeHasHash newTreesync.tree provisionalGroupContext.treeHash.val)
  (hks: pendingCommit.newState.keyscheduleState = st.treekem.keyscheduleState)
  (hinit: st.treekem.keyscheduleState.initSecret.Invariant tr)
  (hcs: pendingCommit.commitSecret.isSome = isFullCommit)
  (hcsGood: isFullCommit = true → ∃ commitSecret, pendingCommit.commitSecret = some commitSecret ∧
    commitSecret.Invariant tr ∧
    (nodeSkLabelNosig newTreesync.tree provisionalGroupContext.groupId st.leafIndex).canFlow (commitSecret.label tr) tr.erase)
  (hcth: confirmedTranscriptHash.val.Publishable tr)
  (hjoiners: TxHashContainsJoiners confirmedTranscriptHash.val joiners)
  (hpsks: PsksBytesInvariant tr psks):
  let newGroupContext: GroupContext Bytes := { provisionalGroupContext with confirmedTranscriptHash }
  let newSt: TreeSyncTreeKEMState :=
    { st with groupContext := newGroupContext, treesync := newTreesync, treekem := commitResult.newState }
  TreesyncTreekemStateInvariant tr me newSt ∧
  TreesyncTreekemStateCoarseInvariant tr me newSt ∧
  TreekemKeyscheduleStateLabelGood tr st.treekem.keyscheduleState.initSecret
    (computeExpectedCommitSecretLabel isFullCommit newTreesync.tree provisionalGroupContext.groupId)
    joiners psks newSt.treekem.keyscheduleState newGroupContext ∧
  TreekemKeyscheduleStateAuthStrong newSt.treekem.keyscheduleState commitResult.joinerSecret psks newGroupContext ∧
  commitResult.joinerSecret.KnowableBy ((joiners.map keyPackageToInitLabel).foldr Label.join Label.secret) tr
:= by
  intro newGroupContext newSt
  have hgc: GroupContext.mf.wf (Bytes.Publishable · tr) newGroupContext := by
    have := hAux.2.2.2.2.1
    rw [GroupContext.mf.wf_eq] at this ⊢
    exact ⟨this.1, this.2.1, hcth, this.2.2.2⟩
  simp only [API.finalizeCreateCommit, Result.bind_eq_success, Result.pure_eq_success] at hfin
  obtain ⟨⟨ks, encSecret, welcomeSecrets⟩, hksEq, rfl⟩ := hfin
  have hcsInv: ∀ cs ∈ pendingCommit.commitSecret, cs.Invariant tr := by
    intro cs hcs'
    rw [Option.mem_def] at hcs'
    grind
  obtain ⟨hksGood, hksLabel, hksAuth, hksAuthEx, hjoinerSecret⟩ := commit_proof tr
    pendingCommit.newState.keyscheduleState pendingCommit.commitSecret psks newGroupContext joiners
    ks encSecret welcomeSecrets hksEq hjoiners (by rw [hks]; exact hinit) hcsInv hpsks hgc
  rw [hks] at hksLabel
  refine ⟨TreesyncTreekemStateInvariantAux_changeGroupContext tr me provisionalGroupContext newGroupContext rfl
    newTreesync _ hAux hgc, ⟨hksGood, hksAuthEx.weak, hth⟩, ?_, hksAuth, hjoinerSecret⟩
  apply TreekemKeyscheduleStateLabelGood_canFlow _ _ _ _ _ _ _ _ hksLabel
  unfold computeExpectedCommitSecretLabel computeCommitSecretLabel
  have := nodeSkLabel_canFlow_nodeSkLabelNosig newTreesync.tree provisionalGroupContext.groupId st.leafIndex tr.erase
  split
  · obtain ⟨cs, hcs', -, hflow⟩ := hcsGood (by assumption)
    grind [Label.canFlow]
  · grind [Label.canFlow]

/-- Port of `_create_commit_proof`. -/
@[instance]
public
theorem createCommit'.proof (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st: TreeSyncTreeKEMState) (txHashInputSkeleton: ConfirmedTranscriptHashInput Bytes):
  HoareTriple
    (createCommit' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st txHashInputSkeleton)
    (fun tr =>
      ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInputSkeleton ∧
      TreesyncTreekemStateAllInvariants tr me st
    )
    (fun (res, _pskStoreSid) tr =>
      TreesyncTreekemStateAllInvariants tr me res.newSt ∧
      GroupInfoSignPredAux tr.erase me res.newSt.groupContext res.newSt.treekem.keyscheduleState.epochKeys.confirmationTag ∧
      ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) res.txHashInput ∧
      KeyPackagesArePublishable tr (res.joinersAndPathSecrets.map (·.1)) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (res.joinersAndPathSecrets.map (·.1)) ∧
      AllOptPathSecretGood tr res.joinersAndPathSecrets ∧
      res.joinerSecret.KnowableBy
        (((res.joinersAndPathSecrets.map (·.1)).map keyPackageToInitLabel).foldr Label.join Label.secret) tr ∧
      PsksBytesInvariant tr res.psks
    )
:= by
  unfold createCommit'
  step_intro
  step_intro
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i commitSkeleton hcontent
  step_intro
  step by
    exact ((Commit.mf.wf_eq _ _).mp (commit_wf_of_txHashInput _ _ _ hcontent ‹_ ∧ _›.1)).1
  replace hprop: ProposalsArePublishable tr (proposals.map (·.proposal)) := ‹∀ p ∈ proposals.map (·.proposal), _›
  step by
    exact ⟨hprop, ‹_ ∧ TreesyncTreekemStateAllInvariants tr me st›.2.1⟩
  split
  rename_i provisionalGroupContext optUpdatePath newTreesync pendingCommit joinersAndPathSecrets pskIds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  step
  step_intro
  step
  step_intro
  step_intro
  step
  step_intro
  step
  step_intro
  -- the confirmed transcript hash and the key schedule
  obtain ⟨hskel, hall0⟩ := ‹_ ∧ TreesyncTreekemStateAllInvariants tr me _›
  have hprovInv := ‹TreesyncTreekemStateInvariantAux tr me provisionalGroupContext newTreesync pendingCommit.newState.treeState›
  have hwf: ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInput :=
    createCommit'_txHashInput_wf _ _ commitSkeleton _ _ _ optUpdatePath hcontent hskel
    (by have := hall0.1.2.2.2.2.1; rw [GroupContext.mf.wf_eq] at this; exact this.1) ‹_›
  obtain ⟨hjoiners, hcthPub⟩ := computeConfirmedTranscriptHash'_txHashContainsJoiners tr me _ txHashInput commit
    confirmedTranscriptHash _ ‹_› rfl ‹_› hwf hall0
  have hjs: joinersAndPathSecrets.map (·.1) = proposalsToKeyPackages (proposals.map (·.proposal)) := ‹_›
  rw [← hjs] at hjoiners
  have hpath := ‹optUpdatePath.isSome = commitSkeleton.path.isSome›
  have hinit0 := hall0.2.1.1.2.2.2.2.2.2.1.1
  have hfinal := createCommit'_finalize tr me st0 provisionalGroupContext newTreesync pendingCommit
    optUpdatePath.isSome _ psks confirmedTranscriptHash _ ‹_› hprovInv ‹_› ‹_› hinit0 (by rw [hpath]; assumption)
    (by rw [hpath]; assumption) hcthPub hjoiners ‹_›
  -- `step` monotonizes `hlabel` with the facts before it
  have hgoodNew := hfinal.2.1.1
  obtain ⟨hinvNew, hcoarseNew, hlabel, hksAuth, hjoinerSecret⟩ := hfinal
  step by
    exact rememberPsk_resumptionPsk_pre tr me newGroupContext newTreesync.tree st0.leafIndex _ hinvNew.2.2.2.2.1
      hcoarseNew.2.2 hprovInv.2.2.2.1 hcoarseNew.1.2.2.2.2.1.1 hlabel.2.2.2.2.2.2.2
  step by
    rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := iAmInGroupPred)]
    have hlabel := ‹TreekemKeyscheduleStateLabelGood tr _ (computeExpectedCommitSecretLabel _ _ _) _ _ _ _›
    refine ⟨‹TreeHasHash newTreesync.tree _›, ‹TreesyncTreekemStateInvariant tr me st›.2.2.2.2.2.2.2.1,
      ‹st0.treekem.keyscheduleState.initSecret.Invariant tr›, (‹provisionalGroupContext.groupId = _›).symm,
      (‹provisionalGroupContext.epoch = _›).symm, ?_, ‹PsksBytesInvariant tr psks›, ‹IHaveVerifiedEveryKeyPackage _ _ _›,
      ‹TreesyncTreekemStateAllInvariants tr me st0›.2.2, ‹TreesyncTreekemStateCoarseInvariant tr me st›.1, ?_⟩
    · intro hty
      apply ‹optUpdatePath = none → _›
      revert hty
      cases optUpdatePath <;> simp
    · revert hlabel
      cases optUpdatePath.isSome <;> exact id
  step
  subst x
  have hlogged := ‹Trace.EventLogged (_: IAmInGroup) tr.erase›
  have hkp: KeyPackagesArePublishable tr (joinersAndPathSecrets.map (·.1)) := by
    rw [‹joinersAndPathSecrets.map (·.1) = _›]
    exact KeyPackagesArePublishable_proposalsToKeyPackages tr _ ‹ProposalsArePublishable tr _›
  refine ⟨⟨‹TreesyncTreekemStateInvariant tr me st›, ‹TreesyncTreekemStateCoarseInvariant tr me st›, ?_⟩, ?_,
    ‹ConfirmedTranscriptHashInput.mf.wf _ txHashInput›, hkp, ‹IHaveVerifiedEveryKeyPackage _ _ _›,
    ‹AllOptPathSecretGood _ _›, ‹commitResult.joinerSecret.KnowableBy _ tr›, ‹PsksBytesInvariant tr psks›⟩
  · exact ⟨_, rfl, hlogged, rfl, rfl, rfl⟩
  · exact ⟨_, commitResult.joinerSecret, ⟨rfl, rfl, ‹TreekemKeyscheduleStateAuthStrong _ _ _ _›,
      ‹TreeHasHash newTreesync.tree _›, ‹JoinersAreStaleParticipants _ _›⟩, rfl, hlogged⟩

/-- Port of `_create_commit_and_welcome_proof`. -/
@[instance]
public
theorem createCommitAndWelcome'.proof (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st: TreeSyncTreeKEMState) (txHashInputSkeleton: ConfirmedTranscriptHashInput Bytes):
  HoareTriple (createCommitAndWelcome' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st txHashInputSkeleton)
    (fun tr => ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInputSkeleton ∧ TreesyncTreekemStateAllInvariants tr me st)
    (fun (txHashInput, welcome, groupInfo, st, _pskStoreSid) tr =>
      ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInput ∧
      (∀ w ∈ welcome, Welcome.mf.wf (Bytes.Publishable · tr) w) ∧
      GroupInfo.mf.wf (Bytes.Publishable · tr) groupInfo ∧
      TreesyncTreekemStateAllInvariants tr me st)
:= by
  unfold createCommitAndWelcome'
  step
  split
  rename_i newSt joinersAndPathSecrets joinerSecret txHashInput psks pskStoreSid _
  obtain ⟨hinv, hgi, htx, hkps, hver, hps, hjs, hpsks⟩ := ‹TreesyncTreekemStateAllInvariants tr me newSt ∧ _›
  step_intro
  step by
    exact ⟨by simp [groupInfoInputs, emptyExtensions], hgi, hinv⟩
  step_intro
  step with ⟨ me ⟩ by
    have hjs := ‹joinerSecret.KnowableBy _ tr›
    exact ⟨hjs.1, ‹_›, ‹_›, ‹_›, ‹_›, hjs, ‹_›⟩
  step
  subst x
  exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

/-- Port of `create_commit_and_welcome_proof`. -/
@[instance]
public
theorem createCommitAndWelcome.proof (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (groupStateSid: Nat) (messageSkeletonTs: Nat):
  HoareTriple
    (createCommitAndWelcome me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid messageSkeletonTs)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold createCommitAndWelcome
  step
  step
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  step
  step by
    exact ⟨wf_of_parse _ _ _ _ ‹_› ‹_›, ‹_›⟩
  split
  rename_i message optWelcome groupInfo st' pskStoreSid' _
  obtain ⟨hmsg, hwel, hgi, hinv⟩ := ‹ConfirmedTranscriptHashInput.mf.wf _ message ∧ _›
  have hrt := hinv.1.2.2.2.2.2.1
  step
  step by
    exact (pred_serializeNE_iff _ _ _).2 ‹ConfirmedTranscriptHashInput.mf.wf _ message›
  dsimp only
  split
  -- `none`
  step
  -- `some welcome`
  rotate_left
  step by
    exact (pred_serializeNE_iff _ _ _).2 (‹∀ w ∈ (some _: Option (Welcome Bytes)), _› _ rfl)
  step
  all_goals
    step by
      exact (pred_serializeNE_iff _ _ _).2 ‹GroupInfo.mf.wf _ groupInfo›
    step
    step by
      exact (pred_serializeNE_iff _ _ _).2 (treesyncToRatchetTree_wf _ _ _ ‹_› ‹_›)
    step
    trivial

end MLS.TreeKEM
