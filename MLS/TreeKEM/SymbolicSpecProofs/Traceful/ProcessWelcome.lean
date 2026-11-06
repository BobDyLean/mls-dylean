module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessWelcome
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProcessCommit
public import MLS.Bootstrap.SymbolicProofs.Welcome
public import MLS.Bootstrap.SymbolicProofs.GroupInfo
public import MLS.Bootstrap.SymbolicProofs.State.KeyPackageStore
import all MLS.TreeKEM.SymbolicSpec.Traceful.ProcessWelcome
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.Bootstrap.SymbolicSpec.State.KeyPackageStore
import all MLS.TreeSync.Code.API
import all MLS.TreeKEM.Code.API
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessWelcome.Proof`.

Port-specific differences:
- The proofs are DyLean Hoare triples (instances), assuming the invariants of
  `MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants` (MLS*'s `has_treesync_and_treekem_invariants`).
- MLS*'s `my_leaf_index_t` is not ported (see `MLS.TreeKEM.SymbolicSpec.Traceful.ProcessWelcome`):
  `findMyIndex'_spec` gives the properties of the leaf index found by `findMyIndex'`.
- The postconditions also state the refinements of MLS*'s types that the state invariant needs
  (e.g. `TreeSyncState.TreeValid`, the position of the trees).
- `processWelcome'` stores the resumption PSK (see `MLS.TreeKEM.SymbolicSpec.Traceful.ProcessWelcome`):
  its label comes from `createFromJoinerSecret_proof`.
-/

-- The proofs assume the bundles of MLS*'s `has_treesync_and_treekem_invariants` as section variables;
-- each proof only uses some of them.
set_option linter.unusedSectionVars false

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap MLS.TreeKEM.Symbolic.API.KeySchedule

/-! ## Lemmas -/

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

theorem findMyIndex'_zero (t: TreeSync Bytes tkt 0) (ln: LeafNode Bytes tkt):
  findMyIndex' t ln =
    match t.leafContent with
    | none => none
    | some ln' => if serializeNE (LeafNode.mf tkt) ln = serializeNE (LeafNode.mf tkt) ln' then some t.position else none
:= by
  obtain ⟨p, ⟨c⟩⟩ := t
  cases c <;> rw [findMyIndex'.eq_def] <;> rfl

theorem findMyIndex'_succ {l: Nat} (t: TreeSync Bytes tkt (l+1)) (ln: LeafNode Bytes tkt):
  findMyIndex' t ln = (findMyIndex' t.left ln).or (findMyIndex' t.right ln)
:= by
  obtain ⟨p, bt⟩ := t
  cases bt with | node c L R =>
  let t: TreeSync Bytes tkt (l+1) := ⟨p, .node c L R⟩
  rw [findMyIndex'.eq_def]
  show (match findMyIndex' t.left ln with
    | some i => some i
    | none =>
      match findMyIndex' t.right ln with
      | some i => some i
      | none => none) = _
  cases findMyIndex' t.left ln <;> cases findMyIndex' t.right ln <;> rfl

/-- The leaf index found by `findMyIndex'` is in the tree, and its leaf is the given leaf node. -/
theorem findMyIndex'_spec {l: Nat} (t: TreeSync Bytes tkt l) (ln: LeafNode Bytes tkt) (li: Nat)
  (h: findMyIndex' t ln = some li):
  t.containsLeafIndex li ∧ leafAt t li = some ln
:= by
  induction t using Tree.leftRightInduction generalizing li with
  | leaf t =>
    rw [findMyIndex'_zero] at h
    unfold leafAt
    split at h
    · simp at h
    · split at h <;> grind [Tree.containsLeafIndex]
  | @node l t ihLeft ihRight =>
    rw [findMyIndex'_succ] at h
    cases hl: findMyIndex' t.left ln <;> simp only [hl] at h
    · grind [leafAt.eq_def, Tree.containsLeafIndex]
    · grind [leafAt.eq_def, Tree.containsLeafIndex]

/--
The path secret of the group secrets (if any) is good for the leaf public key `myLeafPk`
(MLS*'s `match group_secrets.path_secret with …` in the precondition of `_process_welcome_treekem_proof`).
-/
public
def GroupSecretsPathSecretGood (tr: ProofTrace) (me: Participant) (myLeafPk: Bytes) (groupSecrets: GroupSecrets Bytes): Prop :=
  ∀ pathSecret ∈ groupSecrets.pathSecret, DecodedPathSecretGood me myLeafPk pathSecret.pathSecret.val tr

public
theorem GroupSecretsPathSecretGood_later (tr1 tr2: ProofTrace) (me: Participant) (myLeafPk: Bytes)
  (groupSecrets: GroupSecrets Bytes):
  tr1 ≤ tr2 →
  GroupSecretsPathSecretGood tr1 me myLeafPk groupSecrets →
  GroupSecretsPathSecretGood tr2 me myLeafPk groupSecrets
:= by
  intro hle h ps hps
  have := h ps hps
  grind

grind_pattern GroupSecretsPathSecretGood_later => tr1 ≤ tr2, GroupSecretsPathSecretGood tr1 me myLeafPk groupSecrets
grind_pattern [grind_later] GroupSecretsPathSecretGood_later =>
  tr1 ≤ tr2,
  GroupSecretsPathSecretGood tr1 me myLeafPk groupSecrets

section Proofs

variable [TraceInvariant] [HasTreesyncInvariants tkt] [HasTreeKEMProofTrace]
variable [HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant]
variable [HasBootstrapCryptoInvariants] [HasMlsTreekemInvariants] [HasMlsPskInvariants]
variable [SignWithLabelPred.Has groupInfoSignPred]

/-! ## Process welcome, proofs -/

/--
Port of `_process_welcome_treesync_proof`.
The postcondition also states the refinements of the TreeSync state (`TreeValid`, its tree is at position `0`).
-/
@[instance]
public
theorem processWelcomeTreesync'.proof (me: Participant) (authServiceSid: Nat)
  (ratchetTree: RatchetTree Bytes tkt) (groupId: MlsBytes Bytes):
  HoareTriple
    (processWelcomeTreesync' me authServiceSid ratchetTree groupId)
    (fun tr =>
      groupId.val.Publishable tr ∧
      (RatchetTree.mf tkt).wf (Bytes.Publishable · tr) ratchetTree
    )
    (fun treesyncSt tr =>
      treesyncSt.TreeValid ∧
      treesyncSt.tree.position = 0 ∧
      treesyncStateValid (dyAsp tr) treesyncSt ∧
      (TreeSync.mf tkt treesyncSt.levels).wf (Bytes.Publishable · tr) treesyncSt.tree ∧
      IHaveVerifiedEveryLeafNode tr.erase me treesyncSt.tree groupId
    )
:= by
  unfold processWelcomeTreesync'
  step
  split
  rename_i _ l treesync hres
  step
  step
  have hpend := TreeSync.API.prepareWelcome_valid _ _ ‹TreeSync.API.prepareWelcome _ _ = _›
  have hwfT := ratchetTreeToTreesync_wf (Bytes.Publishable · tr) ratchetTree ⟨l, treesync⟩
    ‹_ ∧ (RatchetTree.mf tkt).wf _ ratchetTree›.2 hres
  have hlen: tokens.length = 2^l := by rw [‹tokens.length = _›, hpend.2.1]
  have hvalid := TreeSync.API.finalizeWelcome_valid _ tokens hpend hlen ‹TreeSync.API.TokensForAsInputs _ _ tokens›
  have hpos: treesync.position = 0 := ratchetTreeToTreesync_position ratchetTree ⟨l, treesync⟩ hres
  step by
    exact ⟨by grind [Bytes.Publishable], wf_invariant_of_publishable _ _ _ hwfT, ⟨_, hvalid.1, hvalid.2⟩, hpend.1.2.2⟩
  step
  subst x
  exact ⟨TreeSync.API.finalizeWelcome_treeValid _ _ hpend, ‹treesync.position = 0›, ‹_›,
    ‹(Tree.mf _ _ _).wf _ treesync›, ‹IHaveVerifiedEveryLeafNode _ _ _ _›⟩

/-- Port of `_process_welcome_verify_group_info_proof`. The `tr_out == tr` part of the postcondition is not ported. -/
@[instance]
public
theorem processWelcomeVerifyGroupInfo'.proof {groupId: MlsBytes Bytes} (me: Participant)
  (treesyncSt: TreeSyncState Bytes tkt DyAsToken groupId) (groupInfo: GroupInfo Bytes):
  HoareTriple
    (processWelcomeVerifyGroupInfo' me treesyncSt groupInfo)
    (fun _ => True)
    (fun _ _ =>
      ∃ inviterVerificationKey, getSignerVerificationKey treesyncSt.tree groupInfo = .success inviterVerificationKey ∧
        verifyWelcomeGroupInfo inviterVerificationKey groupInfo = true ∧
        TreeHasHash treesyncSt.tree groupInfo.tbs.groupContext.treeHash.val
    )
:= by
  unfold processWelcomeVerifyGroupInfo'
  step
  step
  step
  step
  refine ⟨_, ‹_›, ‹_›, ?_⟩
  have heq: computedTreeHash = groupInfo.tbs.groupContext.treeHash.val := ‹_›
  rw [← heq]
  exact ‹API.computeTreeHash treesyncSt = _›

/--
Port of `_process_welcome_treekem_proof`.
The precondition also states the refinements of the TreeSync state (`TreeValid`, its tree is at position `0`).
MLS*'s `treesync_st.levels == treekem_st.tree_state.levels` and `treesync_to_treekem treesync_st.tree == treekem_st.tree_state.tree`
are `treesyncTreekemStateRel`; the postcondition also states the refinements of the TreeKEM state (`Valid`) and,
to store the resumption PSK, its knowability.
-/
@[instance]
public
theorem processWelcomeTreekem'.proof {groupId: MlsBytes Bytes} (me: Participant)
  (treesyncSt: TreeSyncState Bytes tkt DyAsToken groupId) (kpStoreValue: KeyPackageStoreValuePost)
  (groupSecrets: GroupSecrets Bytes) (groupInfo: GroupInfo Bytes) (psks: List (PreSharedKeyId Bytes × Bytes)):
  HoareTriple
    (processWelcomeTreekem' me treesyncSt kpStoreValue groupSecrets groupInfo psks)
    (fun tr =>
      credentialToPrincipal kpStoreValue.keyPackage.tbs.leafNode.data.credential = some me ∧
      GroupSecrets.mf.wf (Bytes.Invariant · tr) groupSecrets ∧
      GroupInfo.mf.wf (Bytes.Invariant · tr) groupInfo ∧
      GroupContext.mf.wf (Bytes.Publishable · tr) groupInfo.tbs.groupContext ∧
      PsksBytesInvariant tr psks ∧
      GroupSecretsPathSecretGood tr me kpStoreValue.keyPackage.tbs.leafNode.data.content.val groupSecrets ∧
      TreeHasHash treesyncSt.tree groupInfo.tbs.groupContext.treeHash.val ∧
      treesyncSt.TreeValid ∧
      treesyncSt.tree.position = 0
    )
    (fun ⟨myLeafIndex, treekemSt⟩ tr =>
      treekemSt.keyscheduleState.epochKeys.confirmationTag = groupInfo.tbs.confirmationTag.val ∧
      TreekemKeyscheduleStateGood tr treekemSt.keyscheduleState groupInfo.tbs.groupContext ∧
      TreekemKeyscheduleStateAuthStrong treekemSt.keyscheduleState groupSecrets.joinerSecret.val psks
        groupInfo.tbs.groupContext ∧
      treekemSt.keyscheduleState.epochKeys.resumptionPsk.KnowableBy
        (mkEpochSecretLabel .resumptionPsk groupInfo.tbs.groupContext) tr ∧
      TreekemPrivStatePred tr me treekemSt.treeState.priv ∧
      treesyncTreekemStateRel treesyncSt treekemSt.treeState ∧
      treekemSt.treeState.Valid ∧
      IAmInTreeAt me treesyncSt.tree myLeafIndex
    )
:= by
  unfold processWelcomeTreekem'
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i myLeafIndex hfind
  step_intro
  step_intro
  step
  step
  step
  split
  rename_i treekemSt encryptionSecret hres
  step
  step
  subst x
  obtain ⟨hcred, hgs, -, hgc, hpsks, hps, -, hvalid, hpos⟩ := ‹credentialToPrincipal _ = some me ∧ _›
  obtain ⟨hli, hleaf⟩ := findMyIndex'_spec _ _ _ hfind
  simp only [API.welcome, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at hres
  obtain ⟨treeState, hTree, ⟨ks, encryptionSecret'⟩, hks, rfl, -⟩ := hres
  rw [GroupSecrets.mf.wf_eq] at hgs
  obtain ⟨hgood, hauth, hflow⟩ := createFromJoinerSecret_proof tr _ psks _ ks encryptionSecret' hks hgs.1 hpsks hgc
  -- the TreeKEM tree
  have hliTk: treekem.containsLeafIndex myLeafIndex := by
    grind [Tree.containsLeafIndex, treesyncToTreekem_position]
  have hleafTk: (leafAt treekem myLeafIndex).isSome := by
    simp [treekem, leafAt_treesyncToTreekem, hleaf]
  have hinvTk := treesyncToTreekem_invariant _ hvalid.1
  have hpsTk: ∀ x ∈ optPathSecretAndInviterInd,
      DecodedPathSecretGood me (DySlop.HPKE.hpkePk leafDecryptionKey) x.1 tr := by
    intro x hx
    rw [‹DySlop.HPKE.hpkePk leafDecryptionKey = _›]
    simp only [optPathSecretAndInviterInd] at hx
    split at hx
    · simp at hx
    · rename_i pathSecret hgsps
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hps _ (by simp [hgsps])
  obtain ⟨hpriv, -⟩ := MLS.TreeKEM.Symbolic.API.Tree.welcome_proof tr me treekem leafDecryptionKey
    optPathSecretAndInviterInd myLeafIndex treeState hTree ‹_› hpsTk hliTk hleafTk hinvTk
  have htkValid := API.Tree.welcome_valid treekem _ _ myLeafIndex treeState hTree
    (by rw [treesyncToTreekem_position]; exact hpos) hinvTk hliTk hleafTk
  obtain ⟨priv, rfl⟩ := API.Tree.welcome_success _ _ _ _ _ hTree
  exact ⟨‹(API.getEpochKeys _).confirmationTag = _›, hgood, hauth, ⟨hgood.2.2.2.2.1.1, hflow⟩, hpriv, rfl,
    htkValid, ⟨_, hleaf, hcred⟩⟩

/--
Port of `_process_welcome_proof`.
MLS*'s postcondition is only the trace invariant; unlike MLS*, the function also stores the resumption PSK.
-/
@[instance]
public
theorem processWelcome'.proof (me: Participant) (keyPackageStoreSid authServiceSid pskStoreSid: Nat)
  (welcome: Welcome Bytes) (ratchetTree: RatchetTree Bytes tkt):
  HoareTriple
    (processWelcome' me keyPackageStoreSid authServiceSid pskStoreSid welcome ratchetTree)
    (fun tr =>
      Welcome.mf.wf (Bytes.Invariant · tr) welcome ∧
      (RatchetTree.mf tkt).wf (Bytes.Publishable · tr) ratchetTree
    )
    (fun _ _ => True)
:= by
  unfold processWelcome'
  step
  step
  split
  rename_i groupSecrets keyPackageRef keyPackageStoreValue hdec
  obtain ⟨hwelcome, hrt⟩ := ‹Welcome.mf.wf _ welcome ∧ _›
  obtain ⟨hgs, hpskIds, -, hps, hcred⟩ := decryptGroupSecrets_proof tr me welcome _ _ _ groupSecrets keyPackageRef
    keyPackageStoreValue hdec hwelcome ‹_›
  have hegi := hwelcome
  rw [Welcome.mf.wf_eq] at hegi
  replace hegi := hegi.2
  have hjs := hgs
  rw [GroupSecrets.mf.wf_eq] at hjs
  replace hjs := hjs.1
  step
  step
  obtain ⟨hgi, hgc⟩ := decryptGroupInfo_proof tr _ psks _ groupInfo ‹_› ‹welcome.encryptedGroupInfo.val.Invariant tr›
    ‹groupSecrets.joinerSecret.val.Invariant tr› ‹PsksBytesInvariant tr psks›
  step by
    have := hgc
    rw [GroupContext.mf.wf_eq] at this
    exact ⟨this.1, ‹(RatchetTree.mf tkt).wf _ ratchetTree›⟩
  step
  obtain ⟨vk, hvk, hverif, hth⟩ := ‹∃ vk, getSignerVerificationKey treesyncSt.tree groupInfo = _ ∧ _›
  step by
    exact ⟨‹credentialToPrincipal _ = some me›, ‹GroupSecrets.mf.wf _ groupSecrets›, ‹GroupInfo.mf.wf _ groupInfo›,
      ‹GroupContext.mf.wf _ groupInfo.tbs.groupContext›, ‹PsksBytesInvariant tr psks›, ‹GroupSecretsPathSecretGood _ _ _ _›,
      hth, ‹treesyncSt.TreeValid›, ‹treesyncSt.tree.position = 0›⟩
  split
  rename_i _ myLeafIndex treekemSt hpost
  obtain ⟨htag, hgood, hauth, hpsk, hpriv, hrel, htkValid, hme⟩ := hpost
  have hvalid := ‹treesyncStateValid (dyAsp tr) treesyncSt›
  step by
    rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := iAmInGroupPred)]
    obtain ⟨hsigner, inviterLeafNode, inviterId, hleaf, hcredInv, rfl, hsig⟩ :=
      getSignerVerificationKey_proof tr treesyncSt.tree groupInfo treesyncSt.tokens vk hvk hvalid.1 hvalid.2
    have := verifyWelcomeGroupInfo_proof tr inviterId _ groupInfo _ psks treekemSt.keyscheduleState hverif
      ‹GroupInfo.mf.wf _ groupInfo› hsig hauth htag.symm
    have hinviter: treesyncSt.tree.containsLeafIndex groupInfo.tbs.signer.toNat := by
      simp [Tree.containsLeafIndex, ‹treesyncSt.tree.position = 0›, hsigner]
    exact ⟨hth, ‹IHaveVerifiedEveryLeafNode _ _ _ _›, hinviter, inviterLeafNode, inviterId, hleaf, hcredInv, this⟩
  step by
    have hpsk := ‹treekemSt.keyscheduleState.epochKeys.resumptionPsk.KnowableBy _ tr›
    exact rememberPsk_resumptionPsk_pre tr me _ treesyncSt.tree myLeafIndex _ ‹GroupContext.mf.wf _ groupInfo.tbs.groupContext›
      ‹TreeHasHash treesyncSt.tree _› ‹IAmInTreeAt me treesyncSt.tree myLeafIndex› hpsk.1 hpsk.2
  step by
    refine ⟨⟨‹treesyncSt.TreeValid›, ‹treekemSt.treeState.Valid›, ‹treesyncTreekemStateRel _ _›,
      ‹IAmInTreeAt me treesyncSt.tree myLeafIndex›, ‹GroupContext.mf.wf _ groupInfo.tbs.groupContext›,
      ‹(Tree.mf _ _ _).wf _ treesyncSt.tree›, ‹treesyncStateValid _ treesyncSt›, ‹IHaveVerifiedEveryLeafNode _ _ _ _›,
      ‹TreekemPrivStatePred tr me _›⟩,
      ⟨‹TreekemKeyscheduleStateGood tr _ _›,
        TreekemKeyscheduleStateAuthStrongExists.weak _ ⟨_, _, _, ‹TreekemKeyscheduleStateAuthStrong _ _ _ _›⟩,
        ‹TreeHasHash treesyncSt.tree _›⟩, ?_⟩
    exact ⟨_, rfl, ‹Trace.EventLogged (_: IAmInGroup) tr.erase›, rfl, rfl, rfl⟩
  step
  trivial

/-- Port of `process_welcome_proof`. -/
@[instance]
public
theorem processWelcome.proof (me: Participant) (keyPackageStoreSid authServiceSid pskStoreSid: Nat)
  (welcomeTs ratchetTreeTs: Nat):
  HoareTriple
    (processWelcome me keyPackageStoreSid authServiceSid pskStoreSid welcomeTs ratchetTreeTs)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold processWelcome
  step
  step
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  step by
    exact ⟨wf_invariant_of_publishable _ _ _ (wf_of_parse _ _ _ _ ‹_› ‹welcomeBytes.Publishable tr›),
      wf_of_parse _ _ _ _ ‹_› ‹ratchetTreeBytes.Publishable tr›⟩
  trivial

end Proofs

end MLS.TreeKEM
