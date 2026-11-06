module

public import MLS.TreeKEM.SymbolicProofs.EpochEvent
public import MLS.TreeKEM.SymbolicProofs.State.EpochSecrets
public import MLS.TreeKEM.SymbolicProofs.State.NodeKey
public import MLS.TreeKEM.SymbolicProofs.Tree.Labels
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProtocolInvariants
public import MLS.TreeKEM.SymbolicSpec.Reachability
public import MLS.TreeKEM.SymbolicSpecProofs.Reachability
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.Bootstrap.SymbolicSpec.KeyPackage

/-!
Port of `MLS.TreeKEM.Symbolic.SecurityTheorem`: the security theorem of TreeKEM.
When the init secret of an epoch is known to the attacker, the attacker compromised one of the keys
that protect it (states of participants, init keys, signature keys before they were checked, …).

Port-specific differences:
- MLS*'s `me` is the principal `ev.prin` of the event (DyLean's events do not record who triggered them).
- MLS*'s `prefix tr (find_event_triggered_at_timestamp tr me ev)` is the prefix before the first time
  the event was logged (`∃ i, tr.EventFirstLoggedAt ev i ∧ LocalStateCompromised … (tr.prefix i)`),
  as in `MLS.Bootstrap.keyPackageToInitLabel_isCorrupt`. The conjuncts that MLS* only needs to call
  `find_event_triggered_at_timestamp` (`i_have_verified_key_package tr me joiner`, `i_have_verified_leaf_node …`,
  the squashed `event_triggered tr me ev`) are dropped: they follow from `tr.EventFirstLoggedAt ev i`.
- MLS*'s `Some? (f x)` and `Some?.v (f x)` are existentials (`∃ y, f x = some y ∧ …`).
  MLS*'s leaf indices of `ev.tree` (`leaf_index ev.tree_height 0`, and `inviter < pow2 ev.tree_height` in `JustJoined`)
  are in the tree (`ev.tree.containsLeafIndex li`), since Lean's `leafAt` does not check it.
  This condition is omitted when the leaf index only serves to find a leaf (`InitKeyIsCompromised`, (5), (7)):
  every leaf index reaches a leaf of the tree.
- As in MLS*, the theorem is stated on a proof trace satisfying the trace invariant (`tr.Invariant`).
  Reachability of `tr.erase` would not be enough: the ghost data of `tr` (e.g. the labels of randomness) is arbitrary.
- The theorem has no typeclass parameters: it is stated on the top-level instances
  (`MLS.TreeKEM.SymbolicSpecProofs.Traceful.ProtocolInvariants`, MLS*'s `treesync_treekem_protocol_invariants`),
  which give MLS*'s `has_treekem_invariants`.
- The labels of MLS*'s predicates are unfolded, so that the theorem only states the compromise of states
  (`LocalStateCompromised`): `mk_principal_epoch_secret_label InitSecret prin gc` is the compromise of an init secret
  state of `prin` for `gc`, `init_key_label prin pk` the compromise of an init key state of `prin` whose key has
  public key `pk`, and the same for `signature_key_label` and `node_key_label`.
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.HPKE (hpkePk)
open DY.PersistentLocalState (LocalStateCompromised)

/-! ## Helper predicates for the security theorem -/

section Predicates

/-- Port of `participant_init_key_is_compromised`. -/
@[expose]
public
def ParticipantInitKeyIsCompromised (tr: ExecTrace) (participant: Participant) (groupContext: GroupContext Bytes): Prop :=
  ∃ confirmationTag secret,
    LocalStateCompromised participant
      ({ ty := .initSecret, context := groupContext, confirmationTag, secret }: TreeKEMEpochSecret) tr

/-- Port of `init_key_is_compromised`. -/
@[expose]
public
def InitKeyIsCompromised {l: Nat} (tr: ExecTrace) (groupContext: GroupContext Bytes) (tree: TreeSync Bytes tkt l): Prop :=
  ∃ li ln participant,
    leafAt tree li = some ln ∧
    credentialToPrincipal ln.data.credential = some participant ∧
    ParticipantInitKeyIsCompromised tr participant groupContext

/-- Port of `joiners_init_key_is_compromised`. -/
@[expose]
public
def JoinersInitKeyIsCompromised (tr: ExecTrace) (joiner: KeyPackage Bytes tkt): Prop :=
  ∃ joinerId,
    keyPackageToPrincipal joiner = some joinerId ∧
    ∃ leafPk initSk,
      hpkePk initSk = joiner.tbs.initKey.val ∧
      LocalStateCompromised joinerId ({ leafPk, initSk }: BootstrapInitKeyState) tr

/-- Port of `joiners_signature_key_is_compromised_before_i_checked_it`. -/
@[expose]
public
def JoinersSignatureKeyIsCompromisedBeforeICheckedIt (tr: ExecTrace) (me: Participant) (joiner: KeyPackage Bytes tkt): Prop :=
  ∃ joinerId,
    keyPackageToPrincipal joiner = some joinerId ∧
    ∃ i signatureSk,
      tr.EventFirstLoggedAt ({ prin := me, keyPackage := joiner }: KeyPackageHasBeenVerified) i ∧
      DySlop.Signature.vk signatureSk = joiner.tbs.leafNode.data.signatureKey.val ∧
      LocalStateCompromised joinerId ({ signatureSk }: TreeSyncSignatureKeyState) (tr.prefix i)

/-- Port of `node_key_is_compromised`. -/
@[expose]
public
def NodeKeyIsCompromised (tr: ExecTrace) (leafNode: LeafNode Bytes tkt): Prop :=
  ∃ prin,
    credentialToPrincipal leafNode.data.credential = some prin ∧
    ∃ (l: Nat) (path: TreeKEMPriv Bytes l),
      hpkePk path.getPathLeaf = leafNode.data.content.val ∧
      LocalStateCompromised prin ({ l, path }: TreeKEMNodeKeysState) tr

/-- Port of `signature_key_is_compromised_before_i_checked_leaf_node`. -/
@[expose]
public
def SignatureKeyIsCompromisedBeforeICheckedLeafNode (tr: ExecTrace) (me: Participant)
  (leafNode: LeafNode Bytes tkt) (groupId: MlsBytes Bytes) (leafIndex: Nat): Prop
:=
  ∃ leafNodeId,
    credentialToPrincipal leafNode.data.credential = some leafNodeId ∧
    ∃ i signatureSk,
      tr.EventFirstLoggedAt ({ prin := me, leafNode, groupId, leafIndex }: LeafNodeHasBeenVerified tkt) i ∧
      DySlop.Signature.vk signatureSk = leafNode.data.signatureKey.val ∧
      LocalStateCompromised leafNodeId ({ signatureSk }: TreeSyncSignatureKeyState) (tr.prefix i)

/-- Port of `corresponding_init_key_is_compromised`. -/
@[expose]
public
def CorrespondingInitKeyIsCompromised (tr: ExecTrace) (leafNode: LeafNode Bytes tkt): Prop :=
  ∃ prin,
    credentialToPrincipal leafNode.data.credential = some prin ∧
    ∃ (verifier: Participant) (keyPackage: KeyPackage Bytes tkt),
      keyPackage.tbs.leafNode = leafNode ∧
      IHaveVerifiedKeyPackage tr verifier keyPackage ∧ (
        (∃ leafPk initSk,
          hpkePk initSk = keyPackage.tbs.initKey.val ∧
          LocalStateCompromised prin ({ leafPk, initSk }: BootstrapInitKeyState) tr) ∨
        (∃ i signatureSk,
          tr.EventFirstLoggedAt ({ prin := verifier, keyPackage }: KeyPackageHasBeenVerified) i ∧
          DySlop.Signature.vk signatureSk = leafNode.data.signatureKey.val ∧
          LocalStateCompromised prin ({ signatureSk }: TreeSyncSignatureKeyState) (tr.prefix i))
      )

/--
Port of `inviter_signature_key_is_compromised_before_i_joined`.
MLS*'s `me` is `ev.prin`.
-/
@[expose]
public
def InviterSignatureKeyIsCompromisedBeforeIJoined (tr: ExecTrace) (inviterLeafNode: LeafNode Bytes tkt) (ev: IAmInGroup):
  Prop
:=
  ∃ inviterId,
    credentialToPrincipal inviterLeafNode.data.credential = some inviterId ∧
    ∃ i signatureSk,
      tr.EventFirstLoggedAt ev i ∧
      DySlop.Signature.vk signatureSk = inviterLeafNode.data.signatureKey.val ∧
      LocalStateCompromised inviterId ({ signatureSk }: TreeSyncSignatureKeyState) (tr.prefix i)

/-- Port of `inviter_was_in_same_group_as_me`. -/
@[expose]
public
def InviterWasInSameGroupAsMe (tr: ExecTrace) (inviterLeafNode: LeafNode Bytes tkt) (ev: IAmInGroup): Prop :=
  ∃ inviterId,
    credentialToPrincipal inviterLeafNode.data.credential = some inviterId ∧
    ∃ (inviterEv: IAmInGroup) (lastEpochLink: IProcessedCommitGroup),
      inviterEv.groupContext = ev.groupContext ∧
      (⟨inviterEv.treeHeight, inviterEv.tree⟩: OneTreeSync Bytes tkt) = ⟨ev.treeHeight, ev.tree⟩ ∧
      inviterEv.epochKeys.initSecret = ev.epochKeys.initSecret ∧
      inviterEv.psks = ev.psks ∧
      inviterEv.how = .processedCommit lastEpochLink ∧
      JoinersAreStaleParticipants ev.tree lastEpochLink.joiners ∧
      inviterEv.prin = inviterId ∧
      tr.EventLogged inviterEv

end Predicates

section Publishable

/-- Port of `all_psks_are_publishable`. -/
@[expose]
public
def AllPsksArePublishable (tr: ProofTrace) (psks: List (PreSharedKeyId Bytes × Bytes)): Prop :=
  ∀ pskId psk, (pskId, psk) ∈ psks → psk.Publishable tr

end Publishable

/-! ## Helper lemmas for the security theorem -/

section HelperLemmas

/-- Every leaf of a tree is at a leaf index of the tree (`leafAt` follows the path to the closest leaf). -/
theorem exists_containsLeafIndex_leafAt {Leaf Node: Type} {l: Nat} (t: Tree Leaf Node l) (li: Nat):
  ∃ li', t.containsLeafIndex li' ∧ leafAt t li' = leafAt t li
:= by
  induction t using Tree.childInduction li with
  | leaf t => exact ⟨t.position, Tree.containsLeafIndex_position t, by simp only [leafAt_zero]⟩
  | node t ih =>
    obtain ⟨li', h1, h2⟩ := ih
    refine ⟨li', Tree.containsLeafIndex_of_mem_child t h1, ?_⟩
    rw [leafAt_succ t li', leafAt_succ t li, Tree.child_eq_of_mem_child t h1, h2]

/--
The secrets whose label flows to the label of a publishable secret are corrupt
(the secret was publishable on the prefix `trBefore`).
-/
theorem isCorrupt_of_canFlow_publishable (trBefore tr: ProofTrace) (l: Label) (secret: Bytes)
  (hflow: l.canFlow (secret.label trBefore) trBefore.erase) (hinv: secret.Invariant trBefore)
  (hle: trBefore ≤ tr) (hpub: secret.Publishable tr):
  l.isCorrupt tr.erase
:= by
  rw [Bytes.label_later_fast secret trBefore tr hle hinv] at hflow
  grind [Label.canFlow, Trace.le_trans, Bytes.Publishable]

/-- Port of `psk_secret_label_corrupt_implies_all_psks_are_publishable`. -/
theorem allPsksArePublishable_of_isCorrupt (tr: ProofTrace) (psks: List (PreSharedKeyId Bytes × Bytes))
  (hpsks: PsksBytesInvariant tr psks) (h: (psksLabel tr psks).isCorrupt tr.erase):
  AllPsksArePublishable tr psks
:= by
  intro pskId psk hmem
  refine ⟨hpsks.2 _ hmem, ?_⟩
  rw [← canFlowPubEqIsCorrupt]
  exact (psksLabel_isCorrupt tr psks tr.erase).1 h _ hmem

/-- Port of `is_corrupt_joiners_label_implies_exists`. -/
theorem exists_isCorrupt_of_joinersLabel (tr: ExecTrace) (joiners: List (KeyPackage Bytes tkt))
  (h: ((joiners.map keyPackageToInitLabel).foldr Label.join Label.secret).isCorrupt tr):
  ∃ joiner ∈ joiners, (keyPackageToInitLabel joiner).isCorrupt tr
:= by
  induction joiners with
  | nil => exact absurd h (Label.secretIsCorrupt tr)
  | cons j js ih =>
    simp only [List.map_cons, List.foldr_cons, Label.joinIsCorrupt] at h
    grind

/-- Port of `is_corrupt_key_package_to_init_label_implies`. -/
theorem joinerKeyIsCompromised_of_isCorrupt (tr: ProofTrace) (me: Participant) (joiner: KeyPackage Bytes tkt)
  (h: (keyPackageToInitLabel joiner).isCorrupt tr.erase)
  (hev: IHaveVerifiedKeyPackage tr.erase me joiner) (hinv: tr.Invariant):
  JoinersInitKeyIsCompromised tr.erase joiner ∨
  JoinersSignatureKeyIsCompromisedBeforeICheckedIt tr.erase me joiner
:= by
  obtain ⟨prin, hcp, -⟩ := keyPackageToInitLabel_lemma tr me joiner hev hinv
  have := keyPackageToInitLabel_isCorrupt tr.erase me prin joiner h hcp hev
  grind [JoinersInitKeyIsCompromised, JoinersSignatureKeyIsCompromisedBeforeICheckedIt, signatureKeyLabel, initKeyLabel]

/-- Port of `is_corrupt_leaf_label_implies`. -/
theorem leafKeyIsCompromised_of_isCorrupt (tr: ProofTrace) (me: Participant)
  (groupId: MlsBytes Bytes) (ln: LeafNode Bytes tkt) (li: Nat)
  (h: (nodeSkLabelAuxLeaf ln groupId .yesCommitter li).isCorrupt tr.erase)
  (hev: IHaveVerifiedLeafNode tr.erase me ln groupId li) (hinv: tr.Invariant):
  NodeKeyIsCompromised tr.erase ln ∨
  SignatureKeyIsCompromisedBeforeICheckedLeafNode tr.erase me ln groupId li ∨
  (ln.data.source = .keyPackage ∧ CorrespondingInitKeyIsCompromised tr.erase ln)
:= by
  obtain ⟨prin, hcp⟩ := exists_credentialToPrincipal tr me ln groupId li hev hinv
  have hnode (hc: (nodeKeyLabel prin ln.data.content.val).isCorrupt tr.erase): NodeKeyIsCompromised tr.erase ln :=
    ⟨prin, hcp, hc⟩
  have hsig (hc: (guardedSignatureKeyLabel ln groupId li).isCorrupt tr.erase):
      SignatureKeyIsCompromisedBeforeICheckedLeafNode tr.erase me ln groupId li := by
    have := guardedSignatureKeyLabel_isCorrupt tr.erase me prin ln groupId li hc hcp hev
    grind [SignatureKeyIsCompromisedBeforeICheckedLeafNode, signatureKeyLabel]
  have hinit (hc: (initKeyAssociatedWith ln).isCorrupt tr.erase): CorrespondingInitKeyIsCompromised tr.erase ln := by
    obtain ⟨keyPackage, verifier, hver, rfl, hkc⟩ := initKeyAssociatedWith_isCorrupt tr.erase ln hc
    have := keyPackageToInitLabel_isCorrupt tr.erase verifier prin keyPackage hkc hcp hver
    refine ⟨prin, hcp, verifier, keyPackage, rfl, hver, ?_⟩
    grind [signatureKeyLabel, initKeyLabel]
  simp only [nodeSkLabelAuxLeaf, reduceCtorEq, ↓reduceIte, hcp] at h
  cases hs: ln.data.source <;> simp only [hs, Label.joinIsCorrupt] at h <;> grind

end HelperLemmas

/-! ## Security theorem -/

section SecurityTheorem

public
theorem reachableImpliesInvariant:
  ∀ trExec: ExecTrace,
    trExec.Reachable MLS.TreeKEM.reachability →
    ∃ trProof: ProofTrace,
      trProof.erase = trExec ∧
      trProof.Invariant
:= Trace.Reachable_implies_Invariant MLS.TreeKEM.reachability

/--
info: 'MLS.TreeKEM.reachableImpliesInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reachableImpliesInvariant

/-- Port of `treekem_security_theorem`. -/
public
theorem treekemSecurityTheorem:
  ∀ tr: ProofTrace, tr.Invariant →
  ∀ ev: IAmInGroup,
  tr.erase.EventLogged ev →
  ev.epochKeys.initSecret.Publishable tr →
  match ev.how with
  | .processedCommit lastEpochLink =>
    -- (1) the attacker compromised the epoch secret state
    (
      InitKeyIsCompromised tr.erase ev.groupContext ev.tree
    ) ∨
    -- (2) the attacker compromised a joiner's initialization key
    (
      (∃ joiner ∈ lastEpochLink.joiners, JoinersInitKeyIsCompromised tr.erase joiner) ∧
      AllPsksArePublishable tr ev.psks
    ) ∨
    -- (3) the attacker compromised a joiner's signature key
    (
      (∃ joiner ∈ lastEpochLink.joiners, JoinersSignatureKeyIsCompromisedBeforeICheckedIt tr.erase ev.prin joiner) ∧
      AllPsksArePublishable tr ev.psks
    ) ∨
    -- (4)-(7): the attacker knows the previous init secret, pre-shared keys and...
    -- (4) ... the commit is add-only
    (
      lastEpochLink.commitTy = .addOnlyCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr
    ) ∨
    -- (5) ... the attacker compromised the node keys stored by a participant
    (
      (∃ li ln, leafAt ev.tree li = some ln ∧ NodeKeyIsCompromised tr.erase ln) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr
    ) ∨
    -- (6) ... the attacker compromised the signature keys of a participant
    (
      (∃ li ln,
        ev.tree.containsLeafIndex li ∧
        leafAt ev.tree li = some ln ∧
        SignatureKeyIsCompromisedBeforeICheckedLeafNode tr.erase ev.prin ln ev.groupContext.groupId li
      ) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr
    ) ∨
    -- (7) ... the attacker compromised the initialization key of a stale participant
    (
      (∃ li ln,
        leafAt ev.tree li = some ln ∧
        ln.data.source = .keyPackage ∧
        CorrespondingInitKeyIsCompromised tr.erase ln
      ) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr
    )
  | .justJoined { inviter } =>
    -- (8) the attacker compromised the inviter signature key
    (
      ev.tree.containsLeafIndex inviter ∧
      ∃ ln, leafAt ev.tree inviter = some ln ∧
      InviterSignatureKeyIsCompromisedBeforeIJoined tr.erase ln ev
    ) ∨
    -- (9) the inviter belongs to the same group as us
    (
      ev.tree.containsLeafIndex inviter ∧
      ∃ ln, leafAt ev.tree inviter = some ln ∧
      InviterWasInSameGroupAsMe tr.erase ln ev
    )
  | .justCreated =>
    -- (10) the attacker compromised my epoch secret state
    ParticipantInitKeyIsCompromised tr.erase ev.prin ev.groupContext
:= by
  intro tr hinv ⟨me, how, groupContext, treeHeight, tree, psks, epochKeys⟩ hev hpub
  obtain ⟨i, hi⟩ := ProtocolEvent.exists_eventFirstLoggedAt tr.erase _ hev
  have hle: tr.prefix i ≤ tr := Trace.prefix_le_self tr i
  have hleE: (tr.prefix i).erase ≤ tr.erase := Trace.erase_le _ _ hle
  obtain ⟨hhash, hverif, hpred⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLoggedAt iAmInGroupPred tr _ i hinv hi.1
  dsimp only at hhash hverif hpred hpub ⊢
  have hverif' := IHaveVerifiedEveryLeafNode_le _ _ _ _ _ hleE hverif
  -- the leaves of the tree have been verified: their credentials are principals
  have hcred: ∀ li ln, leafAt tree li = some ln → (credentialToPrincipal ln.data.credential).isSome := by
    intro li ln hl
    obtain ⟨li', hc, hl'⟩ := exists_containsLeafIndex_leafAt tree li
    obtain ⟨prin, hprin⟩ := exists_credentialToPrincipal tr me ln _ li'
      (IHaveVerifiedLeafNode_of_leafAt _ _ _ _ li' ln hverif' hc (hl'.trans hl)) hinv
    simp [hprin]
  -- the init secret state label is corrupt when the epoch secret state of a member is compromised
  have hstate (hc: (mkEpochSecretLabel .initSecret groupContext).isCorrupt tr.erase):
      InitKeyIsCompromised tr.erase groupContext tree := by
    rw [show mkEpochSecretLabel .initSecret groupContext =
        mkGroupSecretLabel (mkPrincipalEpochSecretLabel .initSecret) groupContext from rfl,
      mkGroupSecretLabel_eq _ groupContext tree hhash] at hc
    exact mkTreeSecretLabel_isCorrupt tr.erase _ groupContext tree hcred hc
  cases how with
  | processedCommit lastEpochLink =>
    obtain ⟨previousInitSecret, _, _, _, commitTy, joiners⟩ := lastEpochLink
    obtain ⟨hinit, -, -, -, hpsks, hkps, -, hgood, hlabel⟩ := hpred
    obtain ⟨-, -, -, -, -, -, hflow, -⟩ := hlabel
    have hc := isCorrupt_of_canFlow_publishable _ tr _ _ hflow hgood.2.2.2.2.2.2.1.1 hle hpub
    simp only [Symbolic.API.KeySchedule.computeEpochSecretLabel, Label.joinIsCorrupt, Label.meetIsCorrupt] at hc
    rw [Bytes.label_later_fast previousInitSecret _ tr hle hinit, psksLabel_later _ tr psks hpsks hle] at hc
    have hprev (hc: (previousInitSecret.label tr).isCorrupt tr.erase): previousInitSecret.Publishable tr :=
      ⟨Bytes.Invariant.later_fast _ _ _ hle hinit, by rwa [← canFlowPubEqIsCorrupt]⟩
    have hallPsks := allPsksArePublishable_of_isCorrupt tr psks (PsksBytesInvariant_later _ _ _ hle hpsks)
    rcases hc with ⟨⟨hprevC, hcommit⟩ | hjoiners, hpsksC⟩ | hc
    · -- the attacker knows the previous init secret, the commit secret and the pre-shared keys
      have := hallPsks hpsksC
      have := hprev hprevC
      cases commitTy with
      | addOnlyCommit => grind  -- (4)
      | fullCommit =>
        -- (5)-(7)
        obtain ⟨li, ln, hcont, hl, hc⟩ := (nodeSkLabelAux_isCorrupt _ _ _ _).1 hcommit
        have hev := IHaveVerifiedLeafNode_of_leafAt _ _ _ _ li ln hverif' hcont hl
        have := leafKeyIsCompromised_of_isCorrupt tr me _ ln li hc hev hinv
        grind
    · -- the attacker knows the init key of a joiner (or its signature key) and the pre-shared keys
      obtain ⟨joiner, hj, hc⟩ := exists_isCorrupt_of_joinersLabel _ joiners hjoiners
      have hev := IHaveVerifiedEveryKeyPackage_le _ _ _ _ hleE hkps joiner hj
      have := joinerKeyIsCompromised_of_isCorrupt tr me joiner hc hev hinv
      have := hallPsks hpsksC
      grind  -- (2) or (3)
    · -- (1)
      exact Or.inl (hstate hc)
  | justJoined x =>
    obtain ⟨inviter⟩ := x
    obtain ⟨hcont, ln, inviterId, hl, hcp, hsig | ⟨inviterEv, ⟨hgc, hek, hpsks, hhow⟩, hprin, hlog⟩⟩ := hpred
    · -- (8)
      rw [Trace.prefix_erase] at hsig
      grind [InviterSignatureKeyIsCompromisedBeforeIJoined, signatureKeyLabel]
    · -- (9): the inviter has the same tree (no hash collision), it was in the same group
      have hlog' := Trace.EventLogged_le _ _ _ hleE hlog
      obtain ⟨j, hhash', -⟩ := ProtocolEvent.EventInv.Has.pred_of_eventLogged iAmInGroupPred tr _ hinv hlog'
      obtain ⟨inviterPrin, how', inviterGroupContext, treeHeight', tree', inviterPsks, inviterEpochKeys⟩ := inviterEv
      dsimp only at hgc hek hpsks hhow hprin hlog' hhash'
      subst hgc
      have htree: (⟨treeHeight', tree'⟩: OneTreeSync Bytes tkt) = ⟨treeHeight, tree⟩ :=
        (treeHashInj_spec tree' tree _ hhash' hhash).resolve_right (not_isHashCollision _)
      cases how' with
      | processedCommit lastEpochLink =>
        have hstale: JoinersAreStaleParticipants tree lastEpochLink.joiners := by
          obtain ⟨rfl, htree'⟩ := Sigma.mk.inj htree
          rw [heq_eq_eq] at htree'
          rwa [htree'] at hhow
        refine Or.inr ⟨hcont, ln, hl, inviterId, hcp,
          { prin := inviterPrin, how := .processedCommit lastEpochLink, groupContext := inviterGroupContext, treeHeight := treeHeight',
            tree := tree', psks := inviterPsks, epochKeys := inviterEpochKeys }, lastEpochLink, ?_⟩
        exact ⟨rfl, htree, by rw [hek], hpsks, rfl, hstale, hprin, hlog'⟩
      | justCreated | justJoined _ => exact absurd hhow id
  | justCreated =>
    -- (10)
    obtain ⟨-, rfl, ⟨ln, hl, hcp⟩, hgood, hlabel⟩ := hpred
    obtain ⟨-, -, -, -, -, -, hflow, -⟩ := hlabel
    have hc := isCorrupt_of_canFlow_publishable _ tr _ _ hflow hgood.2.2.2.2.2.2.1.1 hle hpub
    rw [Label.joinIsCorrupt] at hc
    rcases hc with hc | hc
    · exact absurd hc (Label.secretIsCorrupt _)
    · obtain ⟨li, ln', prin, hl', hcp', hc⟩ := hstate hc
      rw [leafAt_zero] at hl hl'
      grind

/--
info: 'MLS.TreeKEM.treekemSecurityTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms treekemSecurityTheorem

end SecurityTheorem

end MLS.TreeKEM
