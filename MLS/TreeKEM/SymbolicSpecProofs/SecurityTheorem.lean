module

public import MLS.TreeKEM.SymbolicProofs.EpochEvent
public import MLS.TreeKEM.SymbolicProofs.State.EpochSecrets
public import MLS.TreeKEM.SymbolicProofs.State.NodeKey
public import MLS.TreeKEM.SymbolicProofs.Tree.Labels
public import MLS.Bootstrap.SymbolicProofs.KeyPackage
public import MLS.Bootstrap.SymbolicProofs.State.InitKey
public import MLS.TreeSync.SymbolicProofs.State.SignatureKey

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
- As in MLS*, the theorem is stated on a proof trace satisfying the trace invariant (`tr.Invariant`),
  with MLS*'s `has_treekem_invariants` (`[HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant]`).
  Reachability of `tr.erase` would not be enough: the ghost data of `tr` (e.g. the labels of randomness) is arbitrary.
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

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

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

variable [HasSymbolicInvariants]

/-- Port of `all_psks_are_publishable`. -/
@[expose]
public
def AllPsksArePublishable (tr: ProofTrace) (psks: List (PreSharedKeyId Bytes × Bytes)): Prop :=
  ∀ pskId psk, (pskId, psk) ∈ psks → psk.Publishable tr

end Publishable

/-! ## Security theorem -/

section SecurityTheorem

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant]

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
    InitKeyIsCompromised tr.erase ev.groupContext ev.tree ∨
    -- (2) the attacker compromised a joiner's initialization key
    ((∃ joiner ∈ lastEpochLink.joiners, JoinersInitKeyIsCompromised tr.erase joiner) ∧
      AllPsksArePublishable tr ev.psks) ∨
    -- (3) the attacker compromised a joiner's signature key
    ((∃ joiner ∈ lastEpochLink.joiners, JoinersSignatureKeyIsCompromisedBeforeICheckedIt tr.erase ev.prin joiner) ∧
      AllPsksArePublishable tr ev.psks) ∨
    -- (4)-(7): the attacker knows the previous init secret, pre-shared keys and...
    -- (4) ... the commit is add-only
    (lastEpochLink.commitTy = .addOnlyCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr) ∨
    -- (5) ... the attacker compromised the node keys stored by a participant
    ((∃ li ln, leafAt ev.tree li = some ln ∧ NodeKeyIsCompromised tr.erase ln) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr) ∨
    -- (6) ... the attacker compromised the signature keys of a participant
    ((∃ li ln, ev.tree.containsLeafIndex li ∧ leafAt ev.tree li = some ln ∧
        SignatureKeyIsCompromisedBeforeICheckedLeafNode tr.erase ev.prin ln ev.groupContext.groupId li) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr) ∨
    -- (7) ... the attacker compromised the initialization key of a stale participant
    ((∃ li ln, leafAt ev.tree li = some ln ∧
        ln.data.source = .keyPackage ∧
        CorrespondingInitKeyIsCompromised tr.erase ln) ∧
      lastEpochLink.commitTy = .fullCommit ∧
      AllPsksArePublishable tr ev.psks ∧
      lastEpochLink.previousInitSecret.Publishable tr)
  | .justJoined { inviter } =>
    -- (8) the attacker compromised the inviter signature key
    (ev.tree.containsLeafIndex inviter ∧
      ∃ ln, leafAt ev.tree inviter = some ln ∧ InviterSignatureKeyIsCompromisedBeforeIJoined tr.erase ln ev) ∨
    -- (9) the inviter belongs to the same group as us
    (ev.tree.containsLeafIndex inviter ∧
      ∃ ln, leafAt ev.tree inviter = some ln ∧ InviterWasInSameGroupAsMe tr.erase ln ev)
  | .justCreated =>
    -- (10) the attacker compromised my epoch secret state
    ParticipantInitKeyIsCompromised tr.erase ev.prin ev.groupContext
:= by
  sorry

end SecurityTheorem

end MLS.TreeKEM
