module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessCommit
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants
public import MLS.TreeKEM.SymbolicProofs.API.Tree
public import MLS.TreeSync.SymbolicProofs.API.IsWellFormedInvariant
public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified.Invariant
import all MLS.TreeKEM.SymbolicSpec.Traceful.ProcessCommit
import all MLS.Bootstrap.SymbolicSpec.KeyPackage
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.TreeKEM.Code.API
import all MLS.TreeSync.Code.Operations
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessCommit.Proof`.

Port-specific differences:
- The proofs are DyLean Hoare triples (instances), assuming the invariants of
  `MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants` (MLS*'s `has_treesync_and_treekem_invariants`).
- The Hoare triples whose pre- or postcondition mentions the principal `me`, which is not an argument of the function
  (e.g. `processGroupContextExtensionsProposal'`, `processNoUpdatePath'`), take it as a ghost argument
  (`HoareTripleGhost`; callers write `step with ⟨ me ⟩`).
- MLS*'s `treesync_treekem_state_invariant_aux` with the provisional group context in the postconditions of
  `processUpdatePath'.proof` and `processNoUpdatePath'.proof` is stated with the current group context
  (the TreeSync state is indexed by the current group identifier); MLS*'s `new_treesync == st.treesync`
  is only used through `tree_add_only_rel`, which is stated instead.
- The refinements of the proposals (e.g. `P_add? proposal`) are dropped (see `MLS.TreeKEM.SymbolicSpec.Traceful.ProcessCommit`):
  MLS*'s `add_proposals_to_key_packages` is `proposalsToKeyPackages`, which skips the other proposals.
-/

-- The proofs assume the bundles of MLS*'s `has_treesync_and_treekem_invariants` as section variables;
-- each proof only uses some of them.
set_option linter.unusedSectionVars false

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap MLS.TreeKEM.Symbolic.API.KeySchedule

variable [HasSymbolicInvariants] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]

/-! ## Lemmas -/

/-- The leaf indices of the TreeSync and TreeKEM trees of a valid state (MLS* uses their common index type). -/
public
theorem TreesyncTreekemStateInvariant.containsLeafIndex_iff (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  (h: TreesyncTreekemStateInvariant tr me st) (li: Nat):
  (st.treekem.treeState.tree.containsLeafIndex li ↔ li < 2^st.treesync.levels) ∧
  (st.treesync.tree.containsLeafIndex li ↔ li < 2^st.treesync.levels)
:= by
  obtain ⟨-, ⟨hpos, -⟩, hrel, -⟩ := h
  grind [Tree.containsLeafIndex]

/-- The TreeSync tree of a valid state is at position `0`. -/
public
theorem TreesyncTreekemStateInvariant.position (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  (h: TreesyncTreekemStateInvariant tr me st):
  st.treesync.tree.position = 0
:= by
  obtain ⟨-, ⟨hpos, -⟩, hrel, -⟩ := h
  grind

/-- My leaf index is in the trees of a valid state. -/
public
theorem TreesyncTreekemStateInvariant.leafIndex_lt (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState)
  (h: TreesyncTreekemStateInvariant tr me st):
  st.leafIndex < 2^st.treesync.levels
:= by
  have := (h.containsLeafIndex_iff tr me st st.leafIndex).1
  obtain ⟨-, ⟨-, -, hpriv⟩, -⟩ := h
  grind [treekemPrivInvariant]

/-- `IAmInTreeAt`, through `leafAtNat` (when the tree contains the leaf index). -/
public
theorem IAmInTreeAt.leafAtNat {l: Nat} {me: Participant} {t: TreeSync Bytes tkt l} {li: Nat}
  (h: IAmInTreeAt me t li) (hli: t.containsLeafIndex li):
  ∃ ln, API.leafAtNat t li = some ln ∧ credentialToPrincipal ln.data.credential = some me
:= by
  simpa [IAmInTreeAt, API.leafAtNat, hli] using h

/-- `IAmInTreeAt`, from `leafAtNat`. -/
public
theorem IAmInTreeAt.of_leafAtNat {l: Nat} {me: Participant} {t: TreeSync Bytes tkt l} {li: Nat}
  (h: ∃ ln, API.leafAtNat t li = some ln ∧ credentialToPrincipal ln.data.credential = some me):
  IAmInTreeAt me t li
:= by
  simp only [API.leafAtNat] at h
  split at h <;> simp_all [IAmInTreeAt]

/-- Port of `joiner_is_in_tree`. -/
@[expose]
public
def JoinerIsInTree {groupId: MlsBytes Bytes} (st: TreeSyncState Bytes tkt DyAsToken groupId)
  (joiner: KeyPackage Bytes tkt × Nat): Prop :=
  joiner.2 < 2^st.levels ∧
  leafAt st.tree joiner.2 = some joiner.1.tbs.leafNode

/-- Port of `joiners_are_in_tree`. -/
@[expose]
public
def JoinersAreInTree {groupId: MlsBytes Bytes} (st: TreeSyncState Bytes tkt DyAsToken groupId)
  (joiners: List (KeyPackage Bytes tkt × Nat)): Prop :=
  ∀ joiner ∈ joiners, JoinerIsInTree st joiner

/-- Port of `i_am_not_a_joiner`. -/
@[expose]
public
def IAmNotAJoiner (leafIndex: Nat) (joinerIndices: List Nat): Prop :=
  leafIndex ∉ joinerIndices

/-- `joiner_is_in_tree`, through `leafAtNat` (for trees at position `0`). -/
public
theorem JoinerIsInTree_iff {groupId: MlsBytes Bytes} (st: TreeSyncState Bytes tkt DyAsToken groupId)
  (joiner: KeyPackage Bytes tkt × Nat) (hpos: st.tree.position = 0):
  JoinerIsInTree st joiner ↔ TreeSync.API.leafAtNat st.tree joiner.2 = some joiner.1.tbs.leafNode
:= by
  simp only [JoinerIsInTree, TreeSync.API.leafAtNat, Tree.containsLeafIndex, hpos]
  split <;> grind

/-- Port of `joiners_are_in_tree_ind`. -/
theorem JoinersAreInTree_cons {groupId groupId': MlsBytes Bytes}
  (stOld: TreeSyncState Bytes tkt DyAsToken groupId) (stNew: TreeSyncState Bytes tkt DyAsToken groupId')
  (joiners: List (KeyPackage Bytes tkt × Nat)) (joiner: KeyPackage Bytes tkt) (joinerIndex: Nat)
  (hposOld: stOld.tree.position = 0) (hposNew: stNew.tree.position = 0)
  (h: JoinersAreInTree stOld joiners)
  (hnone: TreeSync.API.leafAtNat stOld.tree joinerIndex = none)
  (hleaves: ∀ li, TreeSync.API.leafAtNat stNew.tree li =
    if li = joinerIndex then some joiner.tbs.leafNode else TreeSync.API.leafAtNat stOld.tree li):
  JoinersAreInTree stNew ((joiner, joinerIndex) :: joiners)
:= by
  intro j hj
  rw [JoinerIsInTree_iff _ _ hposNew, hleaves]
  rcases List.mem_cons.mp hj with rfl | hj
  · simp
  · have := (JoinerIsInTree_iff _ _ hposOld).mp (h j hj)
    grind

/-- Port of `proposal_and_sender_is_publishable`. -/
public
def ProposalAndSenderIsPublishable (tr: ProofTrace) (p: ProposalAndSender): Prop :=
  Proposal.mf.wf (Bytes.Publishable · tr) p.proposal

/-- Port of `proposal_and_sender_is_publishable_later`. -/
public
theorem ProposalAndSenderIsPublishable_later (tr1 tr2: ProofTrace) (p: ProposalAndSender)
  : tr1 ≤ tr2 →
    ProposalAndSenderIsPublishable tr1 p →
    ProposalAndSenderIsPublishable tr2 p
:= by
  grind [ProposalAndSenderIsPublishable]

grind_pattern ProposalAndSenderIsPublishable_later => tr1 ≤ tr2, ProposalAndSenderIsPublishable tr1 p
grind_pattern [grind_later] ProposalAndSenderIsPublishable_later => tr1 ≤ tr2, ProposalAndSenderIsPublishable tr1 p

/-- `proposalsToKeyPackages` of a list with a head. -/
theorem proposalsToKeyPackages_cons (p: Proposal Bytes) (t: List (Proposal Bytes)):
  proposalsToKeyPackages (p :: t) = proposalsToKeyPackages [p] ++ proposalsToKeyPackages t
:= by
  cases p <;> simp [proposalsToKeyPackages]

/-- `proposalsToKeyPackages` of one proposal has at most one element. -/
theorem proposalsToKeyPackages_singleton_reverse (p: Proposal Bytes):
  (proposalsToKeyPackages [p]).reverse = proposalsToKeyPackages [p]
:= by
  cases p <;> simp [proposalsToKeyPackages]

/-- `sortProposals'` keeps the add proposals, in order. -/
theorem proposalsToKeyPackages_sortProposals' (proposals: List ProposalAndSender):
  proposalsToKeyPackages (proposals.map (·.proposal)) = proposalsToKeyPackages (sortProposals' proposals).adds
:= by
  induction proposals with
  | nil => simp [sortProposals', proposalsToKeyPackages]
  | cons hd t ih =>
    obtain ⟨proposal, sender⟩ := hd
    cases proposal <;> simp_all [sortProposals', proposalsToKeyPackages]

/-- The proposals sorted by `sortProposals'` come from its input. -/
theorem mem_sortProposals' (proposals: List ProposalAndSender):
  (∀ p ∈ (sortProposals' proposals).groupContextExtensions, p ∈ proposals.map (·.proposal)) ∧
  (∀ p ∈ (sortProposals' proposals).adds, p ∈ proposals.map (·.proposal)) ∧
  (∀ p ∈ (sortProposals' proposals).updates, p ∈ proposals) ∧
  (∀ p ∈ (sortProposals' proposals).removes, p ∈ proposals.map (·.proposal)) ∧
  (∀ psk ∈ (sortProposals' proposals).psks, .psk { psk } ∈ proposals.map (·.proposal)) ∧
  (∀ p ∈ (sortProposals' proposals).other, p ∈ proposals.map (·.proposal))
:= by
  induction proposals with
  | nil => simp [sortProposals']
  | cons hd t ih =>
    obtain ⟨proposal, sender⟩ := hd
    cases proposal <;> simp_all [sortProposals']

/--
Port of `_sort_proposals_proof`.
MLS*'s `add_proposals_to_key_packages` is `proposalsToKeyPackages`.
-/
theorem sortProposals'_proof (tr: ProofTrace) (proposals: List ProposalAndSender)
  (h: ∀ p ∈ proposals.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p):
  proposalsToKeyPackages (proposals.map (·.proposal)) = proposalsToKeyPackages (sortProposals' proposals).adds ∧
  (∀ p ∈ (sortProposals' proposals).groupContextExtensions, Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
  (∀ p ∈ (sortProposals' proposals).adds, Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
  (∀ p ∈ (sortProposals' proposals).updates, ProposalAndSenderIsPublishable tr p) ∧
  (∀ p ∈ (sortProposals' proposals).removes, Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
  PskIdsGood tr (sortProposals' proposals).psks ∧
  (∀ p ∈ (sortProposals' proposals).other, Proposal.mf.wf (Bytes.Publishable · tr) p)
:= by
  obtain ⟨hgce, hadd, hupd, hrem, hpsk, hother⟩ := mem_sortProposals' proposals
  refine ⟨proposalsToKeyPackages_sortProposals' proposals, by grind, by grind, ?_, by grind, ?_, by grind⟩
  · grind [ProposalAndSenderIsPublishable]
  · intro psk hpsk'
    simpa [Proposal.mf.wf_eq, PreSharedKey.mf.wf_eq] using h _ (hpsk psk hpsk')

/-- The proposals of a list are publishable (stated with a definition, so that `step` can monotonize it). -/
@[expose]
public
def ProposalsArePublishable (tr: ProofTrace) (l: List (Proposal Bytes)): Prop :=
  ∀ p ∈ l, Proposal.mf.wf (Bytes.Publishable · tr) p

public
theorem ProposalsArePublishable_later (tr1 tr2: ProofTrace) (l: List (Proposal Bytes))
  : tr1 ≤ tr2 →
    ProposalsArePublishable tr1 l →
    ProposalsArePublishable tr2 l
:= by
  grind [ProposalsArePublishable]

grind_pattern ProposalsArePublishable_later => tr1 ≤ tr2, ProposalsArePublishable tr1 l
grind_pattern [grind_later] ProposalsArePublishable_later => tr1 ≤ tr2, ProposalsArePublishable tr1 l

/-- The proposals (with their sender) of a list are publishable (see `ProposalsArePublishable`). -/
def ProposalAndSendersArePublishable (tr: ProofTrace) (l: List ProposalAndSender): Prop :=
  ∀ p ∈ l, ProposalAndSenderIsPublishable tr p

theorem ProposalAndSendersArePublishable_later (tr1 tr2: ProofTrace) (l: List ProposalAndSender)
  : tr1 ≤ tr2 →
    ProposalAndSendersArePublishable tr1 l →
    ProposalAndSendersArePublishable tr2 l
:= by
  grind [ProposalAndSendersArePublishable]

grind_pattern ProposalAndSendersArePublishable_later => tr1 ≤ tr2, ProposalAndSendersArePublishable tr1 l
grind_pattern [grind_later] ProposalAndSendersArePublishable_later => tr1 ≤ tr2, ProposalAndSendersArePublishable tr1 l

/-- The invariant of the states during the processing of the proposals (MLS*'s `acc_inv`). -/
def ProcessProposalsAccInv (me: Participant) (st0: TreeSyncTreeKEMState) (tr: ProofTrace) (st: TreeSyncTreeKEMState): Prop :=
  TreesyncTreekemStateInvariant tr me st ∧
  st.treekem.keyscheduleState = st0.treekem.keyscheduleState ∧
  st.groupContext = { st0.groupContext with extensions := st.groupContext.extensions }

theorem ProcessProposalsAccInv_later (me: Participant) (st0: TreeSyncTreeKEMState) (tr1 tr2: ProofTrace)
  (st: TreeSyncTreeKEMState)
  : tr1 ≤ tr2 →
    ProcessProposalsAccInv me st0 tr1 st →
    ProcessProposalsAccInv me st0 tr2 st
:= by
  grind [ProcessProposalsAccInv]

grind_pattern ProcessProposalsAccInv_later => tr1 ≤ tr2, ProcessProposalsAccInv me st0 tr1 st
grind_pattern [grind_later] ProcessProposalsAccInv_later => tr1 ≤ tr2, ProcessProposalsAccInv me st0 tr1 st

/-- The invariant of the accumulator of the fold over the add proposals (MLS*'s `add_acc_inv`). -/
def ProcessAddProposalsAccInv (me: Participant) (st0: TreeSyncTreeKEMState) (adds: List (Proposal Bytes)) (tr: ProofTrace)
  (lSt: List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState) (proposals: List (Proposal Bytes)): Prop :=
  TreesyncTreekemStateInvariant tr me lSt.2 ∧
  lSt.2.treekem.keyscheduleState = st0.treekem.keyscheduleState ∧
  lSt.2.groupContext = st0.groupContext ∧
  IHaveVerifiedEveryKeyPackage tr.erase me (lSt.1.map (·.1)) ∧
  proposalsToKeyPackages adds = (lSt.1.map (·.1)).reverse ++ proposalsToKeyPackages proposals ∧
  JoinersAreInTree lSt.2.treesync lSt.1 ∧
  IAmNotAJoiner lSt.2.leafIndex (lSt.1.map (·.2)) ∧
  TreeSync.API.treeAddOnlyRel st0.treesync.tree lSt.2.treesync.tree

theorem ProcessAddProposalsAccInv_later (me: Participant) (st0: TreeSyncTreeKEMState) (adds: List (Proposal Bytes))
  (tr1 tr2: ProofTrace) (lSt: List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState) (proposals: List (Proposal Bytes))
  : tr1 ≤ tr2 →
    ProcessAddProposalsAccInv me st0 adds tr1 lSt proposals →
    ProcessAddProposalsAccInv me st0 adds tr2 lSt proposals
:= by
  grind [ProcessAddProposalsAccInv]

grind_pattern ProcessAddProposalsAccInv_later => tr1 ≤ tr2, ProcessAddProposalsAccInv me st0 adds tr1 lSt proposals
grind_pattern [grind_later] ProcessAddProposalsAccInv_later =>
  tr1 ≤ tr2,
  ProcessAddProposalsAccInv me st0 adds tr1 lSt proposals

/-- The invariant of the folds over the group context extensions and the remove proposals (ghost of `foldlM.proof`). -/
def ProcessProposalsLoopInv (me: Participant) (st0: TreeSyncTreeKEMState) {l: List (Proposal Bytes)}
  (c: l.Cursor × TreeSyncTreeKEMState) (tr: ProofTrace): Prop :=
  ProposalsArePublishable tr c.1.suffix ∧ ProcessProposalsAccInv me st0 tr c.2

theorem ProcessProposalsLoopInv_later (me: Participant) (st0: TreeSyncTreeKEMState) {l: List (Proposal Bytes)}
  (c: l.Cursor × TreeSyncTreeKEMState) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    ProcessProposalsLoopInv me st0 c tr1 →
    ProcessProposalsLoopInv me st0 c tr2
:= by
  grind [ProcessProposalsLoopInv]

grind_pattern ProcessProposalsLoopInv_later => tr1 ≤ tr2, ProcessProposalsLoopInv me st0 c tr1
grind_pattern [grind_later] ProcessProposalsLoopInv_later => tr1 ≤ tr2, ProcessProposalsLoopInv me st0 c tr1

/-- The invariant of the fold over the update proposals (ghost of `foldlM.proof`). -/
def ProcessUpdateProposalsLoopInv (me: Participant) (st0: TreeSyncTreeKEMState) {l: List ProposalAndSender}
  (c: l.Cursor × TreeSyncTreeKEMState) (tr: ProofTrace): Prop :=
  ProposalAndSendersArePublishable tr c.1.suffix ∧ ProcessProposalsAccInv me st0 tr c.2

theorem ProcessUpdateProposalsLoopInv_later (me: Participant) (st0: TreeSyncTreeKEMState) {l: List ProposalAndSender}
  (c: l.Cursor × TreeSyncTreeKEMState) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    ProcessUpdateProposalsLoopInv me st0 c tr1 →
    ProcessUpdateProposalsLoopInv me st0 c tr2
:= by
  grind [ProcessUpdateProposalsLoopInv]

grind_pattern ProcessUpdateProposalsLoopInv_later => tr1 ≤ tr2, ProcessUpdateProposalsLoopInv me st0 c tr1
grind_pattern [grind_later] ProcessUpdateProposalsLoopInv_later => tr1 ≤ tr2, ProcessUpdateProposalsLoopInv me st0 c tr1

/-- The invariant of the fold over the add proposals (ghost of `foldlM.proof`), from the state `st0` before the fold. -/
def ProcessAddProposalsLoopInv (me: Participant) (st0: TreeSyncTreeKEMState) {adds: List (Proposal Bytes)}
  (c: adds.Cursor × (List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState)) (tr: ProofTrace): Prop :=
  ProposalsArePublishable tr c.1.suffix ∧ ProcessAddProposalsAccInv me st0 adds tr c.2 c.1.suffix

theorem ProcessAddProposalsLoopInv_later (me: Participant) (st0: TreeSyncTreeKEMState) {adds: List (Proposal Bytes)}
  (c: adds.Cursor × (List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState)) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    ProcessAddProposalsLoopInv me st0 c tr1 →
    ProcessAddProposalsLoopInv me st0 c tr2
:= by
  grind [ProcessAddProposalsLoopInv]

grind_pattern ProcessAddProposalsLoopInv_later => tr1 ≤ tr2, ProcessAddProposalsLoopInv me st0 c tr1
grind_pattern [grind_later] ProcessAddProposalsLoopInv_later => tr1 ≤ tr2, ProcessAddProposalsLoopInv me st0 c tr1

/--
Port of `_compute_confirmed_transcript_hash_proof`.
MLS*'s `match _compute_confirmed_transcript_hash st tx_hash_input` is the success hypothesis `h`;
the commit of MLS*'s `tx_hash_input.content.content.content` is any `commit` in a commit content (`hcommit`).
-/
public
theorem computeConfirmedTranscriptHash'_proof (tr: ProofTrace) (st: TreeSyncTreeKEMState)
  (txHashInput: ConfirmedTranscriptHashInput Bytes) (confirmedTranscriptHash: MlsBytes Bytes)
  (h: computeConfirmedTranscriptHash' st txHashInput = .success confirmedTranscriptHash)
  (htag: st.treekem.keyscheduleState.epochKeys.confirmationTag.Publishable tr)
  (hcth: st.groupContext.confirmedTranscriptHash.val.Publishable tr)
  (hwf: ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInput):
  (∀ commit, txHashInput.content.content = { contentType := .commit, content := commit } →
    CommitIsLastInTxHash commit confirmedTranscriptHash.val) ∧
  confirmedTranscriptHash.val.Publishable tr
:= by
  simp only [computeConfirmedTranscriptHash', computeInterimTranscriptHash, Result.bind_eq_success] at h
  obtain ⟨interim, ⟨tag, htag', hinterim⟩, cth, hcthEq, hres⟩ := h
  have hcthVal := (mkMlsBytes_eq_success _ _ _ _).1 hres
  have := (mkMlsBytes_eq_success _ _ _ _).1 htag'
  have hcompat := preIsHashCompatible_publishable tr
  have hinterimPub: interim.Publishable tr := by
    apply hcompat _ _ _ hinterim
    apply BytesCompatiblePred.pred_concat (pred := (Bytes.Publishable · tr)) _ _ hcth
    apply (pred_serializeNE_iff InterimTranscriptHashInput.mf (Bytes.Publishable · tr) _).2
    rw [InterimTranscriptHashInput.mf.wf_eq]
    grind
  obtain ⟨-, hhash⟩ := (computeConfirmedTranscriptHash_eq_success _ _ _).1 hcthEq
  refine ⟨fun commit hcommit => ⟨(txHashInput, interim), hcthEq.trans (by grind), hashHash_length _ _ hinterim, hcommit⟩, ?_⟩
  rw [← hcthVal]
  apply hcompat _ _ _ hhash
  exact BytesCompatiblePred.pred_concat (pred := (Bytes.Publishable · tr)) _ _ hinterimPub ((pred_serializeNE_iff _ _ _).2 hwf)

/-- The commit of a confirmed transcript hash input is well-formed. -/
public
theorem commit_wf_of_txHashInput (pred: Bytes → Prop) [BytesCompatiblePred pred]
  (txHashInput: ConfirmedTranscriptHashInput Bytes) (commit: Commit Bytes)
  (hcontent: txHashInput.content.content = { contentType := .commit, content := commit })
  (hwf: ConfirmedTranscriptHashInput.mf.wf pred txHashInput):
  Commit.mf.wf pred commit
:= by
  simp only [ConfirmedTranscriptHashInput.mf.wf_eq, FramedContent.mf.wf_eq, MlsTaggedContent.mf.wf_eq] at hwf
  have := hwf.1.2.2
  rw [hcontent] at this
  exact (MlsUntaggedContent.mf.wf_commit _ _).mp this

/--
The confirmed transcript hash of a commit contains the joiners of its proposals, and is publishable
(`_compute_confirmed_transcript_hash_proof` and `intro_tx_hash_contains_joiners`, as in MLS*'s `_process_commit_proof`).
-/
public
theorem computeConfirmedTranscriptHash'_txHashContainsJoiners (tr: ProofTrace) (me: Participant)
  (st: TreeSyncTreeKEMState) (txHashInput: ConfirmedTranscriptHashInput Bytes) (commit: Commit Bytes)
  (confirmedTranscriptHash: MlsBytes Bytes) (proposals: List (Proposal Bytes))
  (h: computeConfirmedTranscriptHash' st txHashInput = .success confirmedTranscriptHash)
  (hcontent: txHashInput.content.content = { contentType := .commit, content := commit })
  (hproposals: ProposalOrRefsRel commit.proposals.val proposals)
  (hwf: ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInput)
  (hinv: TreesyncTreekemStateAllInvariants tr me st):
  TxHashContainsJoiners confirmedTranscriptHash.val (proposalsToKeyPackages proposals) ∧
  confirmedTranscriptHash.val.Publishable tr
:= by
  obtain ⟨hinv, ⟨hgood, -, -⟩, -⟩ := hinv
  have hgc := hinv.2.2.2.2.1
  rw [GroupContext.mf.wf_eq] at hgc
  obtain ⟨hlast, hpub⟩ := computeConfirmedTranscriptHash'_proof tr st txHashInput confirmedTranscriptHash h
    hgood.2.2.2.2.2.2.2 hgc.2.2.1 hwf
  exact ⟨TxHashContainsJoiners.intro _ _ commit proposals (hlast commit hcontent) hproposals rfl, hpub⟩

/-- Port of `compute_expected_commit_secret_label`. -/
@[expose]
public
def computeExpectedCommitSecretLabel {l: Nat} (isFullCommit: Bool) (tree: TreeSync Bytes tkt l) (groupId: MlsBytes Bytes): Label :=
  if isFullCommit then nodeSkLabel tree groupId else Label.pub

/--
The precondition of `rememberPsk` for the resumption PSK of an epoch I am in
(MLS*'s `intro_i_am_in_group_context` and `mk_group_secret_label_can_flow_my_label`, in the callers of `remember_psk`).
-/
public
theorem rememberPsk_resumptionPsk_pre {l: Nat} (tr: ProofTrace) (me: Participant) (groupContext: GroupContext Bytes)
  (tree: TreeSync Bytes tkt l) (leafIndex: Nat) (resumptionPsk: Bytes)
  (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext)
  (hth: TreeHasHash tree groupContext.treeHash.val) (hme: IAmInTreeAt me tree leafIndex)
  (hinv: resumptionPsk.Invariant tr)
  (hlabel: (resumptionPsk.label tr).canFlow (mkEpochSecretLabel .resumptionPsk groupContext) tr.erase):
  PreSharedKeyIdShort.mf.wf (Bytes.Publishable · tr) (.resumptionPsk groupContext.groupId groupContext.epoch) ∧
  resumptionPsk.KnowableBy (pskLabel me (.resumptionPsk groupContext.groupId groupContext.epoch)) tr
:= by
  rw [GroupContext.mf.wf_eq] at hgc
  have := mkGroupSecretLabel_canFlow_myLabel tr.erase me mkResumptionPskLabel groupContext
    (IAmInGroupContext.intro me groupContext tree leafIndex ⟨hth, hme⟩)
  simp only [mkEpochSecretLabel] at hlabel
  refine ⟨by simpa using hgc.1, hinv, ?_⟩
  change (resumptionPsk.label tr).canFlow (mkResumptionPskLabel me groupContext) tr.erase
  grind [Label.canFlow]

/-- Transport of a property along a cast of an index. -/
public
theorem cast_transport {F: Nat → Type} {a b: Nat} (h: a = b) (x: F a) (Q: (n: Nat) → F n → Prop) (hq: Q a x):
  Q b (h ▸ x)
:= by
  subst h
  exact hq

/-- Transport of a property of paths along a cast of their height. -/
public
theorem Path.heq_transport {Leaf Node: Type} {l1 l2: Nat} (p1: Path Leaf Node l1) (p2: Path Leaf Node l2)
  (hl: l1 = l2) (h: HEq p1 p2) (Q: (l: Nat) → Path Leaf Node l → Prop) (hq: Q l2 p2):
  Q l1 p1
:= by
  subst hl
  cases h
  exact hq

/-- The leaf of a path does not depend on a cast of its height. -/
public
theorem Path.getPathLeaf_of_heq {Leaf Node: Type} {l1 l2: Nat} (p1: Path Leaf Node l1) (p2: Path Leaf Node l2)
  (hl: l1 = l2) (h: HEq p1 p2):
  p1.getPathLeaf = p2.getPathLeaf
:= by
  subst hl
  cases h
  rfl

/-- Path filtering on the TreeSync tree implies path filtering on the related TreeKEM tree (after a cast of the path). -/
theorem pathFilteringOk_of_treesyncTreekemStateRel {groupId: MlsBytes Bytes} {leafInd: Nat} {PathLeaf PathNode: Type}
  (stTs: TreeSyncState Bytes tkt DyAsToken groupId) (stTk: TreeKEMTreeState Bytes leafInd)
  (hrel: treesyncTreekemStateRel stTs stTk) (li: Nat)
  (pTs: Path PathLeaf (Option PathNode) stTs.levels) (pTk: Path PathLeaf (Option PathNode) stTk.levels)
  (hheq: HEq pTk pTs) (h: pathFilteringOk stTs.tree li pTs):
  pathFilteringOk stTk.tree li pTk
:= by
  induction stTs, stTk, hrel using treesyncTreekemStateRel_induction with | mk l tsTree tokens priv =>
  cases hheq
  simpa [pathFilteringOk_treesyncToTreekem] using h

/-- Transport of a property of TreeSync states along a cast of their group identifier (as in `_make_provisional_group_context`). -/
public
theorem TreeSyncState.mpr_iff {TokenT: Type} {g1 g2: MlsBytes Bytes} (h: g1 = g2) (ts: TreeSyncState Bytes tkt TokenT g2)
  (P: (g: MlsBytes Bytes) → TreeSyncState Bytes tkt TokenT g → Prop):
  P g1 ((congrArg (TreeSyncState Bytes tkt TokenT) h).mpr ts) ↔ P g2 ts
:= by
  subst h
  rfl

/--
Port of `treesync_treekem_state_invariant_aux_change_group_context`.
MLS*'s equality of the group identifiers is the cast of the TreeSync state.
-/
public
theorem TreesyncTreekemStateInvariantAux_changeGroupContext {leafIndex: Nat} (tr: ProofTrace) (me: Participant)
  (groupContext1 groupContext2: GroupContext Bytes) (h: groupContext2.groupId = groupContext1.groupId)
  (treesync: TreeSyncState Bytes tkt DyAsToken groupContext1.groupId) (treekem: TreeKEMTreeState Bytes leafIndex)
  (hinv: TreesyncTreekemStateInvariantAux tr me groupContext1 treesync treekem)
  (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext2):
  TreesyncTreekemStateInvariantAux tr me groupContext2 ((congrArg (TreeSyncState Bytes tkt DyAsToken) h).mpr treesync) treekem
:= by
  obtain ⟨hvalid, htk, hrel, hme, -, hwf, hasp, hverif, hpriv⟩ := hinv
  refine ⟨?_, htk, ?_, ?_, hgc, ?_, ?_, ?_, hpriv⟩ <;>
    first
    | exact (TreeSyncState.mpr_iff h treesync (fun _ ts => ts.TreeValid)).2 hvalid
    | exact (TreeSyncState.mpr_iff h treesync (fun _ ts => treesyncTreekemStateRel ts treekem)).2 hrel
    | exact (TreeSyncState.mpr_iff h treesync (fun _ ts => IAmInTreeAt me ts.tree leafIndex)).2 hme
    | exact (TreeSyncState.mpr_iff h treesync (fun _ ts => (TreeSync.mf tkt ts.levels).wf (Bytes.Publishable · tr) ts.tree)).2 hwf
    | exact (TreeSyncState.mpr_iff h treesync (fun _ ts => treesyncStateValid (dyAsp tr) ts)).2 hasp
    | exact (TreeSyncState.mpr_iff h treesync (fun g ts => IHaveVerifiedEveryLeafNode tr.erase me ts.tree g)).2 hverif

/-! ## Process proposals -/

section Proofs

variable [TraceInvariant] [HasTreesyncInvariants tkt] [HasTreeKEMProofTrace]
variable [HasKeyPackageInvariant] [HasTreesyncTreekemLinkInvariants]

public
instance (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HasGhostArgumentType (processGroupContextExtensionsProposal' st proposal) Participant
where
  dummy := ()

/--
Port of `_process_group_context_extensions_proposal_proof`.
The principal `me` (not an argument of the function) is the ghost argument.
-/
@[instance]
public
theorem processGroupContextExtensionsProposal'.proof (me: Participant) (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HoareTripleGhost
    (processGroupContextExtensionsProposal' st proposal)
    me
    (fun tr =>
      Proposal.mf.wf (Bytes.Publishable · tr) proposal ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun stOut tr =>
      stOut.treekem.keyscheduleState = st.treekem.keyscheduleState ∧
      stOut.groupContext = { st.groupContext with extensions := stOut.groupContext.extensions } ∧
      TreesyncTreekemStateInvariant tr me stOut
    )
:= by
  apply HoareTripleGhost.mk
  unfold processGroupContextExtensionsProposal'
  split
  · step
    simp only [Proposal.mf.wf_eq, GroupContextExtensions.mf.wf_eq, TreesyncTreekemStateInvariant,
      TreesyncTreekemStateInvariantAux, GroupContext.mf.wf_eq] at *
    grind
  · intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

/-- Port of `_process_add_proposal_aux_proof`. -/
@[instance]
public
theorem processAddProposalAux'.proof (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HoareTriple
    (processAddProposalAux' me authServiceSid st proposal)
    (fun tr =>
      Proposal.mf.wf (Bytes.Publishable · tr) proposal ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun (joiner, joinerIndex, stOut) tr =>
      stOut.treekem.keyscheduleState = st.treekem.keyscheduleState ∧
      stOut.groupContext = st.groupContext ∧
      TreeSync.API.treeAddOnlyRel st.treesync.tree stOut.treesync.tree ∧
      TreesyncTreekemStateInvariant tr me stOut ∧
      proposal = .add { keyPackage := joiner } ∧
      IHaveVerifiedKeyPackage tr.erase me joiner ∧
      stOut.leafIndex = st.leafIndex ∧
      st.leafIndex ≠ joinerIndex ∧
      API.leafAtNat st.treesync.tree joinerIndex = none ∧
      ∀ li, API.leafAtNat stOut.treesync.tree li =
        if li = joinerIndex then some joiner.tbs.leafNode else API.leafAtNat st.treesync.tree li
    )
:= by
  unfold processAddProposalAux'
  split
  · step_intro
    step_intro
    step
    step
    step
    step
    split
    rename_i treesync addIndex _
    have hinv := ‹_ ∧ TreesyncTreekemStateInvariant tr me st›.2
    have hkp := ‹Proposal.mf.wf (Bytes.Publishable · tr) _ ∧ _›.1
    simp only [Proposal.mf.wf_eq, Add.mf.wf_eq] at hkp
    have hpend := TreeSync.API.prepareAdd_valid _ _ _ ‹TreeSync.API.prepareAdd _ _ = _›
    have hadd := TreeSync.API.finalizeAdd_success _ _ _ _ ‹TreeSync.API.finalizeAdd _ _ = _›
    step by
      rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := keyPackageHasBeenVerifiedPred)]
      exact ⟨hpend.1.1, wf_invariant_of_publishable _ _ _ hkp, ⟨token, hpend.2 ▸ ‹_›⟩, ‹verifyWithLabel _ _ _ _ = true›⟩
    step by
      have := (‹TreesyncTreekemStateInvariant tr me st›).2.2.2.2.1
      rw [GroupContext.mf.wf_eq] at this
      have hkp := ‹(KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackage›
      simp only [KeyPackage.mf.wf_eq, KeyPackageTBS.mf.wf_eq] at hkp
      refine ⟨by grind [Bytes.Publishable], wf_invariant_of_publishable _ _ _ hkp.1.2.1, ⟨token, hpend.2 ▸ ‹_›⟩, ?_⟩
      have := hpend.1.2
      rcases hadd with ⟨h1, -⟩ | ⟨h1, h2, -⟩ <;> simp_all
    split
    rename_i treekem _ hadd'
    step
    subst x
    have hfin := ‹TreeSync.API.finalizeAdd addPend token = _›
    have hkp := ‹(KeyPackage.mf tkt).wf (Bytes.Publishable · tr) keyPackage›
    simp only [KeyPackage.mf.wf_eq, KeyPackageTBS.mf.wf_eq] at hkp
    obtain ⟨rfl, -⟩ := hadd'
    have hleaves := fun li => TreeSync.API.leafAtNat_finalizeAdd addPend token li treesync addIndex hfin
    have hinv := ‹TreesyncTreekemStateInvariant tr me st›
    have := hinv.leafIndex_lt tr me st
    obtain ⟨-, hmy⟩ := hinv.containsLeafIndex_iff tr me st st.leafIndex
    obtain ⟨hvalid, htk, hrel, hme, hgc, hwf, hasp, hverif, hpriv⟩ := hinv
    obtain ⟨myLn, hmyLn, hmyCred⟩ := hme.leafAtNat (by grind)
    have hne: st.leafIndex ≠ addIndex := by
      have := (hleaves 0).1
      grind
    refine ⟨rfl, rfl, TreeSync.API.treeAddOnlyRel_finalizeAdd addPend token treesync addIndex hfin hpend,
      ⟨?_, API.Tree.add_valid _ _ htk, ?_, ?_, hgc, ?_, ?_, ?_, ?_⟩, rfl, by unfold IHaveVerifiedKeyPackage; assumption, rfl, hne, (hleaves 0).1, fun li => (hleaves li).2⟩
    · exact TreeSync.API.finalizeAdd_treeValid addPend token treesync addIndex hfin hpend hvalid
    · exact (add_stateRel addPend token _ _ treesync addIndex hfin hrel rfl).1
    · exact IAmInTreeAt.of_leafAtNat ⟨myLn, by grind, hmyCred⟩
    · exact TreeSync.API.finalizeAdd_wf _ addPend token treesync addIndex hfin hwf hkp.1.2.1
    · exact TreeSync.API.finalizeAdd_valid addPend token treesync addIndex hfin hpend ‹_› hasp
    · exact IHaveVerifiedEveryLeafNode_finalizeAdd _ _ addPend token treesync addIndex hfin hverif ‹_›
    · exact MLS.TreeKEM.Symbolic.API.Tree.add_proof tr me _ _ hpriv
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

/-- Port of `_process_add_proposal_proof`. -/
@[instance]
public
theorem processAddProposal'.proof (me: Participant) (authServiceSid: Nat)
  (lSt: List (KeyPackage Bytes tkt × Nat) × TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HoareTriple
    (processAddProposal' me authServiceSid lSt proposal)
    (fun tr =>
      Proposal.mf.wf (Bytes.Publishable · tr) proposal ∧
      TreesyncTreekemStateInvariant tr me lSt.2 ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (lSt.1.map (·.1)) ∧
      JoinersAreInTree lSt.2.treesync lSt.1 ∧
      IAmNotAJoiner lSt.2.leafIndex (lSt.1.map (·.2))
    )
    (fun lStOut tr =>
      lStOut.2.treekem.keyscheduleState = lSt.2.treekem.keyscheduleState ∧
      lStOut.2.groupContext = lSt.2.groupContext ∧
      TreeSync.API.treeAddOnlyRel lSt.2.treesync.tree lStOut.2.treesync.tree ∧
      TreesyncTreekemStateInvariant tr me lStOut.2 ∧
      lStOut.1.map (·.1) = proposalsToKeyPackages [proposal] ++ lSt.1.map (·.1) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (lStOut.1.map (·.1)) ∧
      JoinersAreInTree lStOut.2.treesync lStOut.1 ∧
      IAmNotAJoiner lStOut.2.leafIndex (lStOut.1.map (·.2))
    )
:= by
  obtain ⟨joiners, st⟩ := lSt
  unfold processAddProposal'
  split
  rename_i hjst
  obtain ⟨rfl, rfl⟩ := hjst
  step by grind
  split
  rename_i keyPackage addIndex stOut _
  step
  subst x
  obtain ⟨hks, hgc, hrel, hinv, rfl, hkp, hli, hne, hnone, hleaves⟩ := ‹_ ∧ _›
  obtain ⟨-, hinvSt, hver, hjoin, hnot⟩ := ‹Proposal.mf.wf _ _ ∧ _›
  have hpos := hinvSt.position tr me st
  have hposOut := hinv.position tr me stOut
  refine ⟨hks, hgc, hrel, hinv, by simp [proposalsToKeyPackages], ?_, ?_, ?_⟩
  · intro kp hkp'
    simp only [List.map_cons, List.mem_cons] at hkp'
    rcases hkp' with rfl | hkp'
    · exact hkp
    · exact hver kp hkp'
  · exact JoinersAreInTree_cons _ _ joiners keyPackage addIndex hpos hposOut hjoin hnone hleaves
  · simp only [IAmNotAJoiner, List.map_cons, List.mem_cons, not_or] at *
    grind

/-- Port of `_process_update_proposal_proof`. -/
@[instance]
public
theorem processUpdateProposal'.proof (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st: TreeSyncTreeKEMState) (proposal: ProposalAndSender):
  HoareTriple
    (processUpdateProposal' me authServiceSid updateCacheSid st proposal)
    (fun tr =>
      ProposalAndSenderIsPublishable tr proposal ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun stOut tr =>
      stOut.treekem.keyscheduleState = st.treekem.keyscheduleState ∧
      stOut.groupContext = st.groupContext ∧
      TreesyncTreekemStateInvariant tr me stOut
    )
:= by
  unfold processUpdateProposal'
  split
  · rename_i leafNode _
    step
    step_intro
    step
    step
    step_intro
    have hpend := TreeSync.API.prepareUpdate_valid _ _ _ _ ‹TreeSync.API.prepareUpdate _ _ _ = _›
    step by
      have hinv := ‹_ ∧ TreesyncTreekemStateInvariant tr me st›.2
      have := hinv.2.2.2.2.1
      have hln := ‹ProposalAndSenderIsPublishable tr proposal ∧ _›.1
      simp only [ProposalAndSenderIsPublishable, Proposal.mf.wf_eq, Update.mf.wf_eq, ‹proposal.proposal = _›] at hln
      rw [GroupContext.mf.wf_eq] at this
      exact ⟨by grind [Bytes.Publishable], wf_invariant_of_publishable _ _ _ hln, ⟨token, hpend.2.2 ▸ ‹_›⟩, hpend.1.2.1⟩
    step
    step_intro
    have hleaves := fun li => TreeSync.API.leafAtNat_finalizeUpdate pendUpdate token li hpend.1.2.2.1
    split
    -- `senderIndex = st.leafIndex`
    step
    step
    step
    step
    -- `senderIndex ≠ st.leafIndex`
    rotate_left
    step
    step
    all_goals
      subst x treekem
      have hln := ‹ProposalAndSenderIsPublishable tr proposal ∧ _›.1
      simp only [ProposalAndSenderIsPublishable, Proposal.mf.wf_eq, Update.mf.wf_eq, ‹proposal.proposal = _›] at hln
      have hinv := ‹_ ∧ TreesyncTreekemStateInvariant tr me st›.2
      have := hinv.leafIndex_lt tr me st
      have hsender := hinv.containsLeafIndex_iff tr me st senderIndex
      have hmy := (hinv.containsLeafIndex_iff tr me st st.leafIndex).2
      obtain ⟨hvalid, htk, hrel, hme, hgc, hwf, hasp, hverif, hpriv⟩ := hinv
      refine ⟨rfl, rfl, TreeSync.API.finalizeUpdate_treeValid pendUpdate token hpend hvalid, ?_, ?_, ?_, hgc,
        TreeSync.API.finalizeUpdate_wf _ pendUpdate token hwf hln, TreeSync.API.finalizeUpdate_valid pendUpdate token hpend ‹_› hasp,
        IHaveVerifiedEveryLeafNode_finalizeUpdate _ _ pendUpdate token hpend.1.2.2.1 hverif ‹_›, ?_⟩
      · first
        | exact API.Tree.updateMyself_valid _ _ _ htk
        | exact API.Tree.updateOther_valid _ _ senderIndex (by grind) (by grind) htk
      · first
        | exact updateMyself_stateRel pendUpdate token _ _ _ (by grind) hrel rfl
        | exact updateOther_stateRel pendUpdate token _ _ senderIndex (by grind) (by grind) rfl hrel rfl
      · have := hme.leafAtNat (by grind)
        exact IAmInTreeAt.of_leafAtNat (by grind)
      · first
        | exact MLS.TreeKEM.Symbolic.API.Tree.updateMyself_proof tr me _ _ _ ‹_› hpriv
        | exact MLS.TreeKEM.Symbolic.API.Tree.updateOther_proof tr me _ _ senderIndex (by grind) (by grind) hpriv
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

public
instance (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HasGhostArgumentType (processRemoveProposal' st proposal) Participant
where
  dummy := ()

/--
Port of `_process_remove_proposal_proof`.
The principal `me` (not an argument of the function) is the ghost argument.
-/
@[instance]
public
theorem processRemoveProposal'.proof (me: Participant) (st: TreeSyncTreeKEMState) (proposal: Proposal Bytes):
  HoareTripleGhost
    (processRemoveProposal' st proposal)
    me
    (fun tr =>
      Proposal.mf.wf (Bytes.Publishable · tr) proposal ∧
      TreesyncTreekemStateInvariant tr me st
    )
    (fun stOut tr =>
      stOut.treekem.keyscheduleState = st.treekem.keyscheduleState ∧
      stOut.groupContext = st.groupContext ∧
      TreesyncTreekemStateInvariant tr me stOut
    )
:= by
  apply HoareTripleGhost.mk
  unfold processRemoveProposal'
  split
  · step_intro
    step
    step
    step
    step
    step_intro
    step_intro
    step
    subst x
    have hinv := ‹_ ∧ TreesyncTreekemStateInvariant tr me st›.2
    have hpend := TreeSync.API.prepareRemove_valid _ _ _ ‹TreeSync.API.prepareRemove _ _ = _›
    obtain ⟨hli, hli'⟩ := hinv.containsLeafIndex_iff tr me st removed
    obtain ⟨hmy, hmy'⟩ := hinv.containsLeafIndex_iff tr me st st.leafIndex
    have := hinv.leafIndex_lt tr me st
    obtain ⟨hvalid, htk, hrel, hme, hgc, hwf, hasp, hverif, hpriv⟩ := hinv
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hgc, ?_, ?_, ?_, ?_⟩
    · exact TreeSync.API.finalizeRemove_treeValid removePend hpend hvalid
    · exact API.Tree.remove_valid _ _ (by grind) (by grind) htk
    · exact remove_stateRel removePend _ _ (by grind) (by grind) rfl hrel htk
    · have := hme.leafAtNat (by grind)
      have := TreeSync.API.leafAtNat_finalizeRemove removePend st.leafIndex hpend.1
      exact IAmInTreeAt.of_leafAtNat (by grind)
    · exact TreeSync.API.finalizeRemove_wf _ removePend hwf
    · exact TreeSync.API.finalizeRemove_valid removePend hpend hasp
    · exact IHaveVerifiedEveryLeafNode_finalizeRemove _ _ removePend hpend.1 hverif
    · exact MLS.TreeKEM.Symbolic.API.Tree.remove_proof tr me _ _ (by grind) (by grind) hpriv
  · intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

/-- The ghost of the fold over the group context extensions in `_process_proposals_proof`. -/
abbrev processGroupContextExtensionsLoop (me: Participant) (st0: TreeSyncTreeKEMState) (l: List (Proposal Bytes)):
  FoldlMInvariantAndProof l processGroupContextExtensionsProposal'
where
  inv := ProcessProposalsLoopInv me st0
  step pref cur suff h acc := by
    step with ⟨ me ⟩ by
      simp only [ProcessProposalsLoopInv, ProposalsArePublishable, ProcessProposalsAccInv] at *
      grind
    simp only [ProcessProposalsLoopInv, ProposalsArePublishable, ProcessProposalsAccInv] at *
    grind

/-- The ghost of the fold over the update proposals in `_process_proposals_proof`. -/
abbrev processUpdateProposalsLoop (me: Participant) (authServiceSid updateCacheSid: Nat) (st0: TreeSyncTreeKEMState)
  (l: List ProposalAndSender):
  FoldlMInvariantAndProof l (processUpdateProposal' me authServiceSid updateCacheSid)
where
  inv := ProcessUpdateProposalsLoopInv me st0
  step pref cur suff h acc := by
    step by
      simp only [ProcessUpdateProposalsLoopInv, ProposalAndSendersArePublishable, ProcessProposalsAccInv] at *
      grind
    simp only [ProcessUpdateProposalsLoopInv, ProposalAndSendersArePublishable, ProcessProposalsAccInv] at *
    grind

/-- The ghost of the fold over the remove proposals in `_process_proposals_proof`. -/
abbrev processRemoveProposalsLoop (me: Participant) (st0: TreeSyncTreeKEMState) (l: List (Proposal Bytes)):
  FoldlMInvariantAndProof l processRemoveProposal'
where
  inv := ProcessProposalsLoopInv me st0
  step pref cur suff h acc := by
    step with ⟨ me ⟩ by
      simp only [ProcessProposalsLoopInv, ProposalsArePublishable, ProcessProposalsAccInv] at *
      grind
    simp only [ProcessProposalsLoopInv, ProposalsArePublishable, ProcessProposalsAccInv] at *
    grind

/-- The ghost of the fold over the add proposals in `_process_proposals_proof` (MLS*'s `add_acc_inv`). -/
abbrev processAddProposalsLoop (me: Participant) (authServiceSid: Nat) (st0: TreeSyncTreeKEMState) (adds: List (Proposal Bytes)):
  FoldlMInvariantAndProof adds (processAddProposal' me authServiceSid)
where
  inv := ProcessAddProposalsLoopInv me st0
  step pref cur suff h lSt := by
    step by
      simp only [ProcessAddProposalsLoopInv, ProposalsArePublishable, ProcessAddProposalsAccInv] at *
      grind
    have := proposalsToKeyPackages_cons cur suff
    have := proposalsToKeyPackages_singleton_reverse cur
    simp only [ProcessAddProposalsLoopInv, ProposalsArePublishable, ProcessAddProposalsAccInv] at *
    grind [TreeSync.API.treeAddOnlyRel_transitive]

/-- Port of `_process_proposals_proof`. -/
@[instance]
public
theorem processProposals'.proof (me: Participant) (authServiceSid updateCacheSid: Nat)
  (st0: TreeSyncTreeKEMState) (proposals: List ProposalAndSender):
  HoareTriple
    (processProposals' me authServiceSid updateCacheSid st0 proposals)
    (fun tr =>
      (∀ p ∈ proposals.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p) ∧
      TreesyncTreekemStateInvariant tr me st0
    )
    (fun (newSt, joiners, pskIds, _otherProposals, canAddOnly) tr =>
      TreesyncTreekemStateInvariant tr me newSt ∧
      proposalsToKeyPackages (proposals.map (·.proposal)) = joiners.map (·.1) ∧
      IHaveVerifiedEveryKeyPackage tr.erase me (joiners.map (·.1)) ∧
      newSt.treekem.keyscheduleState = st0.treekem.keyscheduleState ∧
      JoinersAreInTree newSt.treesync joiners ∧
      IAmNotAJoiner newSt.leafIndex (joiners.map (·.2)) ∧
      PskIdsGood tr pskIds ∧
      newSt.groupContext = { st0.groupContext with extensions := newSt.groupContext.extensions } ∧
      (canAddOnly → TreeSync.API.treeAddOnlyRel st0.treesync.tree newSt.treesync.tree)
    )
:= by
  unfold processProposals'
  apply HoareTriple.mk
  intro tr ⟨hpre, hinvSt⟩ hinv
  step_intro
  obtain ⟨hkps, hgceP, haddP, hupdP, hremP, hpsk, -⟩ := sortProposals'_proof tr proposals hpre
  -- an add-only commit does not process the other proposals
  by_cases hc: sortedProposals.groupContextExtensions = [] ∧ sortedProposals.updates = [] ∧ sortedProposals.removes = []
  -- the folds over empty lists
  obtain ⟨hc1, hc2, hc3⟩ := hc
  simp -iota -proj -zeta only [hc1, hc2, hc3, List.foldlM_nil]
  step
  step
  step
  subst_vars
  have: ProcessProposalsLoopInv me st ((⟨sortedProposals.removes, [], by simp⟩: sortedProposals.removes.Cursor), st) tr :=
    ⟨by simp [ProposalsArePublishable], ‹_›, rfl, rfl⟩
  rotate_left
  step with ⟨ processGroupContextExtensionsLoop me st0 sortedProposals.groupContextExtensions ⟩ by
    exact ⟨‹ProposalsArePublishable tr sortedProposals.groupContextExtensions›, ⟨‹_›, rfl, rfl⟩⟩
  step with ⟨ processUpdateProposalsLoop me authServiceSid updateCacheSid st0 sortedProposals.updates ⟩ by
    exact ⟨‹ProposalAndSendersArePublishable tr sortedProposals.updates›, ‹ProcessProposalsLoopInv _ _ _ tr›.2⟩
  step with ⟨ processRemoveProposalsLoop me st0 sortedProposals.removes ⟩ by
    exact ⟨‹ProposalsArePublishable tr sortedProposals.removes›, ‹ProcessUpdateProposalsLoopInv _ _ _ tr›.2⟩
  -- the add proposals
  all_goals
    have hst: ProcessProposalsLoopInv _ _
      ((⟨sortedProposals.removes, [], by simp⟩: sortedProposals.removes.Cursor), st) tr := ‹_›
    step with ⟨ processAddProposalsLoop me authServiceSid st sortedProposals.adds ⟩ by
      refine ⟨‹ProposalsArePublishable tr sortedProposals.adds›, hst.2.1, rfl, rfl, ?_, by simp, ?_, by simp [IAmNotAJoiner],
        TreeSync.API.treeAddOnlyRel_reflexive _⟩
      · simp [IHaveVerifiedEveryKeyPackage]
      · simp [JoinersAreInTree]
    step
    subst x
    obtain ⟨-, hinvOut, hks, hgc, hver, hkps', hjoin, hnot, hrel⟩ := ‹ProcessAddProposalsLoopInv _ _ _ tr›
    obtain ⟨-, -, hks3, hgc3⟩ := ‹ProcessProposalsLoopInv _ _ (_, st) tr›
    simp only [proposalsToKeyPackages, List.append_nil] at hkps'
    refine ⟨hinvOut, by rw [hkps, hkps', List.map_reverse], ?_, by rw [hks, hks3], ?_, ?_, ‹PskIdsGood tr _›,
      by rw [hgc, hgc3], ?_⟩
    · simpa [IHaveVerifiedEveryKeyPackage] using hver
    · simpa [JoinersAreInTree] using hjoin
    · simpa [IAmNotAJoiner] using hnot
    · first
      | exact fun _ => hrel
      | grind

/-- Port of `_make_provisional_group_context_proof`. -/
@[instance]
public
theorem makeProvisionalGroupContext'.proof {groupId: MlsBytes Bytes}
  (groupContext: GroupContext Bytes) (treesync: TreeSyncState Bytes tkt DyAsToken groupId):
  HoareTriple
    (makeProvisionalGroupContext' groupContext treesync)
    (fun tr =>
      GroupContext.mf.wf (Bytes.Publishable · tr) groupContext ∧
      (TreeSync.mf tkt treesync.levels).wf (Bytes.Publishable · tr) treesync.tree
    )
    (fun provisionalGroupContext tr =>
      GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext.val ∧
      TreeHasHash treesync.tree provisionalGroupContext.val.treeHash.val ∧
      provisionalGroupContext.val.groupId = groupContext.groupId ∧
      provisionalGroupContext.val.epoch = groupContext.epoch + 1
    )
:= by
  unfold makeProvisionalGroupContext'
  step
  obtain ⟨hgc, hts⟩ := ‹_ ∧ _›
  simp only [Result.bind_eq_success] at *
  obtain ⟨th, hth, th', hth', hres⟩ := ‹∃ _, _›
  split at hres
  · simp only [Result.pure_eq_success] at hres
    have := (mkMlsBytes_eq_success _ _ _ _).1 hth'
    have hth: TreeHasHash treesync.tree th := hth
    have := pred_treeHash _ _ _ hth (preIsHashCompatible_publishable tr) hts
    simp only [GroupContext.mf.wf_eq] at *
    grind
  · simp [Result.error] at hres

/-! ## Process the update path -/

variable [HasIAmInGroupInvariant] [HasBootstrapCryptoInvariants] [HasMlsTreekemInvariants] [HasMlsPskInvariants]

/--
Port of `_process_update_path_proof`.
MLS*'s `treesync_treekem_state_invariant_aux` with the provisional group context (which has the same group identifier)
is stated with the current group context, together with the well-formedness of the provisional one
(the TreeSync state is indexed by the current group identifier).
MLS*'s `Some? pending_treekem.opt_commit_secret` and the facts on its value are an `∃`.
-/
@[instance]
public
theorem processUpdatePath'.proof (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (senderIndex: Nat) (path: TreeKEM.UpdatePath Bytes)
  (joiners: List (KeyPackage Bytes tkt × Nat)):
  HoareTriple
    (processUpdatePath' me authServiceSid st senderIndex path joiners)
    (fun tr =>
      TreesyncTreekemStateInvariant tr me st ∧
      TreeKEM.UpdatePath.mf.wf (Bytes.Publishable · tr) path
    )
    (fun (newTreesync, pendingTreekem, provisionalGroupContext) tr =>
      provisionalGroupContext.groupId = st.groupContext.groupId ∧
      provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext ∧
      TreesyncTreekemStateInvariantAux tr me st.groupContext newTreesync pendingTreekem.nextTreeState ∧
      TreeHasHash newTreesync.tree provisionalGroupContext.treeHash.val ∧
      ∃ commitSecret, pendingTreekem.optCommitSecret = some commitSecret ∧
        commitSecret.Invariant tr ∧
        (nodeSkLabel newTreesync.tree st.groupContext.groupId).canFlow (commitSecret.label tr) tr.erase
    )
:= by
  unfold processUpdatePath'
  step
  step
  step
  step_intro
  step
  step
  step
  obtain ⟨hinv, hwfPath⟩ := ‹TreesyncTreekemStateInvariant tr me st ∧ _›
  have hwfU := uncompressUpdatePath_wf (Bytes.Publishable · tr) senderIndex st.treesync.tree path uncompressedPath
    hwfPath ‹_›
  have hwfTs := updatePathToTreesync_wf _ _ hwfU
  have htsPend := TreeSync.API.prepareCommit_valid _ _ _ _ ‹API.prepareCommit _ _ _ = _›
  step by
    have := hinv.2.2.2.2.1
    rw [GroupContext.mf.wf_eq] at this
    refine ⟨by grind [Bytes.Publishable], wf_invariant_of_publishable _ _ _ (MLS.getPathLeaf_wf _ _ _ _ hwfTs),
      ⟨token, htsPend.2.2 ▸ ‹_›⟩, ?_⟩
    have := htsPend.1.1
    simp only [pathIsValid, pathLeafIsValid, Bool.and_eq_true] at this
    exact this.1.1.1
  step by
    have hinv := ‹TreesyncTreekemStateInvariant tr me st›
    refine ⟨hinv.2.2.2.2.1, ?_⟩
    exact TreeSync.API.finalizeCommit_wf _ _ _ _ ‹API.finalizeCommit _ _ = _› (preIsHashCompatible_publishable tr) hinv.2.2.2.2.2.1
      ‹(PathSync.mf _ _).wf _ treesyncPath›
  step_intro
  split
  rotate_left
  · simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i hl
  step_intro
  step
  step
  step
  subst x
  have hinv := ‹TreesyncTreekemStateInvariant tr me st›
  have hcl := TreesyncTreekemStateInvariant.containsLeafIndex_iff tr me st hinv
  obtain ⟨hvalid, htk, hrel, hme, hgc, hwf, hasp, hverif, hpriv⟩ := hinv
  have hpend := ‹API.prepareProcessFullCommit _ _ = _›
  simp only [API.prepareProcessFullCommit, Result.bind_eq_success, Result.pure_eq_success] at hpend
  obtain ⟨⟨nextTreeState, commitSecret⟩, hTk, rfl⟩ := hpend
  have hTs := ‹API.finalizeCommit commitPend token = .success treesync›
  have hU := ‹uncompressUpdatePath senderIndex st.treesync.tree path = _›
  have hwfU := ‹(Path.mf _ _ _).wf (Bytes.Publishable · tr) uncompressedPath›
  have hwfTs := ‹(Path.mf _ _ _).wf (Bytes.Publishable · tr) (updatePathToTreesync uncompressedPath)›
  have hne := ‹¬senderIndex = st.leafIndex›
  have hsender := ‹senderIndex < 2 ^ st.treesync.levels›
  have hfilterU := pathFilteringOk_uncompressUpdatePath _ _ _ _ hU
  have hfilterTs: pathFilteringOk st.treesync.tree senderIndex treesyncPath :=
    pathFilteringOk_updatePathToTreesync _ _ _ hfilterU
  have hheq: HEq treekemPath (updatePathToTreekem uncompressedPath) := by
    first | exact eqRec_heq _ _ | exact cast_heq _ _
  have hfilterTk: pathFilteringOk st.treekem.treeState.tree senderIndex treekemPath :=
    pathFilteringOk_of_treesyncTreekemStateRel _ _ hrel _ _ _ hheq (pathFilteringOk_updatePathToTreekem _ _ _ hfilterU)
  have hp: pathsyncPathkemRel treesyncPath treekemPath :=
    Path.heq_transport _ _ hl.symm hheq (fun _ pk => pathsyncPathkemRel treesyncPath pk)
      (pathsyncPathkemRel_updatePathToTreeX _)
  have hpk: PathkemGoodWeak treekemPath tr :=
    Path.heq_transport _ _ hl.symm hheq (fun n pk => (PathKEM.mf n).wf (Bytes.Invariant · tr) pk)
      (updatePathToTreekem_wf _ _ (wf_invariant_of_publishable _ _ _ hwfU))
  have hliTk := (hcl senderIndex).1.2 hsender
  have hliTs := (hcl senderIndex).2.2 hsender
  have hverifNew := IHaveVerifiedEveryLeafNode_finalizeCommit _ _ commitPend token treesync hTs hliTs hverif
    ‹IHaveVerifiedLeafNode _ _ _ _ _›
  have hwfNew := TreeSync.API.finalizeCommit_wf _ _ _ _ hTs (preIsHashCompatible_publishable tr) hwf hwfTs
  have haspNew := TreeSync.API.finalizeCommit_valid _ _ _ hTs htsPend ‹(dyAsp tr).credentialOk _ token› hasp
  have hgcProv := ‹GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext.val›
  have hgid := hgc
  rw [GroupContext.mf.wf_eq] at hgid
  obtain ⟨hpriv', hcsInv, hcsLabel⟩ := MLS.TreeKEM.Symbolic.API.Tree.processCommit_proof tr me st.treesync
    st.treekem.treeState senderIndex treesyncPath treekemPath (joiners.map (·.2)) provisionalGroupContext.val commitPend
    token treesync nextTreeState commitSecret hTs hTk hliTk hne hfilterTs ‹_› hrel hp htk hvalid htsPend hpriv
    ⟨haspNew, hverifNew, wf_invariant_of_publishable _ _ _ hwfNew⟩ hpk (wf_invariant_of_publishable _ _ _ hgcProv)
    (by grind [Bytes.Publishable]) ‹_›
  refine ⟨‹provisionalGroupContext.val.groupId = _›, ‹provisionalGroupContext.val.epoch = _›, hgcProv,
    ⟨TreeSync.API.finalizeCommit_treeValid _ _ _ hTs htsPend hvalid,
      API.Tree.commit_valid _ _ _ _ _ _ _ hTk hliTk hne hfilterTk ‹_› htk,
      processCommit_stateRel commitPend token _ _ _ _ _ _ _ _ hTs hTk hliTk hne hfilterTk ‹_› rfl hrel hp, ?_, hgc,
      hwfNew, haspNew, hverifNew, hpriv'⟩,
    ‹TreeHasHash treesync.tree _›, ⟨commitSecret, rfl, hcsInv, hcsLabel⟩⟩
  apply IAmInTreeAt.of_leafAtNat
  rw [TreeSync.API.leafAtNat_finalizeCommit commitPend token _ treesync hTs hliTs, ite_eq_right hne]
  exact IAmInTreeAt.leafAtNat hme ((hcl st.leafIndex).2.2 (TreesyncTreekemStateInvariant.leafIndex_lt tr me st
    ‹TreesyncTreekemStateInvariant tr me st›))

public
instance (st: TreeSyncTreeKEMState): HasGhostArgumentType (processNoUpdatePath' st) Participant where
  dummy := ()

/--
Port of `_process_no_update_path_proof`.
The principal `me` (not an argument of the function) is the ghost argument.
As for `processUpdatePath'.proof`, the invariant is stated with the current group context.
MLS*'s `new_treesync == st.treesync` is only used through `tree_add_only_rel`, which is stated instead.
-/
@[instance]
public
theorem processNoUpdatePath'.proof (me: Participant) (st: TreeSyncTreeKEMState):
  HoareTripleGhost
    (processNoUpdatePath' st)
    me
    (fun tr => TreesyncTreekemStateInvariant tr me st)
    (fun (newTreesync, pendingTreekem, provisionalGroupContext) tr =>
      provisionalGroupContext.groupId = st.groupContext.groupId ∧
      provisionalGroupContext.epoch = st.groupContext.epoch + 1 ∧
      GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext ∧
      TreesyncTreekemStateInvariantAux tr me st.groupContext newTreesync pendingTreekem.nextTreeState ∧
      TreeHasHash newTreesync.tree provisionalGroupContext.treeHash.val ∧
      pendingTreekem.optCommitSecret = none ∧
      TreeSync.API.treeAddOnlyRel st.treesync.tree newTreesync.tree
    )
:= by
  apply HoareTripleGhost.mk
  unfold processNoUpdatePath'
  step by
    have hinv := ‹TreesyncTreekemStateInvariant tr me st›
    exact ⟨hinv.2.2.2.2.1, hinv.2.2.2.2.2.1⟩
  step
  step
  subst x
  have hpend := ‹API.prepareProcessAddOnlyCommit st.treekem = _›
  simp only [API.prepareProcessAddOnlyCommit, Result.pure_eq_success] at hpend
  subst hpend
  exact ⟨‹_›, ‹_›, ‹_›, ‹TreesyncTreekemStateInvariant tr me st›, ‹_›, rfl, TreeSync.API.treeAddOnlyRel_reflexive _⟩

/-- The end of `_process_opt_update_path_proof`: the key schedule of the new state, from the pending commit. -/
theorem processOptUpdatePath'_finalize (tr: ProofTrace) (me: Participant) (st: TreeSyncTreeKEMState) (isFullCommit: Bool)
  (newTreesync: TreeSyncState Bytes tkt DyAsToken st.groupContext.groupId) (pendingTreekem: API.PendingProcessCommit st.treekem)
  (provisionalGroupContext: GroupContext Bytes) (newConfirmedTranscriptHash: MlsBytes Bytes)
  (joiners: List (KeyPackage Bytes tkt × Nat)) (psks: List (PreSharedKeyId Bytes × Bytes))
  (res: TreeKEMState Bytes st.leafIndex × Bytes)
  (hfin: API.finalizeProcessCommit pendingTreekem psks
    { provisionalGroupContext with groupId := st.groupContext.groupId, confirmedTranscriptHash := newConfirmedTranscriptHash } =
    .success res)
  (hgc: GroupContext.mf.wf (Bytes.Publishable · tr) provisionalGroupContext)
  (hAux: TreesyncTreekemStateInvariantAux tr me st.groupContext newTreesync pendingTreekem.nextTreeState)
  (hth: TreeHasHash newTreesync.tree provisionalGroupContext.treeHash.val)
  (hcs: ∀ commitSecret ∈ pendingTreekem.optCommitSecret, commitSecret.Invariant tr)
  (hlabel: (computeExpectedCommitSecretLabel isFullCommit newTreesync.tree st.groupContext.groupId).canFlow
    (computeCommitSecretLabel tr pendingTreekem.optCommitSecret) tr.erase)
  (hinit: st.treekem.keyscheduleState.initSecret.Invariant tr)
  (hcth: newConfirmedTranscriptHash.val.Publishable tr)
  (hjoiners: TxHashContainsJoiners newConfirmedTranscriptHash.val (joiners.map (·.1)))
  (hpsks: PsksBytesInvariant tr psks):
  let newSt: TreeSyncTreeKEMState := {
    leafIndex := st.leafIndex
    groupContext := { provisionalGroupContext with
      groupId := st.groupContext.groupId, confirmedTranscriptHash := newConfirmedTranscriptHash }
    mySignatureKeySid := st.mySignatureKeySid
    treesync := newTreesync
    treekem := res.1
  }
  TreesyncTreekemStateInvariant tr me newSt ∧
  TreesyncTreekemStateCoarseInvariant tr me newSt ∧
  TreekemKeyscheduleStateLabelGood tr st.treekem.keyscheduleState.initSecret
    (computeExpectedCommitSecretLabel isFullCommit newSt.treesync.tree newSt.groupContext.groupId)
    (joiners.map (·.1)) psks newSt.treekem.keyscheduleState newSt.groupContext
:= by
  intro newSt
  simp only [API.finalizeProcessCommit, Result.bind_eq_success, Result.pure_eq_success] at hfin
  obtain ⟨⟨ks, encSecret, welcomeSecrets⟩, hks, rfl⟩ := hfin
  have hgcNew: GroupContext.mf.wf (Bytes.Publishable · tr) newSt.groupContext := by
    have := hAux.2.2.2.2.1
    rw [GroupContext.mf.wf_eq] at hgc this ⊢
    exact ⟨this.1, hgc.2.1, hcth, hgc.2.2.2⟩
  obtain ⟨hksGood, hksLabel, -, hksAuthEx, -⟩ := commit_proof tr st.treekem.keyscheduleState
    pendingTreekem.optCommitSecret psks newSt.groupContext (joiners.map (·.1)) ks encSecret welcomeSecrets hks hjoiners
    hinit hcs hpsks hgcNew
  exact ⟨TreesyncTreekemStateInvariantAux_changeGroupContext tr me st.groupContext newSt.groupContext rfl newTreesync _
      hAux hgcNew,
    ⟨hksGood, hksAuthEx.weak, hth⟩, TreekemKeyscheduleStateLabelGood_canFlow _ _ _ _ _ _ _ _ hksLabel hlabel⟩

/--
Port of `_process_opt_update_path_proof` (and `_process_opt_update_path_proof_aux`).
MLS*'s `opt_path == None ==> new_st.treesync == st.treesync` is only used through `tree_add_only_rel`,
which is stated instead.
-/
@[instance]
public
theorem processOptUpdatePath'.proof (me: Participant) (authServiceSid: Nat)
  (st: TreeSyncTreeKEMState) (senderIndex: Nat) (optPath: Option (TreeKEM.UpdatePath Bytes))
  (joiners: List (KeyPackage Bytes tkt × Nat)) (newConfirmedTranscriptHash: MlsBytes Bytes)
  (psks: List (PreSharedKeyId Bytes × Bytes)):
  HoareTriple
    (processOptUpdatePath' me authServiceSid st senderIndex optPath joiners newConfirmedTranscriptHash psks)
    (fun tr =>
      (MlsOption.mf TreeKEM.UpdatePath.mf).wf (Bytes.Publishable · tr) optPath ∧
      st.treekem.keyscheduleState.initSecret.Invariant tr ∧
      newConfirmedTranscriptHash.val.Publishable tr ∧
      TxHashContainsJoiners newConfirmedTranscriptHash.val (joiners.map (·.1)) ∧
      TreesyncTreekemStateInvariant tr me st ∧
      PsksBytesInvariant tr psks
    )
    (fun newSt tr =>
      newSt.groupContext.groupId = st.groupContext.groupId ∧
      newSt.groupContext.epoch = st.groupContext.epoch + 1 ∧
      TreesyncTreekemStateInvariant tr me newSt ∧
      TreesyncTreekemStateCoarseInvariant tr me newSt ∧
      TreekemKeyscheduleStateLabelGood tr st.treekem.keyscheduleState.initSecret
        (computeExpectedCommitSecretLabel optPath.isSome newSt.treesync.tree newSt.groupContext.groupId)
        (joiners.map (·.1)) psks newSt.treekem.keyscheduleState newSt.groupContext ∧
      (optPath = none → TreeSync.API.treeAddOnlyRel st.treesync.tree newSt.treesync.tree)
    )
:= by
  unfold processOptUpdatePath'
  dsimp -proj -iota only
  split
  · step by
      have hpre := ‹(MlsOption.mf _).wf _ _ ∧ _›
      refine ⟨hpre.2.2.2.2.1, ?_⟩
      simpa [MlsOption.mf.wf_eq] using hpre.1
    split
    rename_i newTreesync pendingTreekem provisionalGroupContext _
    step
    step
    subst x
    obtain ⟨-, hinit, hcth, hjoiners, -, hpsks⟩ := ‹(MlsOption.mf _).wf _ _ ∧ _›
    obtain ⟨-, hepoch, hgc, hAux, hth, cs, hcs, hcsInv, hcsLabel⟩ := ‹provisionalGroupContext.groupId = _ ∧ _›
    obtain ⟨hinvNew, hcoarse, hlabel⟩ := processOptUpdatePath'_finalize tr me st true newTreesync pendingTreekem
      provisionalGroupContext newConfirmedTranscriptHash joiners psks _ ‹API.finalizeProcessCommit _ _ _ = _› hgc hAux hth
      (by simpa [hcs] using hcsInv) (by simpa [hcs, computeExpectedCommitSecretLabel, computeCommitSecretLabel] using hcsLabel)
      hinit hcth hjoiners hpsks
    exact ⟨rfl, hepoch, hinvNew, hcoarse, hlabel, by simp⟩
  · step with ⟨ me ⟩ by
      obtain ⟨-, -, -, -, hinv, -⟩ := ‹(MlsOption.mf _).wf _ _ ∧ _›
      exact hinv
    split
    rename_i newTreesync pendingTreekem provisionalGroupContext _
    step
    step
    subst x
    obtain ⟨-, hinit, hcth, hjoiners, -, hpsks⟩ := ‹(MlsOption.mf _).wf _ _ ∧ _›
    obtain ⟨-, hepoch, hgc, hAux, hth, hcs, hadd⟩ := ‹provisionalGroupContext.groupId = _ ∧ _›
    obtain ⟨hinvNew, hcoarse, hlabel⟩ := processOptUpdatePath'_finalize tr me st false newTreesync pendingTreekem
      provisionalGroupContext newConfirmedTranscriptHash joiners psks _ ‹API.finalizeProcessCommit _ _ _ = _› hgc hAux hth
      (by simp [hcs]) (by simp [hcs, computeExpectedCommitSecretLabel, computeCommitSecretLabel, Label.canFlow])
      hinit hcth hjoiners hpsks
    exact ⟨rfl, hepoch, hinvNew, hcoarse, hlabel, fun _ => hadd⟩

/-! ## Process commit -/

/-- Port of `_process_commit_proof`. -/
@[instance]
public
theorem processCommit'.proof (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (st0: TreeSyncTreeKEMState) (txHashInput: ConfirmedTranscriptHashInput Bytes):
  HoareTriple (processCommit' me authServiceSid proposalCacheSid updateCacheSid pskStoreSid st0 txHashInput)
    (fun tr => ConfirmedTranscriptHashInput.mf.wf (Bytes.Publishable · tr) txHashInput ∧ TreesyncTreekemStateAllInvariants tr me st0)
    (fun (newSt, _pskStoreSid) tr => TreesyncTreekemStateAllInvariants tr me newSt)
:= by
  unfold processCommit'
  step_intro
  step_intro
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr
  rename_i commit hcontent
  dsimp -proj -iota only
  split
  rotate_left
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_bind, Traceful.run_failure]
    exists tr
  step
  step
  step by
    exact ((Commit.mf.wf_eq _ _).mp (commit_wf_of_txHashInput _ _ _ hcontent ‹_ ∧ _›.1)).1
  replace hprop: ProposalsArePublishable tr (proposals.map (·.proposal)) := ‹∀ p ∈ proposals.map (·.proposal), _›
  step by
    exact ⟨hprop, ‹_ ∧ TreesyncTreekemStateAllInvariants tr me st0›.2.1⟩
  split
  rename_i st joiners pskIds _ canAddOnly hpost
  obtain ⟨hinv, hjoiners, hverif, hks, hjoin, hnot, hpskIds, hgc, hadd⟩ := hpost
  -- the confirmed transcript hash
  obtain ⟨hwf, hinv0⟩ := ‹ConfirmedTranscriptHashInput.mf.wf _ txHashInput ∧ _›
  obtain ⟨htx, hcthPub⟩ := computeConfirmedTranscriptHash'_txHashContainsJoiners tr me st0 txHashInput commit
    newConfirmedTranscriptHash _ ‹_› hcontent ‹_› hwf hinv0
  rw [hjoiners] at htx
  have hinit0 := hinv0.2.1.1.2.2.2.2.2.2.1.1
  have hprev0 := hinv0.2.2
  step
  step
  step by
    rw [‹st.treekem.keyscheduleState = _›]
    exact ⟨((Commit.mf.wf_eq _ _).mp (commit_wf_of_txHashInput _ _ _ hcontent ‹_›)).2,
      ‹st0.treekem.keyscheduleState.initSecret.Invariant tr›,
      ‹_›, ‹_›, ‹_›, ‹_›⟩
  rename_i _ _ _ hcoarse hlabel _
  -- `step` monotonizes `hlabel` with the facts before it
  have hgoodSt := hcoarse.1
  have hlabel' := hlabel
  rw [hks] at hlabel'
  clear hlabel
  step by
    have hinvSt := ‹TreesyncTreekemStateInvariant tr me st›
    exact rememberPsk_resumptionPsk_pre tr me _ _ _ _ hinvSt.2.2.2.2.1 hcoarse.2.2 hinvSt.2.2.2.1
      hcoarse.1.2.2.2.2.1.1 ‹TreekemKeyscheduleStateLabelGood tr _ _ _ _ _ _›.2.2.2.2.2.2.2
  step by
    rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := iAmInGroupPred)]
    have hinvSt := ‹TreesyncTreekemStateInvariant tr me st›
    have hcoarse := ‹TreesyncTreekemStateCoarseInvariant tr me st›
    have hgid := ‹st.groupContext.groupId = _›
    have hepoch := ‹st.groupContext.epoch = _›
    rw [hgc] at hgid hepoch
    refine ⟨hcoarse.2.2, hinvSt.2.2.2.2.2.2.2.1, ‹st0.treekem.keyscheduleState.initSecret.Invariant tr›, hgid.symm, hepoch.symm, ?_, ‹PsksBytesInvariant tr psks›,
      ‹IHaveVerifiedEveryKeyPackage _ _ _›, ‹IHavePreviousEpochEvent _ _ _ _ _›, hcoarse.1, ?_⟩
    · intro hty
      have hnone: commit.path = none := by
        revert hty
        cases commit.path <;> simp
      have hcan: canAddOnly = true := by
        have := ‹(canAddOnly || commit.path.isSome) = true›
        simpa [hnone] using this
      exact TreeSync.API.treeAddOnlyRel_transitive _ _ _ (hadd hcan) (‹commit.path = none → _› hnone)
    · revert ‹TreekemKeyscheduleStateLabelGood tr _ _ _ _ _ _›
      cases commit.path.isSome <;> exact id
  step
  subst x
  exact ⟨‹TreesyncTreekemStateInvariant tr me st›, ‹TreesyncTreekemStateCoarseInvariant tr me st›,
    ⟨_, rfl, ‹Trace.EventLogged (_: IAmInGroup) tr.erase›, rfl, rfl, rfl⟩⟩

/-- Port of `process_commit_proof`. -/
@[instance]
public
theorem processCommit.proof (me: Participant) (authServiceSid proposalCacheSid updateCacheSid pskStoreSid: Nat)
  (groupStateSid: Nat) (commitTs: Nat):
  HoareTriple
    (processCommit me authServiceSid proposalCacheSid updateCacheSid pskStoreSid groupStateSid commitTs)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold processCommit
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
  step
  step
  trivial

end Proofs

end MLS.TreeKEM
