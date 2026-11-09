module

public import MLS.TreeKEM.SymbolicSpec.SanityChecks
public import MLS.TreeKEM.SymbolicSpec.Reachability
public import MLS.Symbolic.SymbolicProofs.Reachability
import MLS.Common.Proofs.Crypto.Derived
import MLS.Common.SymbolicProofs.Crypto.Derived.RefHash
import all MLS.TreeKEM.SymbolicSpec.SanityChecks
import all MLS.TreeKEM.SymbolicSpec.State.API
import all MLS.TreeKEM.SymbolicSpec.State.EpochSecrets
import all MLS.TreeKEM.SymbolicSpec.State.NodeKey

/-!
The honest runs of the sanity checks (`MLS.TreeKEM.SanityChecks.scenario` and `fullScenario`) produce reachable traces
(not in MLS*), for the reachability configuration `MLS.TreeKEM.reachability`:
the run only consists of actions of this configuration, of messages sent by the attacker
(which it knows, as they are built from messages it received), and of reads of the states (`Traceful.ReadOnly`),
which do not change the trace.

As in DyLean's examples, each action is handled by `Traceful.PreservesReachabilityFrom_bind`
(here through the `reach` tactic), with a reachability lemma of the action.
-/

namespace MLS.TreeKEM.SanityChecks

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM MLS.Bootstrap

/-- `grind` chains the inequalities of traces. -/
instance {α: Type}: Std.IsPreorder (Trace α) where
  le_refl := Trace.le_refl
  le_trans := Trace.le_trans

/--
`reach h using hpre as x`: the first action of the program preserves reachability by `h`,
its precondition holds by `hpre` (`trivial` by default), and its result is introduced as `x`.
-/
local syntax "reach " term (" using " term)? (" as " rcasesPat)? : tactic

local macro_rules
  | `(tactic| reach $h $[using $hpre]? $[as $x]?) => do
    let hpre ← match hpre with
      | some hpre => pure hpre
      | none => `(term| trivial)
    let x ← match x with
      | some x => pure x
      | none => `(rcasesPat| _)
    `(tactic| (refine Traceful.PreservesReachabilityFrom_bind _ _ _ _ _ _ _ $h ‹_› $hpre ?_; rintro $x _ _ _ _))

/-- The program ends with `pure x`, whose postcondition holds by `hpost` (`trivial` by default). -/
local syntax "reach_pure" (" using " term)? : tactic

local macro_rules
  | `(tactic| reach_pure $[using $hpost]?) => do
    let hpost ← match hpost with
      | some hpost => pure hpost
      | none => `(term| trivial)
    `(tactic| refine Traceful.PreservesReachabilityFrom_pure _ _ _ _ ‹_› $hpost)

/-- The program ends with `failure`. -/
local macro "reach_failure" : tactic =>
  `(tactic| exact Traceful.PreservesReachabilityFrom_failure _ _ _ ‹_›)

/-- Shorthand for the reachability configuration of TreeKEM. -/
local notation "config" => MLS.TreeKEM.reachability

/-- The reachability lemma of the action `c` of the configuration, on the input `i`. -/
local macro "action " c:term:max i:term:max : term =>
  `(Traceful.PreservesReachability_base $c config $i)

/-- Proves that the attacker knows `b` on the current trace, from the fact that it knew `b` on an earlier trace. -/
local macro "knows_later" : tactic =>
  `(tactic| (refine Bytes.AttackerKnows_le _ _ _ ?_ ‹_›; grind))

/-- Splits a goal `∀ p ∈ [p₁, …, pₙ], P p` (the precondition of `Client.commit.reach`) into `P p₁ ∧ … ∧ P pₙ`. -/
local macro "knows_list" : tactic =>
  `(tactic| simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true])

/-- Proves that a program made of reads of states, `guard`, `pure`, `failure`, `List.mapM` and `for` is read-only. -/
local macro "read_only" : tactic =>
  `(tactic| repeat (first
    | exact Traceful.ReadOnly_pure _
    | exact Traceful.ReadOnly_failure
    | exact Traceful.ReadOnly_guard _
    | exact PersistentLocalState.getLocalState.readOnly _ _
    | refine Traceful.ReadOnly_bind _ _ ?_ fun _ => ?_
    | refine Traceful.ReadOnly_mapM _ (fun _ => ?_) _
    | refine Traceful.ReadOnly_forIn _ _ _ (fun _ _ => ?_)
    | split))

/-! ## Attacker knowledge -/

theorem attackerKnows_serializeNE {α: Type} (mf: NonExtensibleMessageFormat Bytes α) (x: α) (tr: ExecTrace):
  (serializeNE mf x).AttackerKnows tr ↔ mf.wf (Bytes.AttackerKnows · tr) x
:=
  pred_serializeNE_iff mf (Bytes.AttackerKnows · tr) x

theorem attackerKnows_mlsBytesEmpty (tr: ExecTrace): (MlsBytes.empty: MlsBytes Bytes).val.AttackerKnows tr :=
  BytesCompatiblePred.pred_empty (pred := (Bytes.AttackerKnows · tr))

theorem mfLeafContent_empty_attackerKnows (tr: ExecTrace):
  TreeKEM.tkt.mfLeafContent.wf (Bytes.AttackerKnows · tr) MlsBytes.empty
:=
  Eq.mpr (TreeKEM.tkt.mfLeafContent.wf_eq _ _) (attackerKnows_mlsBytesEmpty tr)

theorem leafNodeSkeleton_attackerKnows (source: LeafNodeSource) (tr: ExecTrace):
  (serializeNE (LeafNode.mf TreeKEM.tkt) (leafNodeSkeleton source)).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE]
  cases source <;> simp [leafNodeSkeleton, emptyMlsList, emptyExtensions, attackerKnows_mlsBytesEmpty,
    mfLeafContent_empty_attackerKnows, StaticOption.mk]
  exact fun _ => attackerKnows_mlsBytesEmpty tr

theorem keyPackageSkeleton_attackerKnows (tr: ExecTrace):
  (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackageSkeleton).AttackerKnows tr
:= by
  have := leafNodeSkeleton_attackerKnows .keyPackage tr
  rw [attackerKnows_serializeNE] at this ⊢
  simp_all [keyPackageSkeleton, emptyExtensions, attackerKnows_mlsBytesEmpty]

theorem proposal_attackerKnows {proposal: Proposal Bytes} {tr: ExecTrace}
  (h: (serializeNE Proposal.mf proposal).AttackerKnows tr):
  (serializeNE ProposalOrRef.mf (.proposal proposal)).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE] at h ⊢
  simp only [ProposalOrRef.mf.wf_eq]
  exact h

theorem add_attackerKnows {keyPackage: KeyPackage Bytes TreeKEM.tkt} {tr: ExecTrace}
  (h: (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackage).AttackerKnows tr):
  (serializeNE Proposal.mf (.add { keyPackage })).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE] at h ⊢
  simpa using h

theorem remove_attackerKnows (removed: UInt32) (tr: ExecTrace):
  (serializeNE Proposal.mf (.remove { removed } : Proposal Bytes)).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE]
  simp

theorem groupContextExtensions_attackerKnows (tr: ExecTrace):
  (serializeNE Proposal.mf (.groupContextExtensions { extensions := emptyExtensions } : Proposal Bytes)).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE]
  simp [emptyExtensions]

/-- The resumption PSK proposal of the group of `commit`, with a nonce built from bytes known by the attacker. -/
theorem resumptionPsk_attackerKnows {commit: ConfirmedTranscriptHashInput Bytes} {epoch: UInt64}
  {nonceBytes: Bytes} {nonce: MlsBytes Bytes} {funName: String} {tr: ExecTrace}
  (hnonce: mkMlsBytes nonceBytes funName "pskNonce" = .success nonce)
  (hcommit: (serializeNE ConfirmedTranscriptHashInput.mf commit).AttackerKnows tr)
  (hnonceBytes: nonceBytes.AttackerKnows tr):
  (serializeNE Proposal.mf (.psk { psk := .resumption .application commit.content.groupId epoch nonce })).AttackerKnows tr
:= by
  rw [attackerKnows_serializeNE] at hcommit ⊢
  rw [mkMlsBytes_eq_success] at hnonce
  simp_all

/-! ## Read-only actions -/

theorem checkGroup.readOnly (epoch: UInt64) (members: List (Client × Nat)):
  (checkGroup epoch members).ReadOnly
:= by
  unfold checkGroup Client.state getTreesyncTreekemState getEpochSecret getNodeKeys
  read_only

/-! ## Actions of the attacker -/

theorem receiveKeyPackage.reach (keyPackageTs: Nat):
  (receiveKeyPackage keyPackageTs).PreservesReachability config (fun _ => True)
    (fun keyPackage tr => (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackage).AttackerKnows tr)
:= by
  intro tr h_tr _
  unfold receiveKeyPackage
  reach Network.receiveMessage.preservesReachability _ keyPackageTs
  split
  · reach_pure using (attackerKnows_serializeNE _ _ _).2 (wf_of_parse _ _ _ _ ‹_› ‹_›)
  · reach_failure

theorem receiveProposal.reach (proposalTs: Nat):
  (receiveProposal proposalTs).PreservesReachability config (fun _ => True)
    (fun proposal tr => (serializeNE Proposal.mf proposal).AttackerKnows tr)
:= by
  intro tr h_tr _
  unfold receiveProposal
  reach Network.receiveMessage.preservesReachability _ proposalTs
  split
  · reach_pure using (attackerKnows_serializeNE _ _ _).2 (wf_of_parse _ _ _ _ ‹_› ‹_›)
  · reach_failure

theorem receiveCommit.reach (commitTs: Nat):
  (receiveCommit commitTs).PreservesReachability config (fun _ => True)
    (fun commit tr => (serializeNE ConfirmedTranscriptHashInput.mf commit).AttackerKnows tr)
:= by
  intro tr h_tr _
  unfold receiveCommit
  reach Network.receiveMessage.preservesReachability _ commitTs
  split
  · reach_pure using (attackerKnows_serializeNE _ _ _).2 (wf_of_parse _ _ _ _ ‹_› ‹_›)
  · reach_failure

theorem sendProposal.reach (proposal: Proposal Bytes):
  (sendProposal proposal).PreservesReachability config
    (fun tr => (serializeNE Proposal.mf proposal).AttackerKnows tr) (fun _ _ => True)
:=
  action Network.reachability (serializeNE Proposal.mf proposal)

theorem proposalRef.reach (proposal: Proposal Bytes):
  (proposalRef proposal).PreservesReachability config
    (fun tr => (serializeNE Proposal.mf proposal).AttackerKnows tr)
    (fun ref tr => (serializeNE ProposalOrRef.mf ref).AttackerKnows tr)
:= by
  intro tr h_tr _
  unfold proposalRef
  reach extractResult.preservesReachability _ _ as ref
  reach extractResult.preservesReachability _ _ as ref'
  reach_pure using ?_
  rw [attackerKnows_serializeNE]
  simp only [ProposalOrRef.mf.wf_eq]
  rw [← (mkMlsBytes_eq_success _ _ _ _).1 ‹_›]
  apply makeProposalRef_attackerKnows _ _ _ ‹_›
  knows_later

theorem commitSkeleton.reach (proposals: List (ProposalOrRef Bytes)) (fullCommit: Bool):
  (commitSkeleton proposals fullCommit).PreservesReachability config
    (fun tr => ∀ p ∈ proposals, (serializeNE ProposalOrRef.mf p).AttackerKnows tr)
    (fun msg tr => (serializeNE ConfirmedTranscriptHashInput.mf msg).AttackerKnows tr)
:= by
  intro tr h_tr hproposals
  unfold commitSkeleton
  reach extractResult.preservesReachability _ _ as proposals'
  reach_pure using ?_
  rename_i tr' _ _ _
  have hproposals' : ∀ p ∈ proposals'.val, ProposalOrRef.mf.wf (Bytes.AttackerKnows · tr') p := by
    rw [← (mkMlsList_eq_success _ _ _ _).1 ‹_›]
    exact fun p hp => (attackerKnows_serializeNE _ _ _).1 (Bytes.AttackerKnows_le _ _ _ ‹_› (hproposals p hp))
  have hleafNode := (attackerKnows_serializeNE _ _ _).1 (leafNodeSkeleton_attackerKnows .commit tr')
  rw [attackerKnows_serializeNE]
  cases fullCommit <;> simp [attackerKnows_mlsBytesEmpty] <;>
    refine Eq.mpr (MlsUntaggedContent.mf.wf_commit _ _) (Eq.mpr (Commit.mf.wf_eq _ _) ⟨hproposals', ?_⟩) <;>
    simp [hleafNode, emptyMlsList]

/-! ## Honest clients -/

theorem Client.initialize.reach (me: Participant):
  (Client.initialize me).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.initialize
  reach action mkSignatureKey.reachability me
  reach action initializeAsCache.reachability me
  reach action initializeKeyPackageStore.reachability me
  reach action initializeProposalCache.reachability me
  reach action initializeUpdateCache.reachability me
  reach action initializePskStore.reachability me
  reach_pure

theorem Client.verifyCredential.reach (c other: Client):
  (c.verifyCredential other).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.verifyCredential
  reach action verifyCredential.reachability (c.me, c.authServiceSid, other.me, other.signatureKeySid)
  reach_pure

theorem Client.verifyCredentials.reach (c: Client) (others: List Client):
  (c.verifyCredentials others).PreservesReachability config (fun _ => True) (fun _ _ => True)
:=
  List.foldlM.preservesReachability _ _ Client.verifyCredential.reach others c

theorem Client.createGroup.reach (c: Client):
  c.createGroup.PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.createGroup
  reach action Network.reachability (serializeNE (LeafNode.mf TreeKEM.tkt) (leafNodeSkeleton .keyPackage))
    using leafNodeSkeleton_attackerKnows _ _ as leafNodeSkeletonTs
  reach action createGroup.reachability (c.me, c.signatureKeySid, c.authServiceSid, leafNodeSkeletonTs)
  reach_pure

theorem Client.generateKeyPackage.reach (c: Client):
  c.generateKeyPackage.PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.generateKeyPackage
  reach action Network.reachability (serializeNE (KeyPackage.mf TreeKEM.tkt) keyPackageSkeleton)
    using keyPackageSkeleton_attackerKnows _ as keyPackageSkeletonTs
  reach action generateKeyPackage.reachability (c.me, keyPackageSkeletonTs, c.signatureKeySid, c.keyPackageStoreSid)
    as ⟨_, _⟩
  reach_pure

theorem Client.generateUpdateProposal.reach (c: Client):
  c.generateUpdateProposal.PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.generateUpdateProposal
  reach action Network.reachability (serializeNE (LeafNode.mf TreeKEM.tkt) (leafNodeSkeleton .update))
    using leafNodeSkeleton_attackerKnows _ _ as leafNodeSkeletonTs
  reach action generateUpdateProposal.reachability
    (c.me, c.updateCacheSid, c.groupStateSid, leafNodeSkeletonTs, c.signatureKeySid) as ⟨_, _⟩
  reach_pure

theorem Client.processProposal.reach (c: Client) (proposalTs sender: Nat):
  (c.processProposal proposalTs sender).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.processProposal
  reach action processProposal.reachability (c.me, c.proposalCacheSid, proposalTs, sender)
  reach_pure

theorem Client.commit.reach (c: Client) (proposals: List (ProposalOrRef Bytes)) (fullCommit: Bool):
  (c.commit proposals fullCommit).PreservesReachability config
    (fun tr => ∀ p ∈ proposals, (serializeNE ProposalOrRef.mf p).AttackerKnows tr) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.commit
  reach commitSkeleton.reach proposals fullCommit using ‹_› as messageSkeleton
  reach action Network.reachability (serializeNE ConfirmedTranscriptHashInput.mf messageSkeleton)
    using ‹_› as messageSkeletonTs
  reach action createCommitAndWelcome.reachability
    (c.me, c.authServiceSid, c.proposalCacheSid, c.updateCacheSid, c.pskStoreSid, c.groupStateSid, messageSkeletonTs)
    as ⟨_, _⟩
  reach_pure

theorem Client.processCommit.reach (c: Client) (commitTs: Nat):
  (c.processCommit commitTs).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.processCommit
  reach action processCommit.reachability
    (c.me, c.authServiceSid, c.proposalCacheSid, c.updateCacheSid, c.pskStoreSid, c.groupStateSid, commitTs)
    as ⟨_, _⟩
  reach_pure

theorem Client.processWelcome.reach (c: Client) (welcomeTs ratchetTreeTs: Nat):
  (c.processWelcome welcomeTs ratchetTreeTs).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  unfold Client.processWelcome
  reach action processWelcome.reachability
    (c.me, c.keyPackageStoreSid, c.authServiceSid, c.pskStoreSid, welcomeTs, ratchetTreeTs) as ⟨_, _⟩
  reach_pure

/-! ## Scenario -/

theorem scenario.reach: scenario.PreservesReachability config (fun _ => True) (fun _ _ => True) := by
  intro tr h_tr _
  unfold scenario
  reach Client.initialize.reach _ as alice
  reach Client.initialize.reach _ as bob
  reach Client.initialize.reach _ as charlie
  reach Client.initialize.reach _ as dave
  reach Client.verifyCredentials.reach _ _ as alice
  reach Client.verifyCredentials.reach _ _ as bob
  reach Client.verifyCredentials.reach _ _ as charlie
  reach Client.verifyCredentials.reach _ _ as dave
  -- Epoch 0
  reach Client.createGroup.reach _ as alice
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 1
  reach Client.generateKeyPackage.reach _ as ⟨bobKeyPackageTs, bob⟩
  reach Client.generateKeyPackage.reach _ as ⟨charlieKeyPackageTs, charlie⟩
  reach receiveKeyPackage.reach _ as bobKeyPackage
  reach receiveKeyPackage.reach _ as charlieKeyPackage
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact ⟨proposal_attackerKnows (add_attackerKnows (by knows_later)),
      proposal_attackerKnows (add_attackerKnows (by knows_later))⟩) as ⟨res, alice⟩
  split
  split; rotate_left
  · reach_failure
  reach Client.processWelcome.reach _ _ _ as bob
  reach Client.processWelcome.reach _ _ _ as charlie
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 2
  reach Client.generateKeyPackage.reach _ as ⟨daveKeyPackageTs, dave⟩
  reach receiveKeyPackage.reach _ as daveKeyPackage
  reach sendProposal.reach _ using add_attackerKnows ‹_› as addDaveTs
  reach Client.processProposal.reach _ _ _ as alice
  reach Client.processProposal.reach _ _ _ as bob
  reach Client.processProposal.reach _ _ _ as charlie
  reach proposalRef.reach _ using add_attackerKnows (by knows_later) as addDaveRef
  reach Client.commit.reach _ _ _ using (by
    knows_list
    assumption) as ⟨res, bob⟩
  split
  split; rotate_left
  · reach_failure
  reach Client.processCommit.reach _ _ as alice
  reach Client.processCommit.reach _ _ as charlie
  reach Client.processWelcome.reach _ _ _ as dave
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 3
  reach Client.generateUpdateProposal.reach _ as ⟨updateBobTs, bob⟩
  reach receiveProposal.reach _ as updateBob
  reach Client.processProposal.reach _ _ _ as alice
  reach Client.processProposal.reach _ _ _ as bob
  reach Client.processProposal.reach _ _ _ as charlie
  reach Client.processProposal.reach _ _ _ as dave
  reach receiveCommit.reach _ as commit
  reach Random.attackerGenRand.preservesReachability _ _ as pskNonceBytes
  reach extractResult.preservesReachability _ _ as pskNonce
  reach proposalRef.reach _ using (by knows_later) as updateBobRef
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact ⟨‹_›, proposal_attackerKnows (remove_attackerKnows _ _),
      proposal_attackerKnows (resumptionPsk_attackerKnows ‹_› (by knows_later) (by knows_later)),
      proposal_attackerKnows (groupContextExtensions_attackerKnows _)⟩) as ⟨res, alice⟩
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  reach Client.processCommit.reach _ _ as bob
  reach Client.processCommit.reach _ _ as charlie
  reach Traceful.PreservesReachability_orElse _ _ _
    (fun _ _ _ => by
      reach Client.processCommit.reach _ _
      reach_pure)
    (fun _ _ _ => by reach_pure) as daveFailed
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  exact (checkGroup.readOnly _ _).preservesReachability config _ ‹_› trivial

theorem fullScenario.reach: fullScenario.PreservesReachability config (fun _ => True) (fun _ _ => True) := by
  intro tr h_tr _
  unfold fullScenario
  reach Client.initialize.reach _ as alice
  reach Client.initialize.reach _ as bob
  reach Client.initialize.reach _ as charlie
  reach Client.initialize.reach _ as dave
  reach Client.verifyCredentials.reach _ _ as alice
  reach Client.verifyCredentials.reach _ _ as bob
  reach Client.verifyCredentials.reach _ _ as charlie
  reach Client.verifyCredentials.reach _ _ as dave
  -- Epoch 0
  reach Client.createGroup.reach _ as alice
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 1
  reach Client.generateKeyPackage.reach _ as ⟨bobKeyPackageTs, bob⟩
  reach Client.generateKeyPackage.reach _ as ⟨charlieKeyPackageTs, charlie⟩
  reach receiveKeyPackage.reach _ as bobKeyPackage
  reach receiveKeyPackage.reach _ as charlieKeyPackage
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact ⟨proposal_attackerKnows (add_attackerKnows (by knows_later)),
      proposal_attackerKnows (add_attackerKnows (by knows_later))⟩) as ⟨res, alice⟩
  split
  split; rotate_left
  · reach_failure
  reach Client.processWelcome.reach _ _ _ as bob
  reach Client.processWelcome.reach _ _ _ as charlie
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 2
  reach Client.generateKeyPackage.reach _ as ⟨daveKeyPackageTs, dave⟩
  reach receiveKeyPackage.reach _ as daveKeyPackage
  reach sendProposal.reach _ using add_attackerKnows ‹_› as addDaveTs
  reach Client.processProposal.reach _ _ _ as alice
  reach Client.processProposal.reach _ _ _ as bob
  reach Client.processProposal.reach _ _ _ as charlie
  reach proposalRef.reach _ using add_attackerKnows (by knows_later) as addDaveRef
  reach Client.commit.reach _ _ _ using (by knows_list; assumption) as ⟨res, bob⟩
  split
  split; rotate_left
  · reach_failure
  reach Client.processCommit.reach _ _ as alice
  reach Client.processCommit.reach _ _ as charlie
  reach Client.processWelcome.reach _ _ _ as dave
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 3
  reach Client.commit.reach _ _ _ using (by knows_list) as ⟨res, charlie⟩
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  reach Client.processCommit.reach _ _ as alice
  reach Client.processCommit.reach _ _ as bob
  reach Client.processCommit.reach _ _ as dave
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 4
  reach Client.generateUpdateProposal.reach _ as ⟨updateBobTs, bob⟩
  reach receiveProposal.reach _ as updateBob
  reach Client.processProposal.reach _ _ _ as alice
  reach Client.processProposal.reach _ _ _ as bob
  reach Client.processProposal.reach _ _ _ as charlie
  reach Client.processProposal.reach _ _ _ as dave
  reach receiveCommit.reach _ as commit
  reach Random.attackerGenRand.preservesReachability _ _ as pskNonceBytes
  reach extractResult.preservesReachability _ _ as pskNonce
  reach proposalRef.reach _ using (by knows_later) as updateBobRef
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact ⟨‹_›, proposal_attackerKnows (remove_attackerKnows _ _),
      proposal_attackerKnows (resumptionPsk_attackerKnows ‹_› (by knows_later) (by knows_later)),
      proposal_attackerKnows (groupContextExtensions_attackerKnows _)⟩) as ⟨res, alice⟩
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  reach Client.processCommit.reach _ _ as bob
  reach Client.processCommit.reach _ _ as dave
  reach Traceful.PreservesReachability_orElse _ _ _
    (fun _ _ _ => by
      reach Client.processCommit.reach _ _
      reach_pure)
    (fun _ _ _ => by reach_pure) as charlieFailed
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 5
  reach Client.generateKeyPackage.reach _ as ⟨charlieKeyPackageTs, charlie⟩
  reach receiveKeyPackage.reach _ as charlieKeyPackage
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact proposal_attackerKnows (add_attackerKnows ‹_›)) as ⟨res, dave⟩
  split
  split; rotate_left
  · reach_failure
  reach Client.processCommit.reach _ _ as alice
  reach Client.processCommit.reach _ _ as bob
  reach Client.processWelcome.reach _ _ _ as charlie
  reach (checkGroup.readOnly _ _).preservesReachability config
  -- Epoch 6
  reach Client.commit.reach _ _ _ using (by
    knows_list
    exact ⟨proposal_attackerKnows (remove_attackerKnows _ _), proposal_attackerKnows (remove_attackerKnows _ _)⟩)
    as ⟨res, bob⟩
  reach (Traceful.ReadOnly_guard _).preservesReachability config
  reach Client.processCommit.reach _ _ as charlie
  exact (checkGroup.readOnly _ _).preservesReachability config _ ‹_› trivial

/-- The trace of the honest run of the sanity checks is reachable. -/
public
theorem scenario_reachable: (scenario.run Trace.empty).snd.val.Reachable config :=
  Traceful.PreservesReachability_to_Reachable scenario.reach trivial

/--
info: 'MLS.TreeKEM.SanityChecks.scenario_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scenario_reachable

/-- The trace of the longer honest run of the sanity checks (not checked by `#guard` yet) is reachable. -/
public
theorem fullScenario_reachable: (fullScenario.run Trace.empty).snd.val.Reachable config :=
  Traceful.PreservesReachability_to_Reachable fullScenario.reach trivial

/--
info: 'MLS.TreeKEM.SanityChecks.fullScenario_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fullScenario_reachable

end MLS.TreeKEM.SanityChecks
