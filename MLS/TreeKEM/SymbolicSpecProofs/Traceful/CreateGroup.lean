module

public import MLS.TreeKEM.SymbolicSpec.Traceful.CreateGroup
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.GenerateKeyPackage
public import MLS.TreeSync.SymbolicProofs.Event.LeafNodeHasBeenVerified.Invariant
public import MLS.TreeSync.SymbolicProofs.API.IsWellFormedInvariant
public import MLS.TreeKEM.SymbolicProofs.API.Tree
import all MLS.TreeKEM.SymbolicSpec.Traceful.CreateGroup
import all MLS.TreeKEM.SymbolicSpec.EpochEvent
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.CreateGroup.Proof`.

Port-specific differences:
- The proofs are DyLean Hoare triples (instances), assuming the invariants of
  `MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants` (MLS*'s `has_treesync_and_treekem_invariants`).
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.Bootstrap MLS.TreeKEM.Symbolic.API.KeySchedule

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace]
variable [HasTreesyncInvariants tkt] [HasTreeKEMProofTrace]
variable [HasTreesyncTreekemLinkInvariants] [HasIAmInGroupInvariant] [HasMlsKeyscheduleInvariants]

/-! ## Create group, proof -/

/-- Port of `_create_group_proof`. -/
@[instance]
public
theorem createGroup'.proof (me: Participant) (mySignatureKeySid: Nat) (authServiceSid: Nat)
  (leafNodeSkeleton: LeafNode Bytes tkt):
  HoareTriple
    (createGroup' me mySignatureKeySid authServiceSid leafNodeSkeleton)
    (fun tr => (LeafNode.mf tkt).wf (Bytes.Publishable · tr) leafNodeSkeleton)
    (fun st tr => TreesyncTreekemStateAllInvariants tr me st)
:= by
  unfold createGroup'
  step with ⟨ fun _ => Label.pub, Usage.nothing ⟩
  step
  step
  split
  step
  step
  step_intro
  have hpend := API.prepareCreate_valid _ _ ‹API.prepareCreate groupId _ = _›
  have hgid := (mkMlsBytes_eq_success _ _ _ _).1 ‹mkMlsBytes _ "_create_group" "group_id" = _›
  step by
    refine ⟨by grind, wf_invariant_of_publishable _ _ _ (by grind), ⟨token, ?_⟩, hpend.1⟩
    rw [← hpend.2]
    assumption
  step
  step
  step_intro
  step
  step_intro
  step
  step with ⟨ fun _ => Label.secret, Usage.kdfExpandKey "MLS.TreeKEM.EpochSecret" (serializeNE GroupContext.mf groupContext) ⟩
  step
  split
  -- facts on the group context and the key schedule
  have hts := API.finalizeCreate_wf (Bytes.Publishable · tr) pendingCreate token ‹_ ∧ _›.1
  have hth: TreeHasHash treesync.tree treeHash.val := by
    have := (mkMlsBytes_eq_success _ _ _ _).1 ‹mkMlsBytes _ "_create_group" "tree_hash" = _›
    grind [TreeHasHash, API.computeTreeHash]
  have hgc: GroupContext.mf.wf (Bytes.Publishable · tr) groupContext := by
    have := pred_treeHash _ _ _ hth (preIsHashCompatible_publishable tr) hts
    simp only [groupContext, GroupContext.mf.wf_eq]
    refine ⟨by grind [Bytes.Publishable], this, ?_, by simp [emptyExtensions]⟩
    simpa [MlsBytes.empty] using BytesCompatiblePred.pred_empty (pred := (Bytes.Publishable · tr))
  have hleaf: IAmInTreeAt me treesync.tree 0 := by
    have := API.leafAtNat_finalizeCreate pendingCreate token 0
    simp only [API.leafAtNat] at this
    grind [IAmInTreeAt, API.finalizeCreate, treeCreate, Tree.containsLeafIndex]
  have hcreate := ‹API.create leafSk leafPk epochSecret groupContext = _›
  simp only [API.create, Result.bind_eq_success, Result.pure_eq_success, Prod.mk.injEq] at hcreate
  obtain ⟨⟨ks, encSecret⟩, hks, rfl, rfl⟩ := hcreate
  step by
    have hksGood := createFromEpochSecret_proof tr epochSecret groupContext ks encSecret hks ‹_› hgc ‹_›
    rw [ProtocolEvent.EventInv.Has.invariant_eq (pred := iAmInGroupPred)]
    simp only [iAmInGroupPred]
    refine ⟨hth, IHaveVerifiedEveryLeafNode_finalizeCreate _ _ _ _ ‹_›, rfl, rfl, ?_, hksGood.1, ?_⟩
    · exact hleaf
    · rw [← ‹epochSecret.label tr = Label.secret›]
      exact hksGood.2.1
  step
  subst x
  have hgc := ‹GroupContext.mf.wf (Bytes.Publishable · tr) groupContext›
  have hksGood := createFromEpochSecret_proof tr epochSecret groupContext ks encSecret hks ‹_› hgc ‹_›
  refine ⟨⟨?_, API.Tree.create_valid _ _, ?_, ‹_›, hgc, ‹_›, ?_, ?_, ?_⟩, ⟨hksGood.1, ⟨_, _, hksGood.2.2⟩, ‹_›⟩, ?_⟩
  · exact API.finalizeCreate_treeValid _ _ hpend
  · exact create_stateRel pendingCreate token leafSk leafPk (‹leafPk = _›).symm
  · exact API.finalizeCreate_valid _ _ hpend ‹_›
  · exact IHaveVerifiedEveryLeafNode_finalizeCreate _ _ pendingCreate token ‹_›
  · exact MLS.TreeKEM.Symbolic.API.Tree.create_proof tr me leafSk leafPk ‹_›
  · exact ⟨_, rfl, ‹_›, rfl, rfl, rfl⟩

/-- Port of `create_group_proof`. -/
@[instance]
public
theorem createGroup.proof (me: Participant) (mySignatureKeySid: Nat) (authServiceSid: Nat) (leafNodeSkeletonTs: Nat):
  HoareTriple
    (createGroup me mySignatureKeySid authServiceSid leafNodeSkeletonTs)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold createGroup
  step
  split
  · step by
      exact wf_of_parse _ _ _ _ ‹_› ‹_›
    step
    trivial
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

end MLS.TreeKEM
