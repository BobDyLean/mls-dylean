module

public import MLS.TreeKEM.SymbolicSpec.State.ProposalCache
public import MLS.TreeKEM.SymbolicProofs.KeySchedule
public import MLS.Common.SymbolicProofs.Crypto.Derived.RefHash
public import MLS.Symbolic.SymbolicProofs.Symbolic
import all MLS.TreeKEM.SymbolicSpec.State.ProposalCache
import DY.Meta.Step

/-!
Port of the invariant and proofs of `MLS.TreeKEM.Symbolic.State.ProposalCache`.

Port-specific differences:
- The map predicate has no session identifier (see `DySlop.Map.MapPred`). It is an instance of `MapPred`,
  which gives the invariant of the maps: MLS*'s `has_proposal_cache_invariant` is not needed.
- The proofs of the traceful functions (`_retrieve_one_proposal_proof`, …) are DyLean Hoare triples (instances),
  assuming the proof trace entries of the map. The `tr_out == tr` part of their postconditions is not ported.
- `retrieveOneProposal'.proof` also states that the proposal is publishable (when the proposal or reference is):
  MLS* gets it in `retrieve_proposals_proof` by unfolding `_retrieve_one_proposal`.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.PersistentLocalState
open MLS MLS.TreeDEM
open DySlop.Map (Map MapPred)

variable [HasSymbolicInvariants]
variable [ExecTraceTypes.Has (CompromisableState.ExecEntryT (Map ProposalCacheKey ProposalAndSender))]

/-- Port of `proposal_cache_pred`. -/
public
instance proposalCachePred: MapPred ProposalCacheKey ProposalAndSender where
  pred tr _ key value :=
    key.proposalRef.Publishable tr ∧
    Proposal.mf.wf (Bytes.Publishable · tr) value.proposal ∧
    makeProposalRef (serializeNE Proposal.mf value.proposal) = .success key.proposalRef
  pred_later tr1 tr2 prin key value := by
    grind
  pred_knowable tr prin key value m _ h := by
    show ProposalCacheKey.mf.wf _ _ ∧ ProposalAndSender.mf.wf _ _
    rw [ProposalCacheKey.mf.wf_eq, ProposalAndSender.mf.wf_eq]
    have := wf_knowableBy_of_publishable Proposal.mf (label prin m) tr value.proposal h.2.1
    grind [Bytes.Publishable, Bytes.KnowableBy, canFlowTrans]

section Proofs

variable [TraceInvariant]
variable [ProofTraceTypes.Has (CompromisableState.ProofEntryT (Map ProposalCacheKey ProposalAndSender))]
variable [TraceInvariant.Has (CompromisableState.ProofEntryT (Map ProposalCacheKey ProposalAndSender))]

/-- Invariant of `initialize_proposal_cache` (DY*'s `initialize_map_invariant`). -/
@[instance]
public
theorem initializeProposalCache.proof (prin: Participant):
  HoareTriple
    (initializeProposalCache prin)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold initializeProposalCache
  exact DySlop.Map.initializeMap.proof prin

/-- Port of `_retrieve_one_proposal_proof`. -/
@[instance]
public
theorem retrieveOneProposal'.proof (me: Participant) (sid: Nat) (myIndex: Nat) (proposalOrRef: ProposalOrRef Bytes):
  HoareTriple
    (retrieveOneProposal' me sid myIndex proposalOrRef)
    (fun tr => ProposalOrRef.mf.wf (Bytes.Publishable · tr) proposalOrRef)
    (fun res tr =>
      ProposalOrRefRel proposalOrRef res.proposal ∧
      Proposal.mf.wf (Bytes.Publishable · tr) res.proposal
    )
:= by
  unfold retrieveOneProposal'
  split
  · step
    grind [ProposalOrRefRel, ProposalOrRef.mf.wf_eq]
  · step
    simp only [MapPred.pred] at *
    grind [ProposalOrRefRel]

/-- Port of `retrieve_proposals_proof`. -/
@[instance]
public
theorem retrieveProposals.proof (me: Participant) (sid: Nat) (myIndex: Nat) (proposalOrRefs: List (ProposalOrRef Bytes)):
  HoareTriple
    (retrieveProposals me sid myIndex proposalOrRefs)
    (fun tr => ∀ por ∈ proposalOrRefs, ProposalOrRef.mf.wf (Bytes.Publishable · tr) por)
    (fun res tr =>
      ProposalOrRefsRel proposalOrRefs (res.map (·.proposal)) ∧
      ∀ p ∈ res.map (·.proposal), Proposal.mf.wf (Bytes.Publishable · tr) p
    )
:= by
  induction proposalOrRefs with
  | nil =>
    unfold retrieveProposals
    step
    grind [ProposalOrRefsRel]
  | cons h t ih =>
    unfold retrieveProposals
    step
    step
    step
    grind [ProposalOrRefsRel]

/-- Port of `remember_proposal_proof`. -/
@[instance]
public
theorem rememberProposal.proof (me: Participant) (sid: Nat) (proposal: Proposal Bytes) (sender: Nat):
  HoareTriple
    (rememberProposal me sid proposal sender)
    (fun tr => Proposal.mf.wf (Bytes.Publishable · tr) proposal)
    (fun _ _ => True)
:= by
  unfold rememberProposal
  step
  step_intro
  step_intro
  step by
    have := (pred_serializeNE_iff Proposal.mf (Bytes.Publishable · tr) proposal).2 ‹_›
    have := makeProposalRef_knowableBy tr Label.pub _ _ ‹_› (by grind [Bytes.KnowableBy, Bytes.Publishable])
    simp only [MapPred.pred]
    grind [Bytes.KnowableBy, Bytes.Publishable]
  trivial

end Proofs

end MLS.TreeKEM
