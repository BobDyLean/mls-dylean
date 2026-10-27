module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ProcessProposal
public import MLS.TreeKEM.SymbolicSpecProofs.Traceful.AllInvariants
import all MLS.TreeKEM.SymbolicSpec.Traceful.ProcessProposal
import DY.Meta.Step

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessProposal.Proof`.

Port-specific differences:
- The proof is a DyLean Hoare triple (an instance), assuming the proof trace entries of the network
  and of the proposal cache (`HasTreeKEMProofTrace`).
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeSync MLS.TreeDEM

variable [HasSymbolicInvariants] [TraceInvariant] [HasTreeSyncExecTrace tkt] [HasTreeKEMExecTrace] [HasTreeKEMProofTrace]

/-! ## Process a Proposal, proof -/

/-- Port of `process_proposal_proof`. -/
@[instance]
public
theorem processProposal.proof (me: Participant) (proposalCacheSid: Nat) (proposalTs: Nat) (sender: Nat):
  HoareTriple
    (processProposal me proposalCacheSid proposalTs sender)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold processProposal
  step
  split
  · step by
      exact wf_of_parse _ _ _ _ ‹_› ‹_›
    trivial
  · simp only [WP.wp, Traceful.run_failure]
    exists tr

end MLS.TreeKEM
