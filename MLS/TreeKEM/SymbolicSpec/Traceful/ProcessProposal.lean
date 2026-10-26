module

public import MLS.TreeKEM.SymbolicSpec.Traceful.ExecTrace

/-!
Port of `MLS.TreeKEM.Symbolic.Traceful.ProcessProposal`.

Obtain a proposal from the network, and store it in our proposal cache.

Port-specific differences:
- DyLean's states are immutable: `processProposal` returns the new handle of the proposal cache.
-/

namespace MLS.TreeKEM

open Comparse
open DY DY.Comparse
open MLS MLS.TreeDEM

variable [HasSymbolicBytes] [ExecTraceTypes] [HasTreeKEMExecTrace]

/-! ## Process a Proposal -/

/--
Port of `process_proposal`.
Returns the new handle of the proposal cache.
-/
public
def processProposal (me: Participant) (proposalCacheSid: Nat) (proposalTs: Nat) (sender: Nat): Traceful Nat := do
  let proposalBytes ← Network.receiveMessage proposalTs
  let some proposal := (Proposal.mf (Bytes := Bytes)).toExtensible.parse proposalBytes | failure
  rememberProposal me proposalCacheSid proposal sender

end MLS.TreeKEM
