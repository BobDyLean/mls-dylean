module

public import MLS.Symbolic.Code.Symbolic
import all MLS.Symbolic.Code.Symbolic
import DY.Meta.Step

/-!
Proofs about the traceful functions of `MLS.Symbolic` (`MLS/Symbolic/Code/Symbolic.lean`):
the Hoare triple of `extractResult`, which MLS* proves by unfolding it.
-/

namespace MLS

open DY

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]

/-- Hoare triple of `extract_result`: the result is the value of a successful computation. -/
@[instance]
public
theorem extractResult.proof {α: Type} (x: Result α):
  HoareTriple
    (extractResult x)
    (fun _ => True)
    (fun y _ => x = .success y)
:= by
  unfold extractResult
  split
  · step
    grind
  · apply HoareTriple.mk
    intro tr _ _
    simp only [WP.wp, Traceful.run_failure]
    exists tr

end MLS
