module

public import MLS.TreeKEM.SymbolicSpec.EpochEvent
import all MLS.TreeKEM.SymbolicSpec.EpochEvent

/-!
Lemmas about the predicates of `MLS.TreeKEM.Symbolic.EpochEvent` on traces.

Port-specific differences:
- `IHavePreviousEpochEvent_le` is not in MLS* (DY*'s SMT patterns on `event_triggered` give it).
- The event predicate (`i_am_in_group_pred`, …) is not ported yet.
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync

variable [HasSymbolicBytes] [ExecTraceTypes] [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]

/-- The previous epoch event is still logged when the trace grows. -/
public
theorem IHavePreviousEpochEvent_le {previousTreeHeight: Nat} (tr1 tr2: ExecTrace) (me: Participant)
  (previousGroupContext: GroupContext Bytes) (previousInitSecret: Bytes) (previousTree: TreeSync Bytes tkt previousTreeHeight)
  : tr1 ≤ tr2 →
    IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree →
    IHavePreviousEpochEvent tr2 me previousGroupContext previousInitSecret previousTree
:= by
  intro hle ⟨previousEv, h⟩
  refine ⟨previousEv, ?_⟩
  grind [IHavePreviousEpochEventWithWitness]

grind_pattern IHavePreviousEpochEvent_le =>
  tr1 ≤ tr2,
  IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree
grind_pattern [grind_later] IHavePreviousEpochEvent_le =>
  tr1 ≤ tr2,
  IHavePreviousEpochEvent tr1 me previousGroupContext previousInitSecret previousTree

end MLS.TreeKEM
