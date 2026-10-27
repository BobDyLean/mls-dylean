/-
  Port of the event predicates of `DY.Lib.Event.Typed` (`has_event_pred`),
  and lemmas locating events in the prefixes of a trace.

  Differences with DY*:
  - DyLean's event invariants are given by the instance `ProtocolEvent.EventInv EventT` of the protocol;
    DY*'s `has_event_pred pred` is the class `ProtocolEvent.EventInv.Has pred`, stating that this invariant is `pred`.
-/

module

public import DY.Actions.ProtocolEvent

open DY

namespace DY.ProtocolEvent

section Execution

variable [ExecTraceTypes] {EventT: Type} [ExecTraceTypes.Has (ExecEntryT EventT)]

/-- No event is logged in the empty prefix of a trace. -/
public
theorem not_eventLogged_prefix_zero (tr: ExecTrace) (ev: EventT):
  ¬ (tr.prefix 0).EventLogged ev
:= by
  grind

/-- An event logged in the prefix of length `i+1` of a trace, but not in the prefix of length `i`, is logged at time `i`. -/
public
theorem eventLoggedAt_of_prefix_succ (tr: ExecTrace) (ev: EventT) (i: Nat)
  (h: (tr.prefix (i+1)).EventLogged ev) (hn: ¬ (tr.prefix i).EventLogged ev):
  tr.EventLoggedAt ev i
:= by
  obtain ⟨j, hj⟩ := h
  have := Trace.EventLoggedAt_implies_i_le_length _ _ _ hj
  have hle: tr.prefix i ≤ tr.prefix (i+1) := Trace.prefix_le_prefix _ _ _ (by omega)
  have: j = i := by
    apply Nat.le_antisymm (by grind)
    apply Nat.le_of_not_lt
    intro hji
    exact hn ⟨j, Trace.EventLoggedAt_le' ev j _ _ (by grind) hle hj⟩
  grind

/--
The event `ev` is logged at time `i` for the first time in `tr`
(DY*'s `find_event_triggered_at_timestamp tr prin ev = i`).
-/
@[expose]
public
def _root_.DY.Trace.EventFirstLoggedAt (ev: EventT) (i: Nat) (tr: ExecTrace): Prop :=
  tr.EventLoggedAt ev i ∧ ¬ (tr.prefix i).EventLogged ev

/-- An event logged in a trace has a first occurrence (DY*'s `find_event_triggered_at_timestamp`). -/
public
theorem exists_eventFirstLoggedAt (tr: ExecTrace) (ev: EventT) (h: tr.EventLogged ev):
  ∃ i, tr.EventFirstLoggedAt ev i
:= by
  suffices ∀ n, (tr.prefix n).EventLogged ev → ∃ i, tr.EventFirstLoggedAt ev i from
    this tr.length (by simpa using h)
  intro n hn
  induction n with
  | zero => exact absurd hn (not_eventLogged_prefix_zero tr ev)
  | succ k ih =>
    by_cases hk: (tr.prefix k).EventLogged ev
    · exact ih hk
    · exact ⟨k, eventLoggedAt_of_prefix_succ tr ev k hn hk, hk⟩

end Execution

section Proof

variable [ExecTraceTypes] [ProofTraceTypes]

/-- Port of `has_event_pred`: the invariant of the events of type `EventT` is `pred`. -/
public
class EventInv.Has {EventT: Type} [EventInv EventT] (pred: ProofTrace → EventT → Prop): Prop where
  invariant_eq: ∀ tr ev, EventInv.invariant tr ev = pred tr ev

/--
The invariant of the events of type `EventT` is `pred`, as a function
(to rewrite the preconditions stated with `EventInv.invariant`, e.g. those of the functions triggering events).
-/
public
theorem EventInv.Has.invariant_eq_fun {EventT: Type} [EventInv EventT] (pred: ProofTrace → EventT → Prop) [h: EventInv.Has pred]:
  (EventInv.invariant: ProofTrace → EventT → Prop) = pred
:= by
  funext tr ev
  exact h.invariant_eq tr ev

variable [TraceInvariant] {EventT: Type} [EventInv EventT]
variable [ExecTraceTypes.Has (ExecEntryT EventT)] [ProofTraceTypes.Has (ProofEntryT EventT)] [TraceInvariant.Has (ProofEntryT EventT)]

/-- The predicate of an event holds on the prefix of the trace before the event. -/
public
theorem EventInv.Has.pred_of_eventLoggedAt (pred: ProofTrace → EventT → Prop) [h: EventInv.Has pred]
  (tr: ProofTrace) (ev: EventT) (i: Nat)
  (hinv: tr.Invariant) (hev: tr.erase.EventLoggedAt ev i):
  pred (tr.prefix i) ev
:= by
  rw [← h.invariant_eq]
  exact Trace.EventLoggedAt_imp_EventInv _ _ _ hinv hev

/-- The predicate of an event holds on a prefix of the trace. -/
public
theorem EventInv.Has.pred_of_eventLogged (pred: ProofTrace → EventT → Prop) [EventInv.Has pred]
  (tr: ProofTrace) (ev: EventT)
  (hinv: tr.Invariant) (hev: tr.erase.EventLogged ev):
  ∃ i, pred (tr.prefix i) ev
:= by
  obtain ⟨i, hi⟩ := hev
  refine ⟨i, ?_⟩
  grind [EventInv.Has.pred_of_eventLoggedAt]

/-- The predicate of an event logged in a prefix of the trace holds on a shorter prefix. -/
public
theorem EventInv.Has.pred_of_eventLogged_prefix (pred: ProofTrace → EventT → Prop) [EventInv.Has pred]
  (tr: ProofTrace) (ev: EventT) (i: Nat)
  (hinv: tr.Invariant) (hev: (tr.prefix i).erase.EventLogged ev):
  ∃ j < i, pred (tr.prefix j) ev
:= by
  obtain ⟨j, hj⟩ := hev
  rw [Trace.prefix_erase] at hj
  have := Trace.EventLoggedAt_implies_i_le_length _ _ _ hj
  refine ⟨j, ?_⟩
  grind [EventInv.Has.pred_of_eventLoggedAt]

end Proof

end DY.ProtocolEvent
