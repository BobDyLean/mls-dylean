/-
  Port of DY*'s label library (`DY.Lib.Label.BigJoin`, `DY.Lib.Label.Guarded`, `DY.Lib.Label.Prop`)
  and of `DY.Core.Label.Unknown`.

  Differences with DY*:
  - DyLean's labels are semantic (`Label.isCorrupt` on execution traces): the definitions are not opaque,
    and the `is_corrupt_*` lemmas hold by `rfl`.
  - DY*'s `event_triggered_label prin content` is DyLean's `ProtocolEvent.label ev`
    (DyLean's events record their principal as a field).
  - `is_corrupt_guarded_event` is only ported in the direction used by MLS* (`Label.isCorrupt_guarded_event`),
    with the time `i` of the first occurrence of the event (`tr.EventFirstLoggedAt ev i`)
    instead of `find_event_triggered_at_timestamp`.
  - `guarded_authentication_lemma` (`Label.guarded_authentication`) is stated on the prefixes of a proof trace,
    and its hypothesis is directly on the prefix just before the label `g` becomes corrupt
    (DY*'s `event_pred_lemma` and `auth_pred_lemma` are applied to the minimal corrupt trace,
    here it is the prefix of length `i+1` such that `g` is corrupt on it but not on the prefix of length `i`).
-/

module

public import DY.Label
public import DY.Actions.ProtocolEvent
public import DySlop.Lib.Event

open DY

namespace DY.Label

variable [ExecTraceTypes]

/-- A corrupt label flows to every label. -/
public
theorem canFlow_of_isCorrupt (l1 l2: Label) (tr: ExecTrace) (h: l1.isCorrupt tr): l1.canFlow l2 tr :=
  fun _ hle _ => l1.isCorruptLater _ _ hle h

/-! ## Algebra of `join` -/

/-- Port of `join_associative`. -/
public
theorem join_assoc (l1 l2 l3: Label): (l1.join l2).join l3 = l1.join (l2.join l3) := by
  ext
  grind

public
theorem join_secret_right (l: Label): l.join Label.secret = l := by
  ext
  simp

public
theorem join_secret_left (l: Label): Label.secret.join l = l := by
  ext
  simp

/-- Port of `meet_associative`. -/
public
theorem meet_assoc (l1 l2 l3: Label): (l1.meet l2).meet l3 = l1.meet (l2.meet l3) := by
  ext
  grind

public
theorem meet_pub_left (l: Label): Label.pub.meet l = l := by
  ext
  simp

public
theorem meet_pub_right (l: Label): l.meet Label.pub = l := by
  ext
  simp

/-! ## Equivalence of labels -/

public
theorem equivalent_refl (l: Label) (tr: ExecTrace): l.equivalent l tr :=
  ⟨canFlowRefl l tr, canFlowRefl l tr⟩

public
theorem equivalent_symm (l1 l2: Label) (tr: ExecTrace) (h: l1.equivalent l2 tr): l2.equivalent l1 tr :=
  ⟨h.2, h.1⟩

public
theorem equivalent_trans (l1 l2 l3: Label) (tr: ExecTrace)
  (h12: l1.equivalent l2 tr) (h23: l2.equivalent l3 tr):
  l1.equivalent l3 tr
:=
  ⟨canFlowTrans _ _ _ _ h12.1 h23.1, canFlowTrans _ _ _ _ h23.2 h12.2⟩

/-- Joins of equivalent labels are equivalent. -/
public
theorem equivalent_join (l1 l1' l2 l2': Label) (tr: ExecTrace)
  (h1: l1.equivalent l1' tr) (h2: l2.equivalent l2' tr):
  (l1.join l2).equivalent (l1'.join l2') tr
:= by
  grind [canFlow]

/-- Meets of equivalent labels are equivalent. -/
public
theorem equivalent_meet (l1 l1' l2 l2': Label) (tr: ExecTrace)
  (h1: l1.equivalent l1' tr) (h2: l2.equivalent l2' tr):
  (l1.meet l2).equivalent (l1'.meet l2') tr
:= by
  grind [canFlow]

/-! ## Big join -/

/-- Port of `big_join`: `join`, over a possibly unbounded domain. -/
@[expose]
public
def bigJoin {α: Type} (f: α → Label): Label where
  isCorrupt tr := ∃ x, (f x).isCorrupt tr

/-- Port of `is_corrupt_big_join`. -/
@[simp]
public
theorem bigJoin_isCorrupt {α: Type} (f: α → Label) (tr: ExecTrace):
  (bigJoin f).isCorrupt tr ↔ ∃ x, (f x).isCorrupt tr
:= Iff.rfl

grind_pattern bigJoin_isCorrupt => (bigJoin f).isCorrupt tr

/-- Port of `big_join_eq`. -/
public
theorem canFlow_bigJoin_iff {α: Type} (f: α → Label) (l: Label) (tr: ExecTrace):
  l.canFlow (bigJoin f) tr ↔ ∀ x, l.canFlow (f x) tr
:= by
  grind [canFlow]

/-- Port of `big_join_flow_to_component`. -/
public
theorem bigJoin_canFlow {α: Type} (f: α → Label) (x: α) (tr: ExecTrace):
  (bigJoin f).canFlow (f x) tr
:= by
  grind [canFlow]

/-! ## Labels of propositions -/

/--
Port of `prop_to_label`: interpret a proposition as a label,
always corrupt if the proposition is true, otherwise never corrupt.
-/
@[expose]
public
def ofProp (p: Prop): Label where
  isCorrupt _ := p

/-- Port of `is_corrupt_prop_to_label`. -/
@[simp]
public
theorem ofProp_isCorrupt (p: Prop) (tr: ExecTrace): (ofProp p).isCorrupt tr ↔ p := Iff.rfl

grind_pattern ofProp_isCorrupt => (ofProp p).isCorrupt tr

/-! ## Unknown label -/

/--
Port of `unknown_label`.
It is in reality public (always corrupt), but this definition is not exposed: other modules cannot reason on it.
-/
public
def unknown: Label := Label.pub

/-! ## Guarded labels -/

/-- Port of `guarded`: `guarded l g` is corrupt when `l` was corrupt before `g` was corrupt. -/
@[expose]
public
def guarded (l g: Label): Label where
  isCorrupt tr := ∃ trBefore, trBefore ≤ tr ∧ l.isCorrupt trBefore ∧ ¬ g.isCorrupt trBefore
  isCorruptLater := by grind [Trace.le_trans]

/-- Port of `is_corrupt_guarded`. -/
public
theorem guarded_isCorrupt (l g: Label) (tr: ExecTrace):
  (guarded l g).isCorrupt tr ↔ ∃ trBefore, trBefore ≤ tr ∧ l.isCorrupt trBefore ∧ ¬ g.isCorrupt trBefore
:= Iff.rfl

/-- Port of `guarded_can_flow`. -/
public
theorem guarded_canFlow (l1 l2 g1 g2: Label) (tr: ExecTrace)
  (hg: ∀ tr, g2.canFlow g1 tr) (hl: ∀ tr, l1.canFlow l2 tr):
  (guarded l1 g1).canFlow (guarded l2 g2) tr
:= by
  intro _ _ ⟨trBefore, hle, hl2, hng2⟩
  exact ⟨trBefore, hle, hl _ _ (Trace.le_refl _) hl2, fun hg1 => hng2 (hg _ _ (Trace.le_refl _) hg1)⟩

/--
The prefix of a trace on which an event was not logged is before every time this event is logged in the trace.
-/
theorem le_prefix_of_not_eventLogged {EventT: Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (ev: EventT) (trBefore tr: ExecTrace) (i: Nat)
  (hle: trBefore ≤ tr) (hev: tr.EventLoggedAt ev i) (hnev: ¬ trBefore.EventLogged ev):
  trBefore ≤ tr.prefix i
:= by
  have := Trace.le_imp_prefix_eq _ _ hle
  have: trBefore.length ≤ i := by
    apply Nat.le_of_not_lt
    intro hi
    exact hnev ⟨i, Trace.EventLoggedAt_le' ev i _ _ hi hle hev⟩
  grind

/--
Port of `is_corrupt_guarded_event` (one direction):
if `guarded l (event label)` is corrupt, `l` was corrupt before the first time the event was logged.
-/
public
theorem isCorrupt_guarded_event {EventT: Type} [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
  (tr: ExecTrace) (l: Label) (ev: EventT)
  (h: (guarded l (ProtocolEvent.label ev)).isCorrupt tr) (hev: tr.EventLogged ev):
  ∃ i, tr.EventFirstLoggedAt ev i ∧ l.isCorrupt (tr.prefix i)
:= by
  obtain ⟨trBefore, hle, hl, hng⟩ := h
  obtain ⟨i, hfirst⟩ := ProtocolEvent.exists_eventFirstLoggedAt tr ev hev
  refine ⟨i, hfirst, ?_⟩
  rw [ProtocolEvent.label_isCorrupt] at hng
  exact l.isCorruptLater _ _ (le_prefix_of_not_eventLogged ev _ _ _ hle hfirst.1 hng) hl

/--
Port of `guarded_authentication_lemma`.
A typical use-case of `guarded` is when `l` is the label of an authentication key (e.g. a signature key),
and `g` is a join of event labels.
When `g` is corrupt (i.e. an event has been logged),
either `l` was corrupt before the event (`guarded l g` is corrupt),
or an authentication predicate holds on the trace just before the event.
The hypothesis `hauth` is applied to the prefix of length `i` such that `g` is not corrupt on it,
but is corrupt on the prefix of length `i+1` (i.e. the event was logged at time `i`).
`hg0` excludes labels `g` that are corrupt on the empty trace.
-/
public
theorem guarded_authentication [ProofTraceTypes] (tr: ProofTrace) (l g: Label) (authPred: ProofTrace → Prop)
  (hauth: ∀ i, g.isCorrupt (tr.prefix (i+1)).erase → ¬ g.isCorrupt (tr.prefix i).erase →
    l.isCorrupt (tr.prefix i).erase ∨ authPred (tr.prefix i))
  (hg0: ¬ g.isCorrupt (tr.prefix 0).erase) (hg: g.isCorrupt tr.erase):
  (guarded l g).isCorrupt tr.erase ∨ ∃ i, ¬ g.isCorrupt (tr.prefix i).erase ∧ authPred (tr.prefix i)
:= by
  suffices ∀ n, g.isCorrupt (tr.prefix n).erase →
      (guarded l g).isCorrupt tr.erase ∨ ∃ i, ¬ g.isCorrupt (tr.prefix i).erase ∧ authPred (tr.prefix i) from
    this tr.length (by simpa using hg)
  intro n hn
  induction n with
  | zero => grind
  | succ i ih =>
    by_cases hng: g.isCorrupt (tr.prefix i).erase
    · grind
    grind [guarded_isCorrupt]

end DY.Label
