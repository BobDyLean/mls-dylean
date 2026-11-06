module

public import MLS.Symbolic.Code.Symbolic
public import DY.Trace.Reachability
public import DY.Actions.PersistentLocalState
import all MLS.Symbolic.Code.Symbolic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Actions.PersistentGlobalState
import all DY.Actions.PersistentLocalState

/-!
Lemmas to prove that attacker programs preserve reachability (not in MLS*), complementing DyLean's
`Traceful.PreservesReachabilityFrom_bind` / `_pure` and `Traceful.PreservesReachability_base`:
the actions that do not change the trace (`Traceful.ReadOnly`, e.g. reading a state), `failure`, `<|>`,
`List.foldlM` and `extractResult`.
-/

namespace DY

variable [ExecTraceTypes]

/-! ## Read-only actions -/

/-- `f` does not change the trace (e.g. it only reads states). -/
public
def Traceful.ReadOnly {α: Type} (f: Traceful α): Prop :=
  ∀ tr, (f.run tr).snd.val = tr

public
theorem Traceful.ReadOnly_pure {α: Type} (x: α): (pure x: Traceful α).ReadOnly := by
  intro tr
  rfl

public
theorem Traceful.ReadOnly_failure {α: Type}: (failure: Traceful α).ReadOnly := by
  intro tr
  rfl

public
theorem Traceful.ReadOnly_bind {α β: Type} (x: Traceful α) (f: α → Traceful β)
  (hx: x.ReadOnly) (hf: ∀ a, (f a).ReadOnly):
  (x >>= f).ReadOnly
:= by
  intro tr
  rw [Traceful.run_bind]
  have := hx tr
  generalize x.run tr = r at this ⊢
  obtain ⟨_ | a, tr', _⟩ := r
  · simp_all
  · have := hf a tr'
    simp_all

public
theorem Traceful.ReadOnly_guard (p: Prop) [Decidable p]: (guard p: Traceful Unit).ReadOnly := by
  unfold guard
  split
  · exact Traceful.ReadOnly_pure _
  · exact Traceful.ReadOnly_failure

public
theorem PersistentLocalState.getLocalState.readOnly {StateT: Type}
  [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)]
  (participant: Participant) (handle: Nat):
  (PersistentLocalState.getLocalState participant handle: Traceful StateT).ReadOnly
:= by
  unfold PersistentLocalState.getLocalState PersistentGlobalState.getGlobalState
  refine Traceful.ReadOnly_bind _ _ (Traceful.ReadOnly_bind _ _ (fun tr => rfl) fun _ => Traceful.ReadOnly_pure _) ?_
  intro
  exact Traceful.ReadOnly_bind _ _ (Traceful.ReadOnly_guard _) fun _ => Traceful.ReadOnly_pure _

public
theorem Traceful.ReadOnly_mapM {α β: Type} (f: α → Traceful β) (hf: ∀ a, (f a).ReadOnly) (l: List α):
  (l.mapM f).ReadOnly
:= by
  induction l with
  | nil => exact Traceful.ReadOnly_pure _
  | cons a l ih =>
    rw [List.mapM_cons]
    exact Traceful.ReadOnly_bind _ _ (hf a) fun _ => Traceful.ReadOnly_bind _ _ ih fun _ => Traceful.ReadOnly_pure _

public
theorem Traceful.ReadOnly_forIn {α β: Type} (l: List α) (init: β) (f: α → β → Traceful (ForInStep β))
  (hf: ∀ a b, (f a b).ReadOnly):
  (forIn l init f).ReadOnly
:= by
  induction l generalizing init with
  | nil => exact Traceful.ReadOnly_pure _
  | cons a l ih =>
    rw [List.forIn_cons]
    refine Traceful.ReadOnly_bind _ _ (hf a init) fun step => ?_
    cases step
    · exact Traceful.ReadOnly_pure _
    · exact ih _

/-- A read-only action preserves reachability. -/
public
theorem Traceful.ReadOnly.preservesReachability {α: Type} (config: ReachabilityConfig) {f: Traceful α}
  (h: f.ReadOnly):
  f.PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  have := h tr
  simp only [Traceful.PreservesReachabilityFrom]
  generalize f.run tr = r at this ⊢
  obtain ⟨_ | _, tr', _⟩ := r <;> simp_all

/-! ## Failures and alternatives -/

public
theorem Traceful.PreservesReachabilityFrom_failure {α: Type} (config: ReachabilityConfig)
  (post: α → ExecTrace → Prop) (tr: ExecTrace):
  tr.Reachable config →
  (failure: Traceful α).PreservesReachabilityFrom config post tr
:= by
  simp [Traceful.PreservesReachabilityFrom, Traceful.run_failure]

public
theorem Traceful.PreservesReachability_orElse {α: Type} (config: ReachabilityConfig) (x: Traceful α) (y: Unit → Traceful α)
  (hx: x.PreservesReachability config (fun _ => True) (fun _ _ => True))
  (hy: (y ()).PreservesReachability config (fun _ => True) (fun _ _ => True)):
  (HOrElse.hOrElse x y).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  intro tr h_tr _
  have hx := hx tr h_tr trivial
  simp only [Traceful.PreservesReachabilityFrom] at hx ⊢
  simp only [HOrElse.hOrElse, OrElse.orElse, Alternative.orElse, Traceful.run] at hx ⊢
  generalize x tr = r at hx ⊢
  obtain ⟨_ | _, tr', _⟩ := r
  · have := hy tr' hx.1 trivial
    simp only [Traceful.PreservesReachabilityFrom, Traceful.run] at this
    generalize y () tr' = r at this ⊢
    obtain ⟨_ | _, _, _⟩ := r <;> simp_all
  · simp_all

/-! ## Loops -/

public
theorem List.foldlM.preservesReachability {α β: Type} (config: ReachabilityConfig) (f: β → α → Traceful β)
  (hf: ∀ b a, (f b a).PreservesReachability config (fun _ => True) (fun _ _ => True)) (l: List α) (init: β):
  (l.foldlM f init).PreservesReachability config (fun _ => True) (fun _ _ => True)
:= by
  induction l generalizing init with
  | nil => exact fun tr h_tr _ => Traceful.PreservesReachabilityFrom_pure _ _ _ _ h_tr trivial
  | cons a l ih =>
    intro tr h_tr _
    exact Traceful.PreservesReachabilityFrom_bind _ _ _ _ _ _ _ (hf init a) h_tr trivial
      fun b tr' _ h_tr' _ => ih b tr' h_tr' trivial

end DY

namespace MLS

open DY

variable [ExecTraceTypes]

public
theorem extractResult.preservesReachability {α: Type} (config: ReachabilityConfig) (x: Result α):
  (extractResult x).PreservesReachability config (fun _ => True) (fun y _ => x = .success y)
:= by
  intro tr h_tr _
  unfold extractResult
  split
  · exact Traceful.PreservesReachabilityFrom_pure _ _ _ _ h_tr rfl
  · exact Traceful.PreservesReachabilityFrom_failure _ _ _ h_tr

end MLS
