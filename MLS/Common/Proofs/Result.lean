import MLS.Common.Code.Result

/-!
Lemmas about `MLS.Result`.
They characterize successful computations, to reason on hypotheses `f x = .success y`.
-/

namespace MLS

namespace Result

@[simp] theorem bind_eq_success {α β: Type} (x: Result α) (f: α → Result β) (y: β):
  (x >>= f) = .success y ↔ ∃ a, x = .success a ∧ f a = .success y
:= by
  cases x <;> simp [Bind.bind, Result.bind]

@[simp] theorem map_eq_success {α β: Type} (x: Result α) (f: α → β) (y: β):
  (f <$> x) = .success y ↔ ∃ a, x = .success a ∧ f a = y
:= by
  cases x <;> simp [Functor.map, Result.bind]

@[simp] theorem pure_eq_success {α: Type} (a b: α): (pure a: Result α) = .success b ↔ a = b := by
  simp [pure]

end Result

end MLS
