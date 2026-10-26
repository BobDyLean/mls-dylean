module

public import MLS.Common.Code.Result

/-!
Lemmas about `MLS.Result`.
They characterize successful computations, to reason on hypotheses `f x = .success y`.
-/

namespace MLS

namespace Result

@[simp]
public
theorem bind_eq_success {α β: Type} (x: Result α) (f: α → Result β) (y: β):
  (x >>= f) = .success y ↔ ∃ a, x = .success a ∧ f a = .success y
:= by
  cases x <;> simp [Bind.bind, Result.bind]

@[simp]
public
theorem map_eq_success {α β: Type} (x: Result α) (f: α → β) (y: β):
  (f <$> x) = .success y ↔ ∃ a, x = .success a ∧ f a = y
:= by
  cases x <;> simp [Functor.map, Result.bind]

@[simp]
public
theorem pure_eq_success {α: Type} (a b: α): (pure a: Result α) = .success b ↔ a = b := by
  simp [pure]

@[simp]
public
theorem fromOption_eq_success {α: Type} (s: String) (x: Option α) (y: α): fromOption s x = .success y ↔ x = some y := by
  cases x <;> simp [fromOption, error, pure]

end Result

end MLS
