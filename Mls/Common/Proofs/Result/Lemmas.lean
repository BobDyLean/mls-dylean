import Mls.Common.Code.Crypto.Derived

/-!
Lemmas about `Mls.Result`, and about the functions of `Mls.Crypto.Derived` returning a `Result`.
They characterize successful computations, to reason on hypotheses `f x = .success y`.
-/

namespace Mls

open Comparse

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

@[simp] theorem mkUInt32_eq_success (n: Nat) (funName varName: String) (x: UInt32):
  mkUInt32 n funName varName = .success x ↔ n < 2^32 ∧ n.toUInt32 = x
:= by
  unfold mkUInt32 Result.error
  split <;> simp <;> grind

@[simp] theorem mkMlsList_eq_success {Bytes: Type} [BytesLike Bytes] {α: Type} {mf: NonExtensibleMessageFormat Bytes α} [mf.ParseConsumes]
  (l: List α) (funName varName: String) (x: MlsList mf):
  mkMlsList l funName varName = .success x ↔ l = x.val
:= by
  unfold mkMlsList Result.error
  split <;> simp [pure, Subtype.ext_iff] <;> grind

end Mls
