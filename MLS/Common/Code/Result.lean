/-!
Port of `MLS.Result`.

Port-specific differences:
- `let?` is replaced by the `Monad` instance (`←` in `do` notation).
- `mapM` and `fold_leftM` are provided by the generic `List.mapM` and `List.foldlM`.
-/

namespace MLS

inductive Result (α: Type) where
  | success: α → Result α
  | internalError: String → Result α
  | protocolError: String → Result α
deriving Repr, BEq

namespace Result

/-- Port of `internal_failure`. -/
def internalFailure {α: Type} (s: String): Result α :=
  .internalError s

/-- Port of `error`. -/
def error {α: Type} (s: String): Result α :=
  .protocolError s

/-- Port of `(let?)`. -/
def bind {α β: Type} (rx: Result α) (f: α → Result β): Result β :=
  match rx with
  | .success x => f x
  | .internalError x => .internalError x
  | .protocolError x => .protocolError x

instance: Monad Result where
  pure := .success
  bind := Result.bind

instance: LawfulMonad Result := LawfulMonad.mk'
  (id_map := by intro _ x; cases x <;> rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intro _ _ _ x _ _; cases x <;> rfl)

/-- Port of `from_option`. -/
def fromOption {α: Type} (s: String) (x: Option α): Result α :=
  match x with
  | none => error s
  | some x => pure x

end Result

end MLS
