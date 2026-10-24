import MLS.Common.Code.Crypto.Derived
import MLS.Common.Proofs.Result

/-!
Lemmas about the functions of `MLS.Crypto.Derived`.
They characterize the successful computations of the functions returning a `Result`,
to reason on hypotheses `f x = .success y`.
Also the injectivity of `serializeNE`, used by the reductions to hash collisions.
-/

namespace MLS

open Comparse

@[simp] theorem mkUInt32_eq_success (n: Nat) (funName varName: String) (x: UInt32):
  mkUInt32 n funName varName = .success x ↔ n < 2^32 ∧ n.toUInt32 = x
:= by
  unfold mkUInt32 Result.error
  split <;> simp <;> grind

@[simp] theorem mkMlsBytes_eq_success {Bytes: Type} [BytesLike Bytes] (b: Bytes) (funName varName: String) (x: MlsBytes Bytes):
  mkMlsBytes b funName varName = .success x ↔ b = x.val
:= by
  unfold mkMlsBytes Result.error
  split <;> simp [pure, Subtype.ext_iff] <;> grind

@[simp] theorem mkMlsList_eq_success {Bytes: Type} [BytesLike Bytes] {α: Type} {mf: NonExtensibleMessageFormat Bytes α} [mf.ParseConsumes]
  (l: List α) (funName varName: String) (x: MlsList mf):
  mkMlsList l funName varName = .success x ↔ l = x.val
:= by
  unfold mkMlsList Result.error
  split <;> simp [pure, Subtype.ext_iff] <;> grind

theorem serializeNE_injective {Bytes: Type} [BytesLike Bytes] {α: Type} (mf: NonExtensibleMessageFormat Bytes α) [mf.IsNonAmbiguous]:
  Function.Injective (serializeNE mf)
:= by
  intro x y h
  have hx := ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv mf.toExtensible x
  have hy := ExtensibleMessageFormat.IsNonAmbiguous.parse_serialize_inv mf.toExtensible y
  simp_all [serializeNE]

/-
Pattern for `grind`'s injectivity reasoning (as `@[grind inj]`, which cannot be used here:
it would choose the instance hypothesis `mf.IsNonAmbiguous` as the pattern, which never appears in goals).
-/
grind_pattern serializeNE_injective => serializeNE mf

end MLS
