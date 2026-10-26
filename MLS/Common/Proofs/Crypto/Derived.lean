module

public import MLS.Common.Code.Crypto.Derived
public import MLS.Common.Proofs.Result

/-!
Lemmas about the functions of `MLS.Crypto.Derived`.
They characterize the successful computations of the functions returning a `Result`,
to reason on hypotheses `f x = .success y`.
Also the injectivity of `serializeNE`, used by the reductions to hash collisions.
-/

namespace MLS

open Comparse

@[simp]
public
theorem mkUInt32_eq_success (n: Nat) (funName varName: String) (x: UInt32):
  mkUInt32 n funName varName = .success x ↔ n < 2^32 ∧ n.toUInt32 = x
:= by
  unfold mkUInt32 Result.error
  split <;> simp <;> grind

@[simp]
public
theorem mkUInt16_eq_success (n: Nat) (funName varName: String) (x: UInt16):
  mkUInt16 n funName varName = .success x ↔ n < 2^16 ∧ n.toUInt16 = x
:= by
  unfold mkUInt16 Result.error
  split <;> simp <;> grind

@[simp]
public
theorem mkMlsBytes_eq_success {Bytes: Type} [BytesLike Bytes] (b: Bytes) (funName varName: String) (x: MlsBytes Bytes):
  mkMlsBytes b funName varName = .success x ↔ b = x.val
:= by
  unfold mkMlsBytes Result.error
  split <;> simp [pure, Subtype.ext_iff] <;> grind

@[simp]
public
theorem mkMlsList_eq_success {Bytes: Type} [BytesLike Bytes] {α: Type} {mf: NonExtensibleMessageFormat Bytes α} [mf.ParseConsumes]
  (l: List α) (funName varName: String) (x: MlsList mf):
  mkMlsList l funName varName = .success x ↔ l = x.val
:= by
  unfold mkMlsList Result.error
  split <;> simp [pure, Subtype.ext_iff] <;> grind

@[simp]
public
theorem mkMlsAsciiString_eq_success {Bytes: Type} [BytesLike Bytes] (s: String) (funName varName: String) (x: MlsAsciiString (Bytes := Bytes)):
  mkMlsAsciiString s funName varName = .success x ↔ s = x.val.val
:= by
  unfold mkMlsAsciiString Result.error
  split
  · simp only
    split <;> simp [pure, Subtype.ext_iff] <;> grind
  · simp
    grind

@[simp]
public
theorem getMlsLabel_eq_success {Bytes: Type} [BytesLike Bytes] (label: String) (x: MlsAsciiString (Bytes := Bytes)):
  getMlsLabel label = .success x ↔ "MLS 1.0 " ++ label = x.val.val
:= by
  simp [getMlsLabel]

public
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

/-- `serialize_wf_lemma` (and its converse) for `serializeNE`. -/
public
theorem pred_serializeNE_iff {Bytes: Type} [BytesLike Bytes] {α: Type} (mf: NonExtensibleMessageFormat Bytes α)
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (x: α)
  : pred (serializeNE mf x) ↔ mf.wf pred x
:= by
  rw [serializeNE, ← ExtensibleMessageFormat.wf_eq mf.toExtensible pred x, NonExtensibleMessageFormat.toExtensible.wf_eq]

/-- `parse_wf_lemma` for `mf.toExtensible.parse`. -/
public
theorem wf_of_parse {Bytes: Type} [BytesLike Bytes] {α: Type} (mf: NonExtensibleMessageFormat Bytes α) [mf.HasUniqueRepresentation]
  (pred: Bytes → Prop) [BytesCompatiblePred pred] (buf: Bytes) (x: α)
  : mf.toExtensible.parse buf = some x →
    pred buf →
    mf.wf pred x
:= by
  intro h_parse h_buf
  have := ExtensibleMessageFormat.HasUniqueRepresentation.serialize_parse_inv mf.toExtensible buf
  rw [h_parse] at this
  subst this
  exact (pred_serializeNE_iff mf pred x).1 h_buf

end MLS
