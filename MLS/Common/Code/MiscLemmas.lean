module

public import Comparse
import MLS.Comparse.Derived
import all Comparse.Basic

/-!
Port of `MLS.MiscLemmas` (the parts needed so far: `bytes_length_filter`, used in the code by `MLS.TreeSync.Operations`).
-/

namespace MLS

open Comparse

variable {Bytes: Type} [BytesLike Bytes]

/-- `concat` is injective on bytes whose first parts have the same length. -/
public
theorem concat_inj (a1 b1 a2 b2: Bytes) (h: BytesLike.concat a1 b1 = BytesLike.concat a2 b2)
  (hlen: BytesLike.length a1 = BytesLike.length a2):
  a1 = a2 ∧ b1 = b2
:= by
  have s1 := BytesLike.split_concat a1 b1
  rw [h, hlen, BytesLike.split_concat] at s1
  grind

theorem length_concatPrefixes (prefixes: List Bytes) (suffix: Bytes):
  BytesLike.length (concatPrefixes prefixes suffix) = (prefixes.map BytesLike.length).sum + BytesLike.length suffix
:= by
  induction prefixes <;> grind [concatPrefixes, BytesLike.concat_length]

theorem length_list_serialize_cons {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (h: a) (t: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (h :: t)) =
    BytesLike.length (concatPrefixes (mf.serialize h) BytesLike.empty) + BytesLike.length ((ExtensibleMessageFormat.list mf).serialize t)
:= by
  simp only [ExtensibleMessageFormat.list.serialize_cons, length_concatPrefixes, BytesLike.empty_length]
  grind

/-- Port of `bytes_length_filter`: filtering a list does not increase the length of its serialization. -/
public
theorem bytes_length_filter {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (pred: a → Bool) (l: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (l.filter pred)) ≤
    BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l)
:= by
  induction l <;> grind [length_list_serialize_cons]

end MLS
