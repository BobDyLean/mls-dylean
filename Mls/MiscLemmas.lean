import Comparse

/-!
Port of `MLS.MiscLemmas` (the parts needed so far).
-/

namespace Mls

open Comparse

variable {Bytes: Type} [BytesLike Bytes]

theorem length_concatPrefixes (prefixes: List Bytes) (suffix: Bytes):
  BytesLike.length (concatPrefixes prefixes suffix) = (prefixes.map BytesLike.length).sum + BytesLike.length suffix
:= by
  induction prefixes with
  | nil => simp [concatPrefixes]
  | cons h t ih =>
    simp only [concatPrefixes, List.foldr_cons, BytesLike.concat_length] at *
    simp only [List.map_cons, List.sum_cons]
    omega

theorem length_list_serialize_cons {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (h: a) (t: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (h :: t)) =
    BytesLike.length (concatPrefixes (mf.serialize h) BytesLike.empty) + BytesLike.length ((ExtensibleMessageFormat.list mf).serialize t)
:= by
  simp only [ExtensibleMessageFormat.list, ExtensibleMessageFormat.list.serialize, length_concatPrefixes, BytesLike.empty_length]
  omega

/-- Port of `bytes_length_filter`: filtering a list does not increase the length of its serialization. -/
theorem bytes_length_filter {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (pred: a → Bool) (l: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (l.filter pred)) ≤
    BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l)
:= by
  induction l with
  | nil => simp
  | cons h t ih =>
    rw [length_list_serialize_cons]
    by_cases hp: pred h
    · rw [List.filter_cons_of_pos hp, length_list_serialize_cons]
      omega
    · rw [List.filter_cons_of_neg hp]
      omega

end Mls
