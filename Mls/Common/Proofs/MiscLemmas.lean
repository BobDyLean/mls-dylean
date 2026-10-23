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
  induction prefixes <;> grind [concatPrefixes, BytesLike.concat_length]

theorem length_list_serialize_cons {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (h: a) (t: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (h :: t)) =
    BytesLike.length (concatPrefixes (mf.serialize h) BytesLike.empty) + BytesLike.length ((ExtensibleMessageFormat.list mf).serialize t)
:= by
  simp only [ExtensibleMessageFormat.list, ExtensibleMessageFormat.list.serialize, length_concatPrefixes, BytesLike.empty_length]
  grind

/-- Port of `bytes_length_filter`: filtering a list does not increase the length of its serialization. -/
theorem bytes_length_filter {a: Type} (mf: NonExtensibleMessageFormat Bytes a) [mf.ParseConsumes] (pred: a → Bool) (l: List a):
  BytesLike.length ((ExtensibleMessageFormat.list mf).serialize (l.filter pred)) ≤
    BytesLike.length ((ExtensibleMessageFormat.list mf).serialize l)
:= by
  induction l <;> grind [length_list_serialize_cons]

end Mls
