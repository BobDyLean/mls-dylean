module

public import Comparse
import MLS.Comparse.Derived
import all Comparse.Basic

/-!
Port of `MLS.MiscLemmas` (the parts needed so far: `bytes_length_filter`, used in the code by `MLS.TreeSync.Operations`),
and `ListChain` (F*'s `List.Tot.Properties.sorted`, used in the code by `MLS.TreeSync.Invariants.UnmergedLeaves`).
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
  grind [BytesLike.split_concat]

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

/--
Each element of the list is related to the next one by `R`.
Port of F*'s `List.Tot.Properties.sorted`; MLS* also defines it for specific relations
(e.g. `tree_list_is_parent_hash_linkedP`).
-/
@[expose]
public
def ListChain {α: Type} (R: α → α → Prop): List α → Prop
  | [] | [_] => True
  | a :: b :: l => R a b ∧ ListChain R (b :: l)

public
instance ListChain.instDecidable {α: Type} {R: α → α → Prop} [DecidableRel R]: (l: List α) → Decidable (ListChain R l)
  | [] | [_] => isTrue trivial
  | a :: b :: l =>
    have := ListChain.instDecidable (R := R) (b :: l)
    inferInstanceAs (Decidable (R a b ∧ ListChain R (b :: l)))

/-- For a transitive relation, relating adjacent elements is the same as relating all pairs of elements. -/
public
theorem listChain_iff_pairwise {α: Type} {R: α → α → Prop} (htrans: ∀ a b c, R a b → R b c → R a c) (l: List α):
  ListChain R l ↔ l.Pairwise R
:= by
  induction l with
  | nil => simp [ListChain]
  | cons a l ih =>
    cases l with
    | nil => simp [ListChain]
    | cons b l => grind [ListChain, List.pairwise_cons]

end MLS
