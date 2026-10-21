import Comparse

/-!
`BytesLike` instance for `ByteArray`,
counterpart of `seq_u8_bytes_like` in Comparse (F*).
-/

open Comparse

namespace ByteArray

def splitAt (b : ByteArray) (i : Nat) : Option (ByteArray × ByteArray) :=
  if i ≤ b.size then some (b.extract 0 i, b.extract i b.size) else none

theorem splitAt_some {b : ByteArray} {i : Nat} {b1 b2 : ByteArray} (h : b.splitAt i = some (b1, b2)) :
    i ≤ b.size ∧ b1 = b.extract 0 i ∧ b2 = b.extract i b.size := by
  unfold splitAt at h
  split at h
  · cases h; exact ⟨by assumption, rfl, rfl⟩
  · cases h

theorem size_eq (b : ByteArray) : b.size = b.data.size := rfl

end ByteArray

instance : BytesLike ByteArray where
  length := ByteArray.size
  empty := .empty
  empty_length := ByteArray.size_empty
  recognizeEmpty b := b.size == 0
  recognizeEmpty_correct b := by
    simp only [beq_iff_eq]
    constructor
    · intro h; apply ByteArray.ext; rw [ByteArray.data_empty]; exact Array.size_eq_zero_iff.mp h
    · intro h; subst h; rfl
  concat := (· ++ ·)
  concat_length _ _ := ByteArray.size_append
  split := ByteArray.splitAt
  split_length b i := by
    split
    · trivial
    · rename_i b1 b2 h
      obtain ⟨hi, rfl, rfl⟩ := ByteArray.splitAt_some h
      rw [ByteArray.size_extract, ByteArray.size_extract]
      omega
  split_concat b1 b2 := by
    have h1 : b1.size ≤ (b1 ++ b2).size := by rw [ByteArray.size_append]; omega
    show (if b1.size ≤ (b1 ++ b2).size then _ else _) = _
    rw [ite_eq_left h1]
    have e1 : (b1 ++ b2).extract 0 b1.size = b1 := by
      apply ByteArray.ext
      rw [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
      rw [ByteArray.size_eq, Nat.sub_self, Array.extract_zero, Array.append_empty]
      exact Array.extract_size
    have e2 : (b1 ++ b2).extract b1.size (b1 ++ b2).size = b2 := by
      apply ByteArray.ext
      rw [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
      rw [ByteArray.size_append, ByteArray.size_eq, ByteArray.size_eq, Nat.sub_self, Nat.add_sub_cancel_left]
      rw [Array.extract_size]
      rw [Array.extract_empty_of_size_le_start (Nat.le_refl _), Array.empty_append]
    rw [e1, e2]
  concat_split b i := by
    split
    · trivial
    · rename_i b1 b2 h
      obtain ⟨hi, rfl, rfl⟩ := ByteArray.splitAt_some h
      apply ByteArray.ext
      rw [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_extract, Array.extract_append_extract]
      rw [Nat.zero_min, Nat.max_eq_right hi, ByteArray.size_eq]
      exact Array.extract_size
  toByteArray := some
  fromByteArray := id
  fromByteArray_length _ := rfl
  to_from_ByteArray _ := rfl
  from_to_ByteArray _ := rfl
